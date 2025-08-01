use std::collections::{HashMap, VecDeque};
use std::{cell::RefCell, rc::Rc};

use super::super::*;
use super::metadata::SharedMetadataState;
use crate::utils::aligned_buffer::AlignedBuf;
use crate::{vhost_backend::SECTOR_SIZE, Result, VhostUserBlockError};
use log::{debug, error};

const MAX_CONCURRENT_FETCHES: usize = 16;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FetchState {
    Queued,
    Fetching,
    Flushing,
}

#[derive(Clone)]
struct FetchBuffer {
    used_for: Option<usize>,
    buf: SharedBuffer,
}

pub struct StripeFetcher {
    fetch_source_channel: Box<dyn IoChannel>,
    fetch_target_channel: Box<dyn IoChannel>,
    source_sector_count: u64,
    target_sector_count: u64,
    stripe_sector_count: u64,
    fetch_queue: VecDeque<usize>,
    fetch_buffers: Vec<FetchBuffer>,
    shared_state: SharedMetadataState,
    stripe_states: HashMap<usize, FetchState>,
}

impl StripeFetcher {
    pub fn new(
        source_dev: &dyn BlockDevice,
        target_dev: &dyn BlockDevice,
        stripe_sector_count: u64,
        shared_state: SharedMetadataState,
        alignment: usize,
    ) -> Result<Self> {
        let fetch_source_channel = source_dev.create_channel()?;
        let fetch_target_channel = target_dev.create_channel()?;

        let stripe_size_u64 = stripe_sector_count
            .checked_mul(SECTOR_SIZE as u64)
            .ok_or_else(|| VhostUserBlockError::InvalidParameter {
                description: "stripe size too large".to_string(),
            })?;
        let stripe_size = stripe_size_u64 as usize;

        let fetch_buffers = (0..MAX_CONCURRENT_FETCHES)
            .map(|_| FetchBuffer {
                used_for: None,
                buf: Rc::new(RefCell::new(AlignedBuf::new_with_alignment(
                    stripe_size,
                    alignment,
                ))),
            })
            .collect();
        let source_sector_count = source_dev.sector_count();
        let target_sector_count = target_dev.sector_count();
        if target_sector_count < source_sector_count {
            return Err(VhostUserBlockError::InvalidParameter {
                description: "target device too small".into(),
            });
        }
        let _stripe_count = source_sector_count.div_ceil(stripe_sector_count);
        Ok(StripeFetcher {
            fetch_source_channel,
            fetch_target_channel,
            source_sector_count,
            target_sector_count,
            stripe_sector_count,
            fetch_queue: VecDeque::new(),
            fetch_buffers,
            shared_state,
            stripe_states: HashMap::new(),
        })
    }

    pub fn busy(&self) -> bool {
        !self.fetch_queue.is_empty()
            || self.fetch_source_channel.busy()
            || self.fetch_target_channel.busy()
    }

    pub fn handle_fetch_request(&mut self, stripe_id: usize) {
        if self.shared_state.stripe_fetched(stripe_id) {
            debug!("Stripe {stripe_id} already fetched");
            return;
        }
        if self.stripe_states.contains_key(&stripe_id) {
            debug!("Stripe {stripe_id} is already queued or fetching");
            return;
        }
        debug!("Enqueueing stripe {stripe_id} for fetch");
        self.fetch_queue.push_back(stripe_id);
        self.stripe_states.insert(stripe_id, FetchState::Queued);
    }

    fn fetch_completed(&mut self, buffer_idx: usize, success: bool) -> (usize, bool) {
        let fetch_buffer = &mut self.fetch_buffers[buffer_idx];
        let stripe_id = match fetch_buffer.used_for.take() {
            Some(id) => id,
            None => {
                error!("fetch_completed called with unused buffer {buffer_idx}");
                return (0, false);
            }
        };

        debug!("Fetch completed for stripe {stripe_id}, success={success}");

        self.stripe_states.remove(&stripe_id);
        if success {
            self.shared_state.set_stripe_fetched(stripe_id);
        }
        (stripe_id, success)
    }

    fn start_write(&mut self, buffer_idx: usize) -> bool {
        let fetch_buffer = &mut self.fetch_buffers[buffer_idx];
        let stripe_id = match fetch_buffer.used_for {
            Some(id) => id,
            None => {
                error!("start_write called with unused buffer {buffer_idx}");
                return false;
            }
        };
        let buf = fetch_buffer.buf.clone();
        let stripe_sector_offset = stripe_id as u64 * self.stripe_sector_count;
        let stripe_sector_count = self
            .stripe_sector_count
            .min(self.target_sector_count - stripe_sector_offset);

        self.fetch_target_channel.add_write(
            stripe_sector_offset,
            stripe_sector_count as u32,
            buf,
            buffer_idx,
        );

        if let Err(e) = self.fetch_target_channel.submit() {
            error!("Failed to submit write for stripe {stripe_id}: {e:?}");
            false
        } else {
            true
        }
    }

    fn start_flush(&mut self, buffer_idx: usize, stripe_id: usize) -> bool {
        self.stripe_states.insert(stripe_id, FetchState::Flushing);
        self.fetch_target_channel.add_flush(buffer_idx);

        if let Err(e) = self.fetch_target_channel.submit() {
            error!("Failed to submit flush for stripe {stripe_id}: {e:?}");
            false
        } else {
            true
        }
    }

    fn poll_fetches(&mut self) -> Vec<(usize, bool)> {
        let mut result = Vec::new();
        for (buffer_idx, success) in self.fetch_source_channel.poll() {
            if !success || !self.start_write(buffer_idx) {
                result.push(self.fetch_completed(buffer_idx, false));
            } else if let Some(stripe_id) = self.fetch_buffers[buffer_idx].used_for {
                self.stripe_states.insert(stripe_id, FetchState::Fetching);
            }
        }

        for (buffer_idx, success) in self.fetch_target_channel.poll() {
            if !success {
                result.push(self.fetch_completed(buffer_idx, false));
                continue;
            }
            let stripe_id = match self.fetch_buffers[buffer_idx].used_for {
                Some(id) => id,
                None => {
                    error!("poll_fetches called with unused buffer {buffer_idx}");
                    continue;
                }
            };
            match self.stripe_states.get(&stripe_id) {
                Some(FetchState::Fetching) => {
                    debug!("Stripe {stripe_id} write completed, flushing...");
                    if !self.start_flush(buffer_idx, stripe_id) {
                        result.push(self.fetch_completed(buffer_idx, false));
                        continue;
                    }
                }
                Some(FetchState::Flushing) => {
                    result.push(self.fetch_completed(buffer_idx, success));
                }
                _ => {
                    error!("Unexpected state for stripe {stripe_id} after write");
                }
            }
        }

        result
    }

    fn start_fetches(&mut self) -> Vec<(usize, bool)> {
        let mut result = Vec::new();

        while let Some(stripe_id) = self.fetch_queue.pop_front() {
            let maybe_buffer_idx = self
                .fetch_buffers
                .iter()
                .position(|buf| buf.used_for.is_none());
            let buffer_idx = match maybe_buffer_idx {
                Some(idx) => idx,
                None => {
                    self.fetch_queue.push_front(stripe_id);
                    break;
                }
            };
            let fetch_buffer = &mut self.fetch_buffers[buffer_idx];
            fetch_buffer.used_for = Some(stripe_id);

            let buf = fetch_buffer.buf.clone();
            let stripe_sector_offset = stripe_id as u64 * self.stripe_sector_count;
            let stripe_sector_count = self
                .stripe_sector_count
                .min(self.source_sector_count - stripe_sector_offset);

            self.fetch_source_channel.add_read(
                stripe_sector_offset,
                stripe_sector_count as u32,
                buf.clone(),
                buffer_idx,
            );

            if let Err(e) = self.fetch_source_channel.submit() {
                error!("Failed to submit read for stripe {stripe_id}: {e:?}");
                result.push(self.fetch_completed(buffer_idx, false));
                continue;
            }

            self.stripe_states.insert(stripe_id, FetchState::Fetching);
        }

        result
    }

    pub fn update(&mut self) -> Vec<(usize, bool)> {
        let mut completed_fetches = self.start_fetches();
        completed_fetches.append(&mut self.poll_fetches());
        completed_fetches
    }
}

unsafe impl Send for StripeFetcher {}
unsafe impl Sync for StripeFetcher {}
