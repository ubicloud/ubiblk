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

pub struct StripeFetcher {
    fetch_source_channel: Box<dyn IoChannel>,
    fetch_target_channel: Box<dyn IoChannel>,
    source_sector_count: u64,
    target_sector_count: u64,
    stripe_sector_count: u64,
    fetch_queue: VecDeque<usize>,
    fetch_buffers: Vec<SharedBuffer>,
    shared_state: SharedMetadataState,
    stripe_states: HashMap<usize, FetchState>,
    allocated_buffers: HashMap<usize, usize>,
    available_buffers: VecDeque<usize>,
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
            .map(|_| {
                Rc::new(RefCell::new(AlignedBuf::new_with_alignment(
                    stripe_size,
                    alignment,
                )))
            })
            .collect();
        let source_sector_count = source_dev.sector_count();
        let target_sector_count = target_dev.sector_count();
        if target_sector_count < source_sector_count {
            return Err(VhostUserBlockError::InvalidParameter {
                description: "target device too small".into(),
            });
        }
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
            allocated_buffers: HashMap::new(),
            available_buffers: (0..MAX_CONCURRENT_FETCHES).collect(),
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

    pub fn update(&mut self) {
        self.start_fetches();
        self.poll_fetches();
    }

    fn start_fetches(&mut self) {
        while !self.fetch_queue.is_empty() && !self.available_buffers.is_empty() {
            let stripe_id = self.fetch_queue.pop_front().unwrap();
            let buffer_idx = self.available_buffers.pop_front().unwrap();
            let fetch_buffer = &mut self.fetch_buffers[buffer_idx];
            self.allocated_buffers.insert(stripe_id, buffer_idx);

            let buf = fetch_buffer.clone();
            let stripe_sector_offset = stripe_id as u64 * self.stripe_sector_count;
            let stripe_sector_count = self
                .stripe_sector_count
                .min(self.source_sector_count - stripe_sector_offset);

            self.fetch_source_channel.add_read(
                stripe_sector_offset,
                stripe_sector_count as u32,
                buf.clone(),
                stripe_id,
            );

            if let Err(e) = self.fetch_source_channel.submit() {
                error!("Failed to submit read for stripe {stripe_id}: {e:?}");
                self.fetch_completed(stripe_id, false);
                continue;
            }

            self.stripe_states.insert(stripe_id, FetchState::Fetching);
        }
    }

    fn poll_fetches(&mut self) {
        // Overall fetching logic (assuming things go well):
        // 1. Read from the source channel.
        // 2. Write to the target channel.
        // 3. Flush the target channel.
        // 4. Mark the stripe as fetched in the shared state.

        // Handle completions from the source channel. Did any fetches from the
        // source complete? Start writing the successful ones to the target.
        for (stripe_id, success) in self.fetch_source_channel.poll() {
            let buffer_idx = match self.allocated_buffers.get(&stripe_id) {
                Some(idx) => *idx,
                None => {
                    error!("Received completion for unknown stripe {stripe_id}");
                    continue;
                }
            };

            if !success || !self.start_write(buffer_idx, stripe_id) {
                self.fetch_completed(stripe_id, false);
            }
        }

        // Handle completions from the target channel. We'll start flushing the
        // ones that were successfully written to the target.
        for (stripe_id, success) in self.fetch_target_channel.poll() {
            if !success {
                self.fetch_completed(stripe_id, false);
                continue;
            }

            match self.stripe_states.get(&stripe_id) {
                Some(FetchState::Fetching) => {
                    debug!("Stripe {stripe_id} write completed, flushing...");
                    if self.start_flush(stripe_id) {
                        self.stripe_states.insert(stripe_id, FetchState::Flushing);
                    } else {
                        self.fetch_completed(stripe_id, false);
                        continue;
                    }
                }
                Some(FetchState::Flushing) => {
                    self.fetch_completed(stripe_id, success);
                }
                _ => {
                    error!("Unexpected state for stripe {stripe_id} after write");
                }
            }
        }
    }

    fn start_write(&mut self, buffer_idx: usize, stripe_id: usize) -> bool {
        let fetch_buffer = &mut self.fetch_buffers[buffer_idx];
        let buf = fetch_buffer.clone();

        let stripe_sector_offset = stripe_id as u64 * self.stripe_sector_count;
        let stripe_sector_count = self
            .stripe_sector_count
            .min(self.target_sector_count - stripe_sector_offset);

        self.fetch_target_channel.add_write(
            stripe_sector_offset,
            stripe_sector_count as u32,
            buf,
            stripe_id,
        );

        if let Err(e) = self.fetch_target_channel.submit() {
            error!("Failed to submit write for stripe {stripe_id}: {e:?}");
            false
        } else {
            true
        }
    }

    fn start_flush(&mut self, stripe_id: usize) -> bool {
        self.fetch_target_channel.add_flush(stripe_id);

        if let Err(e) = self.fetch_target_channel.submit() {
            error!("Failed to submit flush for stripe {stripe_id}: {e:?}");
            false
        } else {
            true
        }
    }

    fn fetch_completed(&mut self, stripe_id: usize, success: bool) {
        debug!("Fetch completed for stripe {stripe_id}, success={success}");

        self.stripe_states.remove(&stripe_id);
        if success {
            self.shared_state.set_stripe_fetched(stripe_id);
        }

        if let Some(buffer_idx) = self.allocated_buffers.remove(&stripe_id) {
            self.available_buffers.push_back(buffer_idx);
        } else {
            error!("No buffer allocated for stripe {stripe_id} on completion");
        }
    }
}

unsafe impl Send for StripeFetcher {}
unsafe impl Sync for StripeFetcher {}
