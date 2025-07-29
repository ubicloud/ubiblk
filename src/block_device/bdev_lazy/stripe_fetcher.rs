use std::collections::VecDeque;
use std::{cell::RefCell, rc::Rc};

use super::super::*;
use super::metadata::UBI_MAX_STRIPES;
use crate::utils::aligned_buffer::AlignedBuf;
use crate::{vhost_backend::SECTOR_SIZE, Result, VhostUserBlockError};
use log::{debug, error};
use std::sync::{
    atomic::{AtomicU8, Ordering},
    Arc,
};

const MAX_CONCURRENT_FETCHES: usize = 16;

#[repr(u8)]
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum StripeStatus {
    NotFetched,
    Queued,
    Fetching,
    Fetched,
    Failed,
}

#[derive(Debug, Clone)]
pub struct StripeStatusVec {
    pub data: Arc<Vec<AtomicU8>>,
    pub stripe_sector_count: u64,
    pub source_sector_count: u64,
    pub stripe_count: u64,
}

impl StripeStatusVec {
    pub fn sector_to_stripe_id(&self, sector: u64) -> usize {
        (sector / self.stripe_sector_count) as usize
    }

    pub fn stripe_status(&self, stripe_id: usize) -> StripeStatus {
        if (stripe_id as u64) < self.stripe_count {
            match self.data[stripe_id].load(Ordering::Acquire) {
                0 => StripeStatus::NotFetched,
                1 => StripeStatus::Queued,
                2 => StripeStatus::Fetching,
                3 => StripeStatus::Fetched,
                4 => StripeStatus::Failed,
                other => {
                    error!(
                        "Invalid stripe status value: {other} for stripe_id: {stripe_id}. Defaulting to Failed."
                    );
                    StripeStatus::Failed
                }
            }
        } else {
            StripeStatus::Fetched
        }
    }

    pub fn set_stripe_status(&self, stripe_id: usize, status: StripeStatus) {
        if (stripe_id as u64) >= self.stripe_count {
            error!(
                "Invalid stripe_id: {}. Must be less than stripe_count: {}",
                stripe_id, self.stripe_count
            );
            return;
        }
        self.data[stripe_id].store(status as u8, Ordering::Release);
    }

    pub fn stripe_sector_count(&self, stripe_id: usize) -> u32 {
        let stripe_sector_count = self
            .stripe_sector_count
            .min(self.source_sector_count - (stripe_id as u64 * self.stripe_sector_count))
            as usize;
        stripe_sector_count as u32
    }

    pub fn new(metadata: &UbiMetadata, source_sector_count: u64) -> Result<Self> {
        let v = metadata
            .stripe_headers
            .iter()
            .map(|header| {
                if *header == 0 {
                    AtomicU8::new(StripeStatus::NotFetched as u8)
                } else {
                    AtomicU8::new(StripeStatus::Fetched as u8)
                }
            })
            .collect::<Vec<AtomicU8>>();
        let stripe_sector_count = 1u64 << metadata.stripe_sector_count_shift;
        let stripe_count = source_sector_count.div_ceil(stripe_sector_count);
        if stripe_count as usize > UBI_MAX_STRIPES {
            return Err(VhostUserBlockError::InvalidParameter {
                description: "source sector count exceeds maximum stripe count".to_string(),
            });
        }
        Ok(StripeStatusVec {
            data: Arc::new(v),
            stripe_sector_count,
            source_sector_count,
            stripe_count,
        })
    }
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
    stripes_fetched: usize,
    stripe_status_vec: StripeStatusVec,
}

impl StripeFetcher {
    pub fn new(
        source_dev: &dyn BlockDevice,
        target_dev: &dyn BlockDevice,
        stripe_sector_count: u64,
        stripe_status_vec: StripeStatusVec,
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
        Ok(StripeFetcher {
            fetch_source_channel,
            fetch_target_channel,
            source_sector_count,
            target_sector_count,
            stripe_sector_count,
            fetch_queue: VecDeque::new(),
            fetch_buffers,
            stripes_fetched: 0,
            stripe_status_vec,
        })
    }

    pub fn busy(&self) -> bool {
        !self.fetch_queue.is_empty()
            || self.fetch_source_channel.busy()
            || self.fetch_target_channel.busy()
    }

    pub fn stripe_status_vec(&self) -> StripeStatusVec {
        self.stripe_status_vec.clone()
    }

    pub fn handle_fetch_request(&mut self, stripe_id: usize) {
        match self.stripe_status_vec.stripe_status(stripe_id) {
            StripeStatus::NotFetched | StripeStatus::Failed => {
                debug!("Enqueueing stripe {stripe_id} for fetch");
                self.fetch_queue.push_back(stripe_id);
                self.stripe_status_vec
                    .set_stripe_status(stripe_id, StripeStatus::Queued);
            }
            StripeStatus::Fetched => {
                debug!("Stripe {stripe_id} already fetched");
            }
            StripeStatus::Queued | StripeStatus::Fetching => {
                debug!("Stripe {stripe_id} is already queued or fetching");
            }
        }
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

        if success {
            self.stripe_status_vec
                .set_stripe_status(stripe_id, StripeStatus::Fetched);
            self.stripes_fetched += 1;
        } else {
            self.stripe_status_vec
                .set_stripe_status(stripe_id, StripeStatus::Failed);
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

    fn poll_fetches(&mut self) -> Vec<(usize, bool)> {
        let mut result = Vec::new();
        for (buffer_idx, success) in self.fetch_source_channel.poll() {
            if !success || !self.start_write(buffer_idx) {
                result.push(self.fetch_completed(buffer_idx, false));
            }
        }

        for (buffer_idx, success) in self.fetch_target_channel.poll() {
            result.push(self.fetch_completed(buffer_idx, success));
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

            self.stripe_status_vec
                .set_stripe_status(stripe_id, StripeStatus::Fetching);
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
