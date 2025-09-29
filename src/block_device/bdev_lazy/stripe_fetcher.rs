use std::collections::{HashMap, VecDeque};

use super::super::*;
use super::metadata::SharedMetadataState;
use crate::utils::aligned_buffer_pool::AlignedBufferPool;
use crate::{vhost_backend::SECTOR_SIZE, Result, VhostUserBlockError};
use log::{debug, error};

const MAX_CONCURRENT_FETCHES: usize = 16;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FetchState {
    Queued,
    Fetching,
    Flushing,
    Fetched,
}

pub struct StripeFetcher {
    fetch_source_channel: Box<dyn IoChannel>,
    fetch_target_channel: Box<dyn IoChannel>,
    source_sector_count: u64,
    target_sector_count: u64,
    stripe_sector_count: u64,
    fetch_queue: VecDeque<usize>,
    buffer_pool: AlignedBufferPool,
    shared_metadata_state: SharedMetadataState,
    stripe_states: HashMap<usize, FetchState>,
    allocated_buffers: HashMap<usize, (SharedBuffer, usize)>,
    finished_fetches: Vec<(usize, bool)>,
}

impl StripeFetcher {
    pub fn new(
        source_dev: &dyn BlockDevice,
        target_dev: &dyn BlockDevice,
        stripe_sector_count: u64,
        shared_metadata_state: SharedMetadataState,
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

        let buffer_pool = AlignedBufferPool::new(alignment, MAX_CONCURRENT_FETCHES, stripe_size);
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
            buffer_pool,
            shared_metadata_state,
            stripe_states: HashMap::new(),
            allocated_buffers: HashMap::new(),
            finished_fetches: Vec::new(),
        })
    }

    pub fn busy(&self) -> bool {
        !self.fetch_queue.is_empty()
            || self.fetch_source_channel.busy()
            || self.fetch_target_channel.busy()
            || !self.finished_fetches.is_empty()
    }

    pub fn handle_fetch_request(&mut self, stripe_id: usize) {
        if self.shared_metadata_state.stripe_fetched(stripe_id) {
            debug!("Stripe {stripe_id} already fetched");
            return;
        }

        if self.stripe_states.contains_key(&stripe_id) {
            debug!("Stripe {stripe_id} has already been requested");
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

    pub fn take_finished_fetches(&mut self) -> Vec<(usize, bool)> {
        std::mem::take(&mut self.finished_fetches)
    }

    fn start_fetches(&mut self) {
        while !self.fetch_queue.is_empty() && self.buffer_pool.has_available() {
            let stripe_id = self.fetch_queue.pop_front().unwrap();
            let (buf, buffer_idx) = self.buffer_pool.get_buffer().unwrap();
            self.allocated_buffers
                .insert(stripe_id, (buf.clone(), buffer_idx));
            let stripe_sector_offset = stripe_id as u64 * self.stripe_sector_count;
            if stripe_sector_offset >= self.source_sector_count {
                error!("Stripe {stripe_id} beyond end of source");
                self.fetch_completed(stripe_id, false);
                continue;
            }

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
            let buf = match self.allocated_buffers.get(&stripe_id) {
                Some((buf, _)) => buf.clone(),
                None => {
                    error!("Received completion for unknown stripe {stripe_id}");
                    continue;
                }
            };

            if !success || !self.start_write(buf, stripe_id) {
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

    fn start_write(&mut self, buf: SharedBuffer, stripe_id: usize) -> bool {
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

        if success {
            self.stripe_states.insert(stripe_id, FetchState::Fetched);
        } else {
            self.stripe_states.remove(&stripe_id);
        }

        if let Some((_, buffer_idx)) = self.allocated_buffers.remove(&stripe_id) {
            self.buffer_pool.return_buffer(buffer_idx);
        } else {
            error!("No buffer allocated for stripe {stripe_id} on completion");
        }

        self.finished_fetches.push((stripe_id, success));
    }
}

unsafe impl Send for StripeFetcher {}
unsafe impl Sync for StripeFetcher {}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::block_device::bdev_test::TestBlockDevice;

    struct TestState {
        source_dev: Box<TestBlockDevice>,
        target_dev: Box<TestBlockDevice>,
        fetcher: StripeFetcher,
    }

    fn prep() -> TestState {
        let source_size: u64 = 1024 * 1024; // 1 MiB
        let target_size: u64 = 2 * 1024 * 1024; // 2 MiB
        let stripe_sector_count_shift = 3; // 8 sectors per stripe
        let stripe_sector_count = 1u64 << stripe_sector_count_shift;
        let source_stripe_count = source_size.div_ceil(stripe_sector_count * 512) as usize;
        let target_stripe_count = target_size.div_ceil(stripe_sector_count * 512) as usize;

        let source_dev = Box::new(TestBlockDevice::new(source_size));
        let target_dev = Box::new(TestBlockDevice::new(target_size));

        let metadata = UbiMetadata::new(
            stripe_sector_count_shift,
            target_stripe_count,
            source_stripe_count,
        );

        let shared_metadata_state = SharedMetadataState::new(&metadata);

        let fetcher = StripeFetcher::new(
            &*source_dev,
            &*target_dev,
            stripe_sector_count,
            shared_metadata_state.clone(),
            512,
        )
        .unwrap();

        TestState {
            source_dev,
            target_dev,
            fetcher,
        }
    }

    #[test]
    fn test_basic_fetch() {
        let mut state = prep();
        state.fetcher.handle_fetch_request(0);
        for _ in 0..10 {
            state.fetcher.update();
        }
        let finished = state.fetcher.take_finished_fetches();
        assert_eq!(finished.len(), 1);
        assert_eq!(finished[0], (0, true));

        let source_metrics = state.source_dev.metrics.read().unwrap();
        assert_eq!(source_metrics.reads, 1);
        assert_eq!(source_metrics.writes, 0);
        assert_eq!(source_metrics.flushes, 0);

        let target_metrics = state.target_dev.metrics.read().unwrap();
        assert_eq!(target_metrics.reads, 0);
        assert_eq!(target_metrics.writes, 1);
        assert_eq!(target_metrics.flushes, 1);
    }

    #[test]
    fn test_repeat_requests_ignored() {
        let mut state = prep();
        state.fetcher.handle_fetch_request(1);
        for _ in 0..10 {
            state.fetcher.update();
        }
        let finished = state.fetcher.take_finished_fetches();
        assert_eq!(finished.len(), 1);
        assert_eq!(finished[0], (1, true));

        state.fetcher.handle_fetch_request(1);
        for _ in 0..10 {
            state.fetcher.update();
        }
        let finished = state.fetcher.take_finished_fetches();
        assert_eq!(finished.len(), 0);

        let source_metrics = state.source_dev.metrics.read().unwrap();
        assert_eq!(source_metrics.reads, 1);
        assert_eq!(source_metrics.writes, 0);
        assert_eq!(source_metrics.flushes, 0);

        let target_metrics = state.target_dev.metrics.read().unwrap();
        assert_eq!(target_metrics.reads, 0);
        assert_eq!(target_metrics.writes, 1);
        assert_eq!(target_metrics.flushes, 1);
    }
}
