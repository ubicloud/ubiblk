use std::collections::{HashMap, VecDeque};

use log::{debug, error, info, warn};

use super::super::*;

use crate::{
    backends::SECTOR_SIZE,
    block_device::SharedMetadataState,
    stripe_source::{BlockDeviceStripeSource, StripeSource},
    utils::aligned_buffer_pool::AlignedBufferPool,
    Result,
};

const MAX_CONCURRENT_FETCHES: usize = 16;
const MAX_FETCH_RETRIES: u8 = 3;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FetchState {
    Queued,
    Fetching,
    Flushing,
    Fetched,
}

pub struct StripeFetcher {
    stripe_source: Box<dyn StripeSource>,
    fetch_target_channel: Box<dyn IoChannel>,
    #[cfg_attr(not(test), allow(dead_code))]
    source_sector_count: u64,
    target_sector_count: u64,
    stripe_sector_count: u64,
    fetch_queue: VecDeque<usize>,
    autofetch_queue: VecDeque<usize>,
    buffer_pool: AlignedBufferPool,
    shared_metadata_state: SharedMetadataState,
    stripe_states: HashMap<usize, FetchState>,
    stripe_fetch_retries: HashMap<usize, u8>,
    allocated_buffers: HashMap<usize, SharedBuffer>,
    finished_fetches: Vec<(usize, bool)>,
    autofetch: bool,
    disconnected: bool,
}

impl StripeFetcher {
    pub fn new(
        stripe_source: Box<dyn StripeSource>,
        target_dev: &dyn BlockDevice,
        stripe_sector_count: u64,
        shared_metadata_state: SharedMetadataState,
        alignment: usize,
        autofetch: bool,
    ) -> Result<Self> {
        let fetch_target_channel = target_dev.create_channel()?;

        let stripe_size_u64 = stripe_sector_count
            .checked_mul(SECTOR_SIZE as u64)
            .ok_or_else(|| {
                crate::ubiblk_error!(InvalidParameter {
                    description: "stripe size too large".to_string(),
                })
            })?;
        let stripe_size = stripe_size_u64 as usize;

        let buffer_pool = AlignedBufferPool::new(alignment, MAX_CONCURRENT_FETCHES, stripe_size);
        let source_sector_count = stripe_source.sector_count();
        let target_sector_count = target_dev.sector_count();
        if target_sector_count < source_sector_count {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: format!(
                    "target device too small ({} sectors) for source device ({} sectors)",
                    target_sector_count, source_sector_count
                ),
            }));
        }

        let source_stripe_count = source_sector_count.div_ceil(stripe_sector_count);
        let autofetch_queue = if autofetch {
            (0..source_stripe_count as usize).collect()
        } else {
            VecDeque::new()
        };

        Ok(StripeFetcher {
            stripe_source,
            fetch_target_channel,
            source_sector_count,
            target_sector_count,
            stripe_sector_count,
            fetch_queue: VecDeque::new(),
            buffer_pool,
            shared_metadata_state,
            stripe_states: HashMap::new(),
            stripe_fetch_retries: HashMap::new(),
            allocated_buffers: HashMap::new(),
            finished_fetches: Vec::new(),
            autofetch,
            autofetch_queue,
            disconnected: false,
        })
    }

    pub fn busy(&self) -> bool {
        !self.fetch_queue.is_empty()
            || self.stripe_source.busy()
            || self.fetch_target_channel.busy()
            || !self.finished_fetches.is_empty()
            || !self.autofetch_queue.is_empty()
    }

    pub fn handle_fetch_request(&mut self, stripe_id: usize) {
        if self
            .shared_metadata_state
            .stripe_fetched_if_needed(stripe_id)
        {
            debug!("Stripe {stripe_id} already fetched or has no source data, skipping fetch");
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
        self.update_autofetch();
        self.start_fetches();
        self.poll_fetches();
    }

    pub fn disconnect_from_source_if_all_fetched(&mut self) {
        if !self.disconnected
            && !self.busy()
            && self.shared_metadata_state.source_stripes()
                == self.shared_metadata_state.fetched_stripes()
        {
            let prev_source_sector_count = self.stripe_source.sector_count();
            let result =
                BlockDeviceStripeSource::new(NullBlockDevice::new(), self.stripe_sector_count);
            // NullBlockDevice always succeeds, so we can ignore errors here
            if let Ok(source) = result {
                self.stripe_source = Box::new(source);
                if prev_source_sector_count != 0 {
                    info!("All stripes fetched, disconnected from source device");
                }
                self.disconnected = true;
            }
        }
    }

    #[cfg(test)]
    pub fn source_stripe_count(&self) -> u64 {
        self.source_sector_count.div_ceil(self.stripe_sector_count)
    }

    pub fn take_finished_fetches(&mut self) -> Vec<(usize, bool)> {
        std::mem::take(&mut self.finished_fetches)
    }

    pub fn update_autofetch(&mut self) {
        if self.autofetch && self.fetch_queue.is_empty() {
            if let Some(stripe_id) = self.autofetch_queue.pop_front() {
                self.handle_fetch_request(stripe_id);
            }
        }
    }

    fn start_fetches(&mut self) {
        while !self.fetch_queue.is_empty() && self.buffer_pool.has_available() {
            let stripe_id = self.fetch_queue.pop_front().unwrap();

            let buf = self.buffer_pool.get_buffer().unwrap();
            self.allocated_buffers.insert(stripe_id, buf.clone());
            if let Err(e) = self.stripe_source.request(stripe_id, buf.clone()) {
                error!("Failed to request stripe {stripe_id} from source: {e:?}");
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
        for (stripe_id, success) in self.stripe_source.poll() {
            let buf = match self.allocated_buffers.get(&stripe_id) {
                Some(buf) => buf.clone(),
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

        if let Some(buf) = self.allocated_buffers.remove(&stripe_id) {
            self.buffer_pool.return_buffer(&buf);
        } else {
            error!("No buffer allocated for stripe {stripe_id} on completion");
        }

        if success {
            self.stripe_states.insert(stripe_id, FetchState::Fetched);
            self.stripe_fetch_retries.remove(&stripe_id);
            self.finished_fetches.push((stripe_id, true));
            return;
        }

        let retries = self.stripe_fetch_retries.entry(stripe_id).or_insert(0);
        if *retries < MAX_FETCH_RETRIES {
            *retries += 1;
            warn!("Retrying stripe {stripe_id}, attempt {retries}");
            self.fetch_queue.push_back(stripe_id);
            self.stripe_states.insert(stripe_id, FetchState::Queued);
        } else {
            error!("Stripe {stripe_id} failed after {MAX_FETCH_RETRIES} retries");
            self.shared_metadata_state.set_stripe_failed(stripe_id);
            self.stripe_states.remove(&stripe_id);
            self.stripe_fetch_retries.remove(&stripe_id);
            self.finished_fetches.push((stripe_id, false));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block_device::bdev_test::TestBlockDevice;
    use crate::stripe_source::BlockDeviceStripeSource;

    struct TestState {
        source_dev: Box<TestBlockDevice>,
        target_dev: Box<TestBlockDevice>,
        fetcher: StripeFetcher,
    }

    fn prep(autofetch: bool) -> TestState {
        let source_size: u64 = 1024 * 1024; // 1 MiB
        let target_size: u64 = 2 * 1024 * 1024; // 2 MiB
        let stripe_sector_count_shift = 3; // 8 sectors per stripe
        let stripe_sector_count = 1u64 << stripe_sector_count_shift;

        let source_dev = Box::new(TestBlockDevice::new(source_size));
        let target_dev = Box::new(TestBlockDevice::new(target_size));

        let stripe_source = Box::new(
            BlockDeviceStripeSource::new(source_dev.clone(), stripe_sector_count).unwrap(),
        );

        let metadata = UbiMetadata::new(
            stripe_sector_count_shift,
            target_dev.stripe_count(stripe_sector_count),
            source_dev.stripe_count(stripe_sector_count),
        );

        let shared_metadata_state = SharedMetadataState::new(&metadata);

        let fetcher = StripeFetcher::new(
            stripe_source,
            &*target_dev,
            stripe_sector_count,
            shared_metadata_state.clone(),
            SECTOR_SIZE,
            autofetch,
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
        let mut state = prep(false);
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
        let mut state = prep(false);
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

    #[test]
    fn test_autofetch() {
        let mut state = prep(true);
        let finished = state.fetcher.take_finished_fetches();
        assert_eq!(finished.len(), 0);
        for _ in 0..1000 {
            state.fetcher.update();
        }
        let mut finished = state.fetcher.take_finished_fetches();
        let source_stripe_count = state.fetcher.source_stripe_count() as usize;
        assert_eq!(finished.len(), source_stripe_count);
        finished.sort_by_key(|(stripe_id, _)| *stripe_id);
        for (idx, (stripe_id, success)) in finished.iter().enumerate() {
            assert!(*stripe_id == idx);
            assert!(success);
        }
    }

    #[test]
    fn test_autofetch_prioritizes_manual() {
        let mut state = prep(true);
        for _ in 0..20 {
            state.fetcher.update();
        }
        let mut finished = state.fetcher.take_finished_fetches();
        assert!(!finished.is_empty());

        // We shouldn't have finished the following stripes in the first 20
        // cycles yet.
        let priority_list = vec![100, 110, 122];
        for stripe_id in &priority_list {
            assert!(finished.iter().all(|(sid, _)| *sid != *stripe_id));
        }

        // Now request those specifically.
        for stripe_id in &priority_list {
            state.fetcher.handle_fetch_request(*stripe_id);
        }

        for _ in 0..20 {
            state.fetcher.update();
        }
        let finished_2nd_batch = state.fetcher.take_finished_fetches();

        // The explicit requests should have been prioritized and completed.
        for stripe_id in &priority_list {
            assert!(finished_2nd_batch[..priority_list.len() + 1]
                .iter()
                .any(|(sid, _)| *sid == *stripe_id));
        }

        finished.extend(finished_2nd_batch);

        // Now process until all the autofetches are done.
        for _ in 0..1000 {
            state.fetcher.update();
        }

        finished.extend(state.fetcher.take_finished_fetches());

        let source_stripe_count = state.fetcher.source_stripe_count() as usize;
        assert_eq!(finished.len(), source_stripe_count);
        finished.sort_by_key(|(stripe_id, _)| *stripe_id);
        for (idx, (stripe_id, success)) in finished.iter().enumerate() {
            assert!(*stripe_id == idx);
            assert!(success);
        }
    }

    #[test]
    fn test_retry_logic() {
        let mut state = prep(false);
        let buf = state.fetcher.buffer_pool.get_buffer().unwrap();
        state.fetcher.allocated_buffers.insert(0, buf);

        state.fetcher.fetch_completed(0, false);
        assert!(!state.fetcher.fetch_queue.is_empty());
        state.fetcher.fetch_queue.pop_front();
        assert_eq!(
            state.fetcher.stripe_states.get(&0),
            Some(&FetchState::Queued)
        );
        assert_eq!(state.fetcher.stripe_fetch_retries.get(&0), Some(&1));

        let buf = state.fetcher.buffer_pool.get_buffer().unwrap();
        state.fetcher.allocated_buffers.insert(0, buf);

        assert!(!state.fetcher.shared_metadata_state.is_stripe_failed(0));

        state.fetcher.fetch_completed(0, false);
        assert!(!state.fetcher.fetch_queue.is_empty());
        state.fetcher.fetch_queue.pop_front();
        assert_eq!(state.fetcher.stripe_fetch_retries.get(&0), Some(&2));

        let buf = state.fetcher.buffer_pool.get_buffer().unwrap();
        state.fetcher.allocated_buffers.insert(0, buf);

        assert!(!state.fetcher.shared_metadata_state.is_stripe_failed(0));

        state.fetcher.fetch_completed(0, false);
        assert!(!state.fetcher.fetch_queue.is_empty());
        state.fetcher.fetch_queue.pop_front();
        assert_eq!(state.fetcher.stripe_fetch_retries.get(&0), Some(&3));

        let buf = state.fetcher.buffer_pool.get_buffer().unwrap();
        state.fetcher.allocated_buffers.insert(0, buf);

        state.fetcher.fetch_completed(0, false);
        assert!(state.fetcher.fetch_queue.is_empty());
        assert_eq!(state.fetcher.stripe_states.get(&0), None);
        assert!(state.fetcher.shared_metadata_state.is_stripe_failed(0));
    }

    #[test]
    fn test_disconnects_when_all_fetched() {
        let mut state = prep(false);
        let source_stripe_count = state.fetcher.source_stripe_count() as usize;

        // Not done yet
        state.fetcher.disconnect_from_source_if_all_fetched();
        assert_ne!(state.fetcher.stripe_source.sector_count(), 0);
        assert!(!state.fetcher.disconnected);

        // Mark all fetched
        for stripe_id in 0..source_stripe_count {
            state.fetcher.shared_metadata_state.set_stripe_header(
                stripe_id,
                metadata_flags::FETCHED | metadata_flags::HAS_SOURCE,
            );
        }

        // Now should disconnect
        state.fetcher.disconnect_from_source_if_all_fetched();
        assert_eq!(state.fetcher.stripe_source.sector_count(), 0);
        assert!(state.fetcher.disconnected);
    }
}
