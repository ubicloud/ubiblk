use crate::{
    backends::SECTOR_SIZE,
    block_device::{
        bdev_lazy::metadata::types::{write_sector_with_crc32, STRIPE_HEADERS_PER_SECTOR},
        metadata_flags, BlockDevice, IoChannel, SharedBuffer, SharedMetadataState, UbiMetadata,
    },
    utils::AlignedBufferPool,
    Result,
};
use log::{debug, error};
use std::collections::{HashMap, HashSet, VecDeque};

const MAX_CONCURRENT_CHANGES: usize = 16;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MetadataFlusherRequestKind {
    SetFetched,
    SetWritten,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct MetadataFlusherRequest {
    stripe_id: usize,
    kind: MetadataFlusherRequestKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RequestStage {
    Writing,
    Flushing,
}

struct HeaderUpdateStatus {
    buffer: SharedBuffer,
    stage: RequestStage,
    stripe_id: usize,
    header: u8,
    /// The specific flag bit(s) added by this request, used to revert on failure.
    requested_bitmask: u8,
    sector: u64,
}

pub struct MetadataFlusher {
    channel: Box<dyn IoChannel>,
    metadata: Box<UbiMetadata>,
    shared_state: SharedMetadataState,
    sectors_being_updated: HashSet<u64>,
    header_updates: HashMap<usize, HeaderUpdateStatus>,
    queued_requests: VecDeque<MetadataFlusherRequest>,
    buffer_pool: AlignedBufferPool,
    /// A submit failed with requests in the channel. Their SQEs stay in the
    /// ring and the next submit enters them (see `bdev_uring::submit`), so
    /// their completions are still owed: the statuses, buffers and sectors
    /// stay as they are and `update` submits again until one succeeds.
    resubmit_needed: bool,
}

impl MetadataFlusher {
    pub fn new(
        metadata_dev: &dyn BlockDevice,
        source_sector_count: u64,
        shared_state: SharedMetadataState,
    ) -> Result<Self> {
        let channel = metadata_dev.create_channel()?;
        let metadata = UbiMetadata::load_from_bdev(metadata_dev)?;

        // Validate stripe count
        let source_stripe_count = source_sector_count.div_ceil(metadata.stripe_sector_count());
        if source_stripe_count > metadata.stripe_count() {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: format!(
                    "Source stripe count {} exceeds metadata stripe count {}",
                    source_stripe_count,
                    metadata.stripe_count()
                ),
            }));
        }

        Ok(MetadataFlusher {
            channel,
            shared_state,
            metadata,
            sectors_being_updated: HashSet::new(),
            queued_requests: VecDeque::new(),
            buffer_pool: AlignedBufferPool::new(4096, MAX_CONCURRENT_CHANGES, SECTOR_SIZE),
            header_updates: HashMap::new(),
            resubmit_needed: false,
        })
    }

    pub fn busy(&self) -> bool {
        !self.sectors_being_updated.is_empty() || !self.queued_requests.is_empty()
    }

    pub fn set_stripe_fetched(&mut self, stripe_id: usize) {
        self.queued_requests.push_back(MetadataFlusherRequest {
            stripe_id,
            kind: MetadataFlusherRequestKind::SetFetched,
        });
    }

    pub fn set_stripe_written(&mut self, stripe_id: usize) {
        self.queued_requests.push_back(MetadataFlusherRequest {
            stripe_id,
            kind: MetadataFlusherRequestKind::SetWritten,
        });
    }

    pub fn update(&mut self) {
        self.resubmit();
        self.start_writes();
        self.poll_channel();
    }

    /// Submit the requests added to the channel. A failed submit leaves the
    /// SQEs in the ring for the next one, so the requests may yet run and
    /// their completions will arrive: nothing is undone here. Returning a
    /// buffer now would let the kernel write another sector's bytes to this
    /// request's sector, with a valid CRC, and reverting the header now
    /// would report a failure for a write that may still land.
    fn submit(&mut self, what: &str) {
        match self.channel.submit() {
            Ok(()) => self.resubmit_needed = false,
            Err(e) => {
                error!("Failed to submit metadata {what}: {e}");
                self.resubmit_needed = true;
            }
        }
    }

    /// Enter the SQEs a failed submit left in the ring, so that their
    /// completions can arrive even if no new request is added.
    fn resubmit(&mut self) {
        if !self.resubmit_needed {
            return;
        }
        match self.channel.submit() {
            Ok(()) => self.resubmit_needed = false,
            Err(e) => debug!("Metadata requests still cannot be submitted: {e}"),
        }
    }

    fn poll_channel(&mut self) {
        let mut finished_stripes = Vec::new();
        let mut newly_flushing = false;

        for (stripe_id, success) in self.channel.poll() {
            let maybe_status = self.header_updates.get_mut(&stripe_id);
            match (maybe_status, success) {
                (None, _) => {
                    error!("Received unexpected response for stripe {stripe_id}");
                }
                (Some(status), false) => {
                    error!("Failed to write metadata for stripe {stripe_id}");
                    // Revert only the specific flag bit we added, so a future
                    // retry for the same operation won't be skipped by the
                    // dedup check in start_writes.
                    self.metadata.stripe_headers[status.stripe_id] &= !status.requested_bitmask;
                    // Only return the buffer if it hasn't already been returned.
                    // On write success the buffer is returned before transitioning
                    // to Flushing, so a subsequent flush failure must not return
                    // it a second time.
                    if status.stage == RequestStage::Writing {
                        self.buffer_pool.return_buffer(&status.buffer);
                    }
                    self.sectors_being_updated.remove(&status.sector);
                    self.header_updates.remove(&stripe_id);
                }
                (Some(status), true) => match status.stage {
                    RequestStage::Writing => {
                        self.buffer_pool.return_buffer(&status.buffer);
                        self.channel.add_flush(stripe_id);
                        status.stage = RequestStage::Flushing;
                        newly_flushing = true;
                    }
                    RequestStage::Flushing => {
                        self.sectors_being_updated.remove(&(status.sector));
                        finished_stripes.push((status.stripe_id, status.header));
                    }
                },
            }
        }

        for (stripe, header) in finished_stripes {
            debug!("Stripe {stripe} metadata updated with header {header}");
            self.header_updates.remove(&stripe);
            self.shared_state.set_stripe_header(stripe, header);
        }

        if newly_flushing {
            self.submit("flushes");
        }
    }

    fn start_writes(&mut self) {
        let mut newly_added = false;

        while !self.queued_requests.is_empty() && self.buffer_pool.has_available() {
            let req = *self.queued_requests.front().unwrap();
            let group = UbiMetadata::stripe_id_to_group(req.stripe_id);
            let sector = UbiMetadata::stripe_id_to_sector(req.stripe_id);
            if self.sectors_being_updated.contains(&sector) {
                // Updates to each sector should be serialized
                break;
            }
            self.queued_requests.pop_front();

            let requested_bitmask = match req.kind {
                MetadataFlusherRequestKind::SetFetched => metadata_flags::FETCHED,
                MetadataFlusherRequestKind::SetWritten => metadata_flags::WRITTEN,
            };

            if self.metadata.stripe_headers[req.stripe_id] & requested_bitmask != 0 {
                // Already set, skip
                continue;
            }

            let buf = self.buffer_pool.get_buffer().unwrap();
            self.metadata.stripe_headers[req.stripe_id] |= requested_bitmask;

            let headers_start = group * STRIPE_HEADERS_PER_SECTOR;
            let headers_end =
                (headers_start + STRIPE_HEADERS_PER_SECTOR).min(self.metadata.stripe_headers.len());
            let headers = &self.metadata.stripe_headers[headers_start..headers_end];
            write_sector_with_crc32(buf.borrow_mut().as_mut_slice(), headers);

            self.channel
                .add_write(sector, 1, buf.clone(), req.stripe_id);
            self.sectors_being_updated.insert(sector);
            self.header_updates.insert(
                req.stripe_id,
                HeaderUpdateStatus {
                    buffer: buf,
                    stage: RequestStage::Writing,
                    stripe_id: req.stripe_id,
                    header: self.metadata.stripe_headers[req.stripe_id],
                    requested_bitmask,
                    sector,
                },
            );
            newly_added = true;
        }

        if newly_added {
            self.submit("writes");
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::block_device::bdev_test::TestBlockDevice;

    use super::*;

    fn init_metadata_device() -> TestBlockDevice {
        let metadata = UbiMetadata::new(11, 16, 16);
        let block_device = TestBlockDevice::new(8 * 1024);
        metadata.save_to_bdev(&block_device).unwrap();
        block_device
    }

    fn wait_for_completion(metadata_flusher: &mut MetadataFlusher) {
        let start = std::time::Instant::now();
        while start.elapsed().as_secs() < 1 && metadata_flusher.busy() {
            metadata_flusher.update();
        }
    }

    #[test]
    fn test_metadata_flusher() {
        let metadata_dev = init_metadata_device();
        let shared_state = {
            let metadata = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
            SharedMetadataState::new(&metadata)
        };
        let mut metadata_flusher =
            MetadataFlusher::new(&metadata_dev, 8 * 1024, shared_state.clone()).unwrap();

        metadata_flusher.set_stripe_fetched(5);
        metadata_flusher.set_stripe_fetched(6);

        for stripe_id in 5..=6 {
            assert!(!shared_state.stripe_fetched(stripe_id));
            assert!(!shared_state.stripe_written(stripe_id));
        }

        wait_for_completion(&mut metadata_flusher);

        for stripe_id in 5..=6 {
            assert!(shared_state.stripe_fetched(stripe_id));
            assert!(!shared_state.stripe_written(stripe_id));
        }

        metadata_flusher.set_stripe_written(7);
        assert!(!shared_state.stripe_written(7));
        assert!(!shared_state.stripe_fetched(7));

        wait_for_completion(&mut metadata_flusher);

        assert!(!shared_state.stripe_fetched(7));
        assert!(shared_state.stripe_written(7));
    }

    #[test]
    fn test_source_stripe_count_too_large() {
        let metadata_dev = init_metadata_device();
        let shared_state = {
            let metadata = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
            SharedMetadataState::new(&metadata)
        };
        let metadata_flusher =
            MetadataFlusher::new(&metadata_dev, 1024 * 1024 * 1024, shared_state);
        assert!(metadata_flusher.is_err());
    }

    #[test]
    fn test_request_serialization() {
        let metadata_dev = init_metadata_device();
        let shared_state = {
            let metadata = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
            SharedMetadataState::new(&metadata)
        };
        let mut metadata_flusher =
            MetadataFlusher::new(&metadata_dev, 8 * 1024, shared_state.clone()).unwrap();

        // Stripes 0-7 are in sector 1
        for stripe_id in 0..8 {
            metadata_flusher.set_stripe_fetched(stripe_id);
            if stripe_id % 3 == 0 {
                // Interleave some writes
                metadata_flusher.set_stripe_written(stripe_id);
            }
        }

        // add some duplicate requests
        metadata_flusher.set_stripe_fetched(2);
        metadata_flusher.set_stripe_written(3);

        wait_for_completion(&mut metadata_flusher);

        for stripe_id in 0..8 {
            assert!(shared_state.stripe_fetched(stripe_id));
            if stripe_id % 3 == 0 {
                assert!(shared_state.stripe_written(stripe_id));
            } else {
                assert!(!shared_state.stripe_written(stripe_id));
            }
        }
    }

    #[test]
    fn test_write_failure_allows_retry() {
        let metadata_dev = init_metadata_device();
        let shared_state = {
            let metadata = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
            SharedMetadataState::new(&metadata)
        };
        let mut metadata_flusher =
            MetadataFlusher::new(&metadata_dev, 8 * 1024, shared_state.clone()).unwrap();

        // Queue a fetched request and inject a write failure
        metadata_flusher.set_stripe_fetched(5);
        metadata_dev
            .fail_next
            .store(true, std::sync::atomic::Ordering::SeqCst);

        // First update: start_writes issues add_write (which fails), poll_channel sees failure
        metadata_flusher.update();

        // Stripe 5 should NOT be marked fetched in shared state
        assert!(!shared_state.stripe_fetched(5));
        // Flusher should not be busy (failure was handled, no pending requests)
        assert!(!metadata_flusher.busy());

        // Retry: queue the same request again - should NOT be skipped by dedup
        metadata_flusher.set_stripe_fetched(5);
        wait_for_completion(&mut metadata_flusher);

        // Now it should succeed
        assert!(shared_state.stripe_fetched(5));
    }

    #[test]
    fn test_write_failure_does_not_affect_other_stripes() {
        let metadata_dev = init_metadata_device();
        let shared_state = {
            let metadata = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
            SharedMetadataState::new(&metadata)
        };
        let mut metadata_flusher =
            MetadataFlusher::new(&metadata_dev, 8 * 1024, shared_state.clone()).unwrap();

        // First, successfully set stripe 5 as fetched
        metadata_flusher.set_stripe_fetched(5);
        wait_for_completion(&mut metadata_flusher);
        assert!(shared_state.stripe_fetched(5));

        // Now try to set stripe 5 as written, but inject a failure.
        // Stripe 5 is in sector group 0 (stripe 5 / 508 = 0), sector 1.
        metadata_flusher.set_stripe_written(5);
        metadata_dev
            .fail_next
            .store(true, std::sync::atomic::Ordering::SeqCst);
        metadata_flusher.update();

        // The written flag should NOT be set, but fetched should still be set
        assert!(shared_state.stripe_fetched(5));
        assert!(!shared_state.stripe_written(5));

        // Retry written - should succeed
        metadata_flusher.set_stripe_written(5);
        wait_for_completion(&mut metadata_flusher);
        assert!(shared_state.stripe_written(5));
        assert!(shared_state.stripe_fetched(5));
    }

    #[test]
    fn test_metadata_flusher_coalesces_duplicate_requests() {
        let metadata_dev = init_metadata_device();
        let shared_state = {
            let metadata = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
            SharedMetadataState::new(&metadata)
        };
        let mut metadata_flusher =
            MetadataFlusher::new(&metadata_dev, 8 * 1024, shared_state.clone()).unwrap();
        let (start_writes, start_flushes) = {
            let metrics = metadata_dev.metrics.read().unwrap();
            (metrics.writes, metrics.flushes)
        };

        metadata_flusher.set_stripe_written(3);
        metadata_flusher.set_stripe_written(3);
        metadata_flusher.set_stripe_written(3);
        metadata_flusher.set_stripe_fetched(3);
        metadata_flusher.set_stripe_fetched(3);

        assert!(!shared_state.stripe_written(3));
        assert!(!shared_state.stripe_fetched(3));

        wait_for_completion(&mut metadata_flusher);

        assert!(shared_state.stripe_written(3));
        assert!(shared_state.stripe_fetched(3));

        let metrics = metadata_dev.metrics.read().unwrap();
        assert_eq!(metrics.writes - start_writes, 2);
        assert_eq!(metrics.flushes - start_flushes, 2);
    }

    fn io_counts(metadata_dev: &TestBlockDevice) -> (usize, usize) {
        let metrics = metadata_dev.metrics.read().unwrap();
        (metrics.writes, metrics.flushes)
    }

    /// How many buffers the pool has on offer, so a test can tell whether a
    /// request's buffer has been returned.
    fn spare_buffers(metadata_flusher: &mut MetadataFlusher) -> usize {
        let mut spare = Vec::new();
        while let Some(buf) = metadata_flusher.buffer_pool.get_buffer() {
            spare.push(buf);
        }
        for buf in &spare {
            metadata_flusher.buffer_pool.return_buffer(buf);
        }
        spare.len()
    }

    #[test]
    fn test_write_submit_failure_keeps_request_until_completion_lands() {
        // A failed submit leaves the write SQE in the ring, where the next
        // submit enters it, so the write may still happen. The request must
        // keep its status, buffer and sector until the completion arrives,
        // and nothing may be reported before then.
        let metadata_dev = init_metadata_device();
        let shared_state = {
            let metadata = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
            SharedMetadataState::new(&metadata)
        };
        let mut metadata_flusher =
            MetadataFlusher::new(&metadata_dev, 8 * 1024, shared_state.clone()).unwrap();
        let (writes, flushes) = io_counts(&metadata_dev);
        assert_eq!(spare_buffers(&mut metadata_flusher), MAX_CONCURRENT_CHANGES);

        metadata_flusher.set_stripe_fetched(5);
        metadata_dev
            .fail_submit
            .store(true, std::sync::atomic::Ordering::SeqCst);
        metadata_flusher.update();

        // Nothing reported, nothing undone: the flag stays in memory for the
        // sector image the kernel will read, and the buffer is not on offer.
        assert!(!shared_state.stripe_fetched(5));
        assert!(metadata_flusher.busy());
        assert_eq!(
            metadata_flusher.header_updates[&5].stage,
            RequestStage::Writing
        );
        assert_ne!(
            metadata_flusher.metadata.stripe_headers[5] & metadata_flags::FETCHED,
            0
        );
        assert_eq!(
            spare_buffers(&mut metadata_flusher),
            MAX_CONCURRENT_CHANGES - 1
        );

        // A submit that fails again changes nothing: the write is neither
        // re-issued nor given up on.
        metadata_dev
            .fail_submit
            .store(true, std::sync::atomic::Ordering::SeqCst);
        metadata_flusher.update();
        assert!(!shared_state.stripe_fetched(5));
        assert!(metadata_flusher.busy());
        assert_eq!(io_counts(&metadata_dev), (writes + 1, flushes));
        assert_eq!(
            spare_buffers(&mut metadata_flusher),
            MAX_CONCURRENT_CHANGES - 1
        );

        // The next submit succeeds, the completion lands, and the request
        // finishes once.
        wait_for_completion(&mut metadata_flusher);
        assert!(shared_state.stripe_fetched(5));
        assert!(!metadata_flusher.busy());
        assert_eq!(io_counts(&metadata_dev), (writes + 1, flushes + 1));
        assert_eq!(spare_buffers(&mut metadata_flusher), MAX_CONCURRENT_CHANGES);
    }

    #[test]
    fn test_write_submit_failure_reports_failed_completion_when_it_lands() {
        // The completion a failed submit still owes may itself report a
        // failure. The flag is reverted and the buffer returned when that
        // completion arrives, not at the failed submit.
        let metadata_dev = init_metadata_device();
        let shared_state = {
            let metadata = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
            SharedMetadataState::new(&metadata)
        };
        let mut metadata_flusher =
            MetadataFlusher::new(&metadata_dev, 8 * 1024, shared_state.clone()).unwrap();

        metadata_flusher.set_stripe_fetched(5);
        metadata_dev
            .fail_next
            .store(true, std::sync::atomic::Ordering::SeqCst);
        metadata_dev
            .fail_submit
            .store(true, std::sync::atomic::Ordering::SeqCst);
        metadata_flusher.update();

        assert!(metadata_flusher.busy());
        assert_ne!(
            metadata_flusher.metadata.stripe_headers[5] & metadata_flags::FETCHED,
            0
        );
        assert_eq!(
            spare_buffers(&mut metadata_flusher),
            MAX_CONCURRENT_CHANGES - 1
        );

        // The resubmit succeeds and the failed completion is processed.
        metadata_flusher.update();
        assert!(!shared_state.stripe_fetched(5));
        assert!(!metadata_flusher.busy());
        assert_eq!(
            metadata_flusher.metadata.stripe_headers[5] & metadata_flags::FETCHED,
            0
        );
        assert_eq!(spare_buffers(&mut metadata_flusher), MAX_CONCURRENT_CHANGES);

        // Retry: queue the same request again - should NOT be skipped by dedup
        metadata_flusher.set_stripe_fetched(5);
        wait_for_completion(&mut metadata_flusher);
        assert!(shared_state.stripe_fetched(5));
    }

    #[test]
    fn test_flush_failure_no_double_buffer_return() {
        // Regression: when a write succeeds and the subsequent flush fails,
        // the error handler must NOT return the buffer a second time (it was
        // already returned when transitioning to Flushing).
        let metadata_dev = init_metadata_device();
        let shared_state = {
            let metadata = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
            SharedMetadataState::new(&metadata)
        };
        let mut metadata_flusher =
            MetadataFlusher::new(&metadata_dev, 8 * 1024, shared_state.clone()).unwrap();

        // Queue a request and let the write complete normally
        metadata_flusher.set_stripe_fetched(5);
        metadata_flusher.start_writes();

        // Set fail_next so that add_flush() (called when poll_channel
        // processes the write completion) will enqueue a flush failure.
        metadata_dev
            .fail_next
            .store(true, std::sync::atomic::Ordering::SeqCst);
        metadata_flusher.poll_channel();

        // Now poll_channel again to process the flush failure.
        // Without the fix this panics due to double buffer return.
        metadata_flusher.poll_channel();

        // Stripe 5 should NOT be marked fetched (flush failed)
        assert!(!shared_state.stripe_fetched(5));
        // Flusher should not be busy (failure was cleaned up)
        assert!(!metadata_flusher.busy());
    }

    #[test]
    fn test_flush_failure_allows_retry() {
        // After a flush failure, the same stripe operation can be retried
        // and should succeed.
        let metadata_dev = init_metadata_device();
        let shared_state = {
            let metadata = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
            SharedMetadataState::new(&metadata)
        };
        let mut metadata_flusher =
            MetadataFlusher::new(&metadata_dev, 8 * 1024, shared_state.clone()).unwrap();

        // Queue a request and let the write complete normally
        metadata_flusher.set_stripe_fetched(5);
        metadata_flusher.start_writes();

        // Inject flush failure
        metadata_dev
            .fail_next
            .store(true, std::sync::atomic::Ordering::SeqCst);
        metadata_flusher.poll_channel();
        metadata_flusher.poll_channel();

        // Verify the failure state
        assert!(!shared_state.stripe_fetched(5));
        assert!(!metadata_flusher.busy());

        // Retry: queue the same request again - should NOT be skipped by dedup
        metadata_flusher.set_stripe_fetched(5);
        wait_for_completion(&mut metadata_flusher);

        // Now it should succeed
        assert!(shared_state.stripe_fetched(5));
    }

    #[test]
    fn test_flush_submit_failure_keeps_request_until_completion_lands() {
        // The same for a flush: its SQE stays in the ring, the request stays
        // in Flushing, and the stripe lands when the fsync completes.
        let metadata_dev = init_metadata_device();
        let shared_state = {
            let metadata = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
            SharedMetadataState::new(&metadata)
        };
        let mut metadata_flusher =
            MetadataFlusher::new(&metadata_dev, 8 * 1024, shared_state.clone()).unwrap();
        let (writes, flushes) = io_counts(&metadata_dev);

        // Queue a request and let the write succeed
        metadata_flusher.set_stripe_fetched(5);
        metadata_flusher.start_writes();

        // Poll sees the write completion and adds a flush, whose submit fails.
        metadata_dev
            .fail_submit
            .store(true, std::sync::atomic::Ordering::SeqCst);
        metadata_flusher.poll_channel();
        assert!(!shared_state.stripe_fetched(5));
        assert!(metadata_flusher.busy());
        assert_eq!(
            metadata_flusher.header_updates[&5].stage,
            RequestStage::Flushing
        );

        // A submit that fails again changes nothing.
        metadata_dev
            .fail_submit
            .store(true, std::sync::atomic::Ordering::SeqCst);
        metadata_flusher.update();
        assert!(!shared_state.stripe_fetched(5));
        assert!(metadata_flusher.busy());
        assert_eq!(io_counts(&metadata_dev), (writes + 1, flushes + 1));

        // The next submit succeeds and the flush completion lands.
        wait_for_completion(&mut metadata_flusher);
        assert!(shared_state.stripe_fetched(5));
        assert!(!metadata_flusher.busy());
        assert_eq!(io_counts(&metadata_dev), (writes + 1, flushes + 1));
    }
}
