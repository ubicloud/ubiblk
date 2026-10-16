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
use std::collections::{hash_map::Entry, HashMap, VecDeque};

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

/// One stripe's part of a sector write.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct HeaderUpdate {
    stripe_id: usize,
    header: u8,
    /// The specific flag bit(s) added by this request, used to revert on failure.
    requested_bitmask: u8,
}

/// A metadata sector write in flight, carrying every header update that was
/// queued for the sector when it started.
///
/// A sector holds the headers of 508 consecutive stripes, so stripes fetched
/// close together nearly always share one. Writing them one header at a time
/// would cost a write and an fsync each; one sector write covers them all for
/// the price of one.
struct SectorUpdateStatus {
    buffer: SharedBuffer,
    stage: RequestStage,
    group: usize,
    updates: Vec<HeaderUpdate>,
}

pub struct MetadataFlusher {
    channel: Box<dyn IoChannel>,
    metadata: Box<UbiMetadata>,
    shared_state: SharedMetadataState,
    sector_updates: HashMap<u64, SectorUpdateStatus>,
    queued_requests: VecDeque<MetadataFlusherRequest>,
    buffer_pool: AlignedBufferPool,
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
            sector_updates: HashMap::new(),
            queued_requests: VecDeque::new(),
            buffer_pool: AlignedBufferPool::new(4096, MAX_CONCURRENT_CHANGES, SECTOR_SIZE),
        })
    }

    pub fn busy(&self) -> bool {
        !self.sector_updates.is_empty() || !self.queued_requests.is_empty()
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
        self.start_writes();
        self.poll_channel();
    }

    fn cleanup_failed_submission(&mut self, sectors: &[u64], return_buffer: bool) {
        for sector in sectors {
            if let Some(status) = self.sector_updates.remove(sector) {
                for update in &status.updates {
                    self.metadata.stripe_headers[update.stripe_id] &= !update.requested_bitmask;
                }
                if return_buffer {
                    self.buffer_pool.return_buffer(&status.buffer);
                }
            }
        }
    }

    fn poll_channel(&mut self) {
        let mut finished_sectors = Vec::new();
        let mut newly_flushing = Vec::new();

        for (id, success) in self.channel.poll() {
            let sector = id as u64;
            let Some(status) = self.sector_updates.get_mut(&sector) else {
                error!("Received unexpected response for metadata sector {sector}");
                continue;
            };

            if !success {
                error!("Failed to write metadata sector {sector}");
                // Revert only the specific flag bits we added, so a future
                // retry for the same operations won't be skipped by the
                // dedup check in start_writes.
                for update in &status.updates {
                    self.metadata.stripe_headers[update.stripe_id] &= !update.requested_bitmask;
                }
                // Only return the buffer if it hasn't already been returned.
                // On write success the buffer is returned before transitioning
                // to Flushing, so a subsequent flush failure must not return
                // it a second time.
                if status.stage == RequestStage::Writing {
                    self.buffer_pool.return_buffer(&status.buffer);
                }
                self.sector_updates.remove(&sector);
                continue;
            }

            match status.stage {
                RequestStage::Writing => {
                    self.buffer_pool.return_buffer(&status.buffer);
                    self.channel.add_flush(id);
                    status.stage = RequestStage::Flushing;
                    newly_flushing.push(sector);
                }
                RequestStage::Flushing => {
                    finished_sectors.push(sector);
                }
            }
        }

        for sector in finished_sectors {
            if let Some(status) = self.sector_updates.remove(&sector) {
                for update in status.updates {
                    debug!(
                        "Stripe {} metadata updated with header {}",
                        update.stripe_id, update.header
                    );
                    self.shared_state
                        .set_stripe_header(update.stripe_id, update.header);
                }
            }
        }

        if newly_flushing.is_empty() {
            return;
        }

        // submit flushes, if any
        if let Err(e) = self.channel.submit() {
            error!("Failed to submit metadata flushes: {e}");
            // The kernel never received the flush SQEs. Clean up entries
            // that just transitioned to Flushing to avoid permanently
            // blocking the affected sectors.
            self.cleanup_failed_submission(&newly_flushing, false);
        }
    }

    fn start_writes(&mut self) {
        let mut newly_added: Vec<u64> = Vec::new();
        let mut deferred = VecDeque::new();

        while let Some(req) = self.queued_requests.pop_front() {
            let sector = UbiMetadata::stripe_id_to_sector(req.stripe_id);

            // Updates to each sector are serialized: a request for a sector
            // whose write is already in flight waits for the next round.
            // It is looked at again once that write has completed, so it is
            // dropped if the write made it redundant and retried if the
            // write failed. Requests for other sectors are not held up.
            if self.sector_updates.contains_key(&sector) && !newly_added.contains(&sector) {
                deferred.push_back(req);
                continue;
            }

            let requested_bitmask = match req.kind {
                MetadataFlusherRequestKind::SetFetched => metadata_flags::FETCHED,
                MetadataFlusherRequestKind::SetWritten => metadata_flags::WRITTEN,
            };

            if self.metadata.stripe_headers[req.stripe_id] & requested_bitmask != 0 {
                // Already set, skip
                continue;
            }

            let status = match self.sector_updates.entry(sector) {
                Entry::Occupied(entry) => entry.into_mut(),
                Entry::Vacant(entry) => {
                    let Some(buffer) = self.buffer_pool.get_buffer() else {
                        deferred.push_back(req);
                        continue;
                    };
                    newly_added.push(sector);
                    entry.insert(SectorUpdateStatus {
                        buffer,
                        stage: RequestStage::Writing,
                        group: UbiMetadata::stripe_id_to_group(req.stripe_id),
                        updates: Vec::new(),
                    })
                }
            };

            self.metadata.stripe_headers[req.stripe_id] |= requested_bitmask;
            status.updates.push(HeaderUpdate {
                stripe_id: req.stripe_id,
                header: self.metadata.stripe_headers[req.stripe_id],
                requested_bitmask,
            });
        }
        self.queued_requests = deferred;

        if newly_added.is_empty() {
            return;
        }

        // Every request for a sector has been applied to the in-memory
        // headers, so one write of the sector carries all of them.
        for sector in &newly_added {
            let Some(status) = self.sector_updates.get(sector) else {
                continue;
            };
            let headers_start = status.group * STRIPE_HEADERS_PER_SECTOR;
            let headers_end =
                (headers_start + STRIPE_HEADERS_PER_SECTOR).min(self.metadata.stripe_headers.len());
            let headers = &self.metadata.stripe_headers[headers_start..headers_end];
            write_sector_with_crc32(status.buffer.borrow_mut().as_mut_slice(), headers);

            self.channel
                .add_write(*sector, 1, status.buffer.clone(), *sector as usize);
        }

        // submit writes, if any
        if let Err(e) = self.channel.submit() {
            error!("Failed to submit metadata writes: {e}");
            // The kernel never received the SQEs, so no completions will
            // arrive. Revert all entries we just added to avoid permanently
            // blocking the affected sectors.
            self.cleanup_failed_submission(&newly_added, true);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::block_device::bdev_test::TestBlockDevice;

    use super::*;

    fn init_metadata_device() -> TestBlockDevice {
        init_metadata_device_with_stripes(16)
    }

    fn init_metadata_device_with_stripes(stripe_count: usize) -> TestBlockDevice {
        let metadata = UbiMetadata::new(11, stripe_count, stripe_count);
        let block_device = TestBlockDevice::new(64 * 1024);
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

        // Every request was for one stripe in one sector, so one write and
        // one flush carried all of them.
        let metrics = metadata_dev.metrics.read().unwrap();
        assert_eq!(metrics.writes - start_writes, 1);
        assert_eq!(metrics.flushes - start_flushes, 1);
    }

    #[test]
    fn test_submit_failure_in_start_writes_allows_retry() {
        let metadata_dev = init_metadata_device();
        let shared_state = {
            let metadata = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
            SharedMetadataState::new(&metadata)
        };
        let mut metadata_flusher =
            MetadataFlusher::new(&metadata_dev, 8 * 1024, shared_state.clone()).unwrap();

        // Queue a request and make submit() fail
        metadata_flusher.set_stripe_fetched(5);
        metadata_dev
            .fail_submit
            .store(true, std::sync::atomic::Ordering::SeqCst);

        // start_writes will add_write then fail on submit
        metadata_flusher.update();

        // Stripe 5 should NOT be marked fetched in shared state
        assert!(!shared_state.stripe_fetched(5));
        // Flusher should not be busy (submit failure was cleaned up)
        assert!(!metadata_flusher.busy());

        // Retry: queue the same request again - should NOT be blocked
        metadata_flusher.set_stripe_fetched(5);
        wait_for_completion(&mut metadata_flusher);

        // Now it should succeed
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
    fn test_submit_failure_in_poll_channel_allows_retry() {
        let metadata_dev = init_metadata_device();
        let shared_state = {
            let metadata = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
            SharedMetadataState::new(&metadata)
        };
        let mut metadata_flusher =
            MetadataFlusher::new(&metadata_dev, 8 * 1024, shared_state.clone()).unwrap();

        // Queue a request and let the write succeed
        metadata_flusher.set_stripe_fetched(5);
        metadata_flusher.start_writes();

        // Poll should see the write completion and enqueue a flush.
        // Make submit fail so the flush SQE is never submitted.
        metadata_dev
            .fail_submit
            .store(true, std::sync::atomic::Ordering::SeqCst);
        metadata_flusher.poll_channel();

        // Stripe 5 should NOT be marked fetched (flush never reached kernel)
        assert!(!shared_state.stripe_fetched(5));
        // Flusher should not be busy (submit failure was cleaned up)
        assert!(!metadata_flusher.busy());

        // Retry: queue the same request again - should NOT be blocked
        metadata_flusher.set_stripe_fetched(5);
        wait_for_completion(&mut metadata_flusher);

        // Now it should succeed
        assert!(shared_state.stripe_fetched(5));
    }

    #[test]
    fn test_same_sector_updates_share_one_write_and_flush() {
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

        // Stripes 0-7 are in sector 1. Queued together, they go out as one
        // sector write and one flush rather than one of each per stripe.
        for stripe_id in 0..8 {
            metadata_flusher.set_stripe_fetched(stripe_id);
        }
        metadata_flusher.set_stripe_written(3);

        wait_for_completion(&mut metadata_flusher);

        for stripe_id in 0..8 {
            assert!(shared_state.stripe_fetched(stripe_id));
        }
        assert!(shared_state.stripe_written(3));
        assert!(!shared_state.stripe_written(4));

        let metrics = metadata_dev.metrics.read().unwrap();
        assert_eq!(metrics.writes - start_writes, 1);
        assert_eq!(metrics.flushes - start_flushes, 1);
    }

    #[test]
    fn test_requests_behind_a_busy_sector_share_its_next_write() {
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

        // Start a write for sector 1 and leave it in flight.
        metadata_flusher.set_stripe_fetched(0);
        metadata_flusher.start_writes();
        assert_eq!(
            metadata_dev.metrics.read().unwrap().writes - start_writes,
            1
        );

        // Requests for the same sector that arrive meanwhile wait for it...
        for stripe_id in 1..4 {
            metadata_flusher.set_stripe_fetched(stripe_id);
        }
        metadata_flusher.start_writes();
        assert_eq!(
            metadata_dev.metrics.read().unwrap().writes - start_writes,
            1
        );
        assert_eq!(metadata_flusher.queued_requests.len(), 3);

        // ...and then all share the next write.
        wait_for_completion(&mut metadata_flusher);
        for stripe_id in 0..4 {
            assert!(shared_state.stripe_fetched(stripe_id));
        }
        let metrics = metadata_dev.metrics.read().unwrap();
        assert_eq!(metrics.writes - start_writes, 2);
        assert_eq!(metrics.flushes - start_flushes, 2);
    }

    #[test]
    fn test_busy_sector_does_not_hold_up_other_sectors() {
        // 1024 stripes span three header sectors: stripe 0 is in sector 1,
        // stripe 600 in sector 2.
        let metadata_dev = init_metadata_device_with_stripes(1024);
        let shared_state = {
            let metadata = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
            SharedMetadataState::new(&metadata)
        };
        let mut metadata_flusher =
            MetadataFlusher::new(&metadata_dev, 8 * 1024, shared_state.clone()).unwrap();
        let start_writes = metadata_dev.metrics.read().unwrap().writes;

        metadata_flusher.set_stripe_fetched(0);
        metadata_flusher.start_writes();
        assert_eq!(
            metadata_dev.metrics.read().unwrap().writes - start_writes,
            1
        );

        // Stripe 1 shares the in-flight sector and has to wait; stripe 600
        // does not and must not be held up behind it.
        metadata_flusher.set_stripe_fetched(1);
        metadata_flusher.set_stripe_fetched(600);
        metadata_flusher.start_writes();
        assert_eq!(
            metadata_dev.metrics.read().unwrap().writes - start_writes,
            2
        );
        assert_eq!(metadata_flusher.queued_requests.len(), 1);
        assert_eq!(metadata_flusher.queued_requests[0].stripe_id, 1);

        wait_for_completion(&mut metadata_flusher);
        for stripe_id in [0, 1, 600] {
            assert!(shared_state.stripe_fetched(stripe_id));
        }
        assert_eq!(
            metadata_dev.metrics.read().unwrap().writes - start_writes,
            3
        );
    }

    #[test]
    fn test_write_failure_reverts_every_stripe_in_the_sector() {
        let metadata_dev = init_metadata_device();
        let shared_state = {
            let metadata = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
            SharedMetadataState::new(&metadata)
        };
        let mut metadata_flusher =
            MetadataFlusher::new(&metadata_dev, 8 * 1024, shared_state.clone()).unwrap();

        // Two stripes share one failing sector write.
        metadata_flusher.set_stripe_fetched(1);
        metadata_flusher.set_stripe_written(2);
        metadata_dev
            .fail_next
            .store(true, std::sync::atomic::Ordering::SeqCst);
        metadata_flusher.update();

        assert!(!shared_state.stripe_fetched(1));
        assert!(!shared_state.stripe_written(2));
        assert!(!metadata_flusher.busy());

        // Neither bit was left set in memory, so both retries go through.
        metadata_flusher.set_stripe_fetched(1);
        metadata_flusher.set_stripe_written(2);
        wait_for_completion(&mut metadata_flusher);

        assert!(shared_state.stripe_fetched(1));
        assert!(shared_state.stripe_written(2));
    }
}
