use crate::{
    block_device::{
        BlockDevice, IoChannel, SharedMetadataState, UbiMetadata, METADATA_STRIPE_FETCHED_BITMASK,
        METADATA_STRIPE_WRITTEN_BITMASK,
    },
    utils::AlignedBufferPool,
    vhost_backend::SECTOR_SIZE,
    Result, UbiblkError,
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
    buffer_index: usize,
    stage: RequestStage,
    stripe_id: usize,
    header: u8,
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
            return Err(UbiblkError::InvalidParameter {
                description: format!(
                    "Source stripe count {} exceeds metadata stripe count {}",
                    source_stripe_count,
                    metadata.stripe_count()
                ),
            });
        }

        Ok(MetadataFlusher {
            channel,
            shared_state,
            metadata,
            sectors_being_updated: HashSet::new(),
            queued_requests: VecDeque::new(),
            buffer_pool: AlignedBufferPool::new(4096, MAX_CONCURRENT_CHANGES, SECTOR_SIZE),
            header_updates: HashMap::new(),
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
        self.start_writes();
        self.poll_channel();
    }

    fn poll_channel(&mut self) {
        let mut finished_stripes = Vec::new();

        for (stripe_id, success) in self.channel.poll() {
            let maybe_status = self.header_updates.get_mut(&stripe_id);
            match (maybe_status, success) {
                (None, _) => {
                    error!("Received unexpected response for stripe {stripe_id}");
                }
                (Some(status), false) => {
                    error!("Failed to write metadata for stripe {stripe_id}");
                    self.buffer_pool.return_buffer(status.buffer_index);
                    self.sectors_being_updated.remove(&status.sector);
                    self.header_updates.remove(&stripe_id);
                }
                (Some(status), true) => match status.stage {
                    RequestStage::Writing => {
                        self.buffer_pool.return_buffer(status.buffer_index);
                        self.channel.add_flush(stripe_id);
                        status.stage = RequestStage::Flushing;
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

        // submit flushes, if any
        if let Err(e) = self.channel.submit() {
            error!("Failed to submit metadata writes: {e}");
        }
    }

    fn start_writes(&mut self) {
        while !self.queued_requests.is_empty() && self.buffer_pool.has_available() {
            let req = *self.queued_requests.front().unwrap();
            let group = req.stripe_id / SECTOR_SIZE;
            let sector = (group + 1) as u64;
            if self.sectors_being_updated.contains(&sector) {
                // Updates to each sector should be serialized
                break;
            }
            self.queued_requests.pop_front();

            let requested_bitmask = match req.kind {
                MetadataFlusherRequestKind::SetFetched => METADATA_STRIPE_FETCHED_BITMASK,
                MetadataFlusherRequestKind::SetWritten => METADATA_STRIPE_WRITTEN_BITMASK,
            };

            if self.metadata.stripe_headers[req.stripe_id] & requested_bitmask != 0 {
                // Already set, skip
                continue;
            }

            let (buf, index) = self.buffer_pool.get_buffer().unwrap();
            self.metadata.stripe_headers[req.stripe_id] |= requested_bitmask;
            buf.borrow_mut().as_mut_slice().copy_from_slice(
                &self.metadata.stripe_headers[group * SECTOR_SIZE..(group + 1) * SECTOR_SIZE],
            );

            self.channel.add_write(sector, 1, buf, req.stripe_id);
            self.sectors_being_updated.insert(sector);
            self.header_updates.insert(
                req.stripe_id,
                HeaderUpdateStatus {
                    buffer_index: index,
                    stage: RequestStage::Writing,
                    stripe_id: req.stripe_id,
                    header: self.metadata.stripe_headers[req.stripe_id],
                    sector,
                },
            );
        }

        // submit writes, if any
        if let Err(e) = self.channel.submit() {
            error!("Failed to submit metadata writes: {e}");
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
}
