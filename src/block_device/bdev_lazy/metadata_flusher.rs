#[cfg(test)]
use crate::block_device::bdev_lazy::metadata::UBI_MAX_STRIPES;
use crate::{
    block_device::{
        bdev_lazy::metadata::load_metadata, BlockDevice, IoChannel, SharedBuffer, UbiMetadata,
    },
    utils::aligned_buffer::AlignedBuf,
    vhost_backend::SECTOR_SIZE,
    Result,
};
use log::{debug, error};
use std::{
    cell::RefCell,
    ptr::copy_nonoverlapping,
    rc::Rc,
    sync::{
        atomic::{AtomicU64, Ordering},
        Arc,
    },
};

const METADATA_WRITE_ID: usize = 0;
const METADATA_FLUSH_ID: usize = 1;

#[derive(Debug, Clone)]
pub struct MetadataFlushState {
    metadata_version: Arc<AtomicU64>,
    metadata_version_flushed: Arc<AtomicU64>,
}

impl MetadataFlushState {
    pub fn new() -> Self {
        Self {
            metadata_version: Arc::new(AtomicU64::new(1)),
            metadata_version_flushed: Arc::new(AtomicU64::new(0)),
        }
    }

    pub fn increment_version(&self) {
        self.metadata_version.fetch_add(1, Ordering::SeqCst);
    }

    pub fn set_flushed_version(&self, version: u64) {
        self.metadata_version_flushed
            .store(version, Ordering::Release);
    }

    pub fn flushed_version(&self) -> u64 {
        self.metadata_version_flushed.load(Ordering::Acquire)
    }

    pub fn current_version(&self) -> u64 {
        self.metadata_version.load(Ordering::Acquire)
    }

    pub fn needs_flush(&self) -> bool {
        let flushed = self.metadata_version_flushed.load(Ordering::Acquire);
        let current = self.metadata_version.load(Ordering::Acquire);
        current > flushed
    }
}

impl Default for MetadataFlushState {
    fn default() -> Self {
        Self::new()
    }
}

pub struct MetadataFlusher {
    channel: Box<dyn IoChannel>,
    metadata: Box<UbiMetadata>,
    metadata_buf: SharedBuffer,
    flush_state: MetadataFlushState,
    metadata_version_being_flushed: Option<u64>,
    pending_flush_requests: bool,
    inprogress_flush_requests: bool,
}

impl MetadataFlusher {
    pub fn new(metadata_dev: &dyn BlockDevice) -> Result<Self> {
        let mut channel = metadata_dev.create_channel()?;
        let metadata = load_metadata(&mut channel)?;
        let metadata_size = std::mem::size_of::<UbiMetadata>();
        let metadata_buf_size = metadata_size.div_ceil(SECTOR_SIZE) * SECTOR_SIZE;
        Ok(MetadataFlusher {
            channel,
            metadata,
            metadata_buf: Rc::new(RefCell::new(AlignedBuf::new(metadata_buf_size))),
            flush_state: MetadataFlushState::new(),
            metadata_version_being_flushed: None,
            pending_flush_requests: false,
            inprogress_flush_requests: false,
        })
    }

    pub fn busy(&self) -> bool {
        self.inprogress_flush_requests || self.pending_flush_requests
    }

    pub fn stripe_sector_count(&self) -> u64 {
        1u64 << self.metadata.stripe_sector_count_shift
    }

    pub fn metadata(&self) -> &UbiMetadata {
        &self.metadata
    }

    pub fn set_stripe_fetched(&mut self, stripe_id: usize) {
        self.metadata.stripe_headers[stripe_id] = 1;
        self.flush_state.increment_version();
    }

    fn start_flush(&mut self) -> Result<()> {
        let current_version = self.flush_state.current_version();
        debug!("Starting flush for metadata version {current_version}");
        self.metadata_version_being_flushed = Some(current_version);

        let metadata_buf = self.metadata_buf.clone();
        let metadata_size = std::mem::size_of::<UbiMetadata>();
        unsafe {
            let src = &*self.metadata as *const UbiMetadata as *const u8;
            let dst = metadata_buf.borrow_mut().as_mut_ptr();
            copy_nonoverlapping(src, dst, metadata_size);
        }

        let sector_count = metadata_buf.borrow().len() / SECTOR_SIZE;
        self.channel
            .add_write(0, sector_count as u32, metadata_buf, METADATA_WRITE_ID);
        self.channel.submit()?;
        Ok(())
    }

    fn poll(&mut self) -> Option<bool> {
        for (id, success) in self.channel.poll() {
            if id == METADATA_WRITE_ID {
                if !success {
                    error!("Metadata write failed");
                    return Some(false);
                }
                self.channel.add_flush(METADATA_FLUSH_ID);
                if let Err(e) = self.channel.submit() {
                    error!("Failed to submit flush: {e}");
                    return Some(false);
                }
                return None;
            } else if id == METADATA_FLUSH_ID {
                return Some(success);
            } else {
                error!("Unexpected ID {id} in poll result");
            }
        }
        None
    }

    fn finish_flush(&mut self, success: bool) {
        match (self.metadata_version_being_flushed, success) {
            (None, _) => {
                error!("Flush completion received without a pending flush");
            }
            (Some(version), false) => {
                error!("Metadata flush for version {version} failed");
            }
            (Some(version), true) => {
                debug!("Metadata flush completed for version {version}");
                self.flush_state.set_flushed_version(version);
            }
        }
        self.inprogress_flush_requests = false;
        self.metadata_version_being_flushed = None;
    }

    pub fn request_flush(&mut self) {
        self.pending_flush_requests = true;
    }

    pub fn shared_flush_state(&self) -> MetadataFlushState {
        self.flush_state.clone()
    }

    pub fn update(&mut self) {
        if let Some(success) = self.poll() {
            self.finish_flush(success);
        }

        if self.pending_flush_requests && !self.inprogress_flush_requests {
            self.inprogress_flush_requests = true;
            self.pending_flush_requests = false;
            match self.start_flush() {
                Ok(()) => {
                    debug!("Flush request started successfully");
                }
                Err(e) => {
                    error!("Failed to start flush: {e:?}");
                    self.finish_flush(false);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block_device::bdev_failing::FailingBlockDevice;
    use crate::block_device::bdev_lazy::init_metadata;
    use crate::block_device::bdev_lazy::metadata::{UBI_MAGIC, UBI_MAGIC_SIZE};
    use crate::block_device::bdev_lazy::stripe_fetcher::{StripeStatus, StripeStatusVec};
    use crate::block_device::bdev_test::TestBlockDevice;
    use crate::Result;
    use crate::VhostUserBlockError;

    #[test]
    fn test_metadata_flusher() -> Result<()> {
        let metadata_dev = TestBlockDevice::new(40 * 1024 * 1024);
        let stripe_sector_count_shift = 11;
        let stripe_sector_count: u64 = 1 << stripe_sector_count_shift;
        let source_sector_count = 29 * stripe_sector_count + 4;
        let stripe_count = source_sector_count.div_ceil(stripe_sector_count);

        let mut ch = metadata_dev.create_channel()?;
        let metadata = UbiMetadata::new(stripe_sector_count_shift);
        init_metadata(&metadata, &mut ch).unwrap();

        let mut flusher = MetadataFlusher::new(&metadata_dev)?;
        let stripe_status_vec = StripeStatusVec::new(flusher.metadata(), source_sector_count)?;

        assert_eq!(stripe_status_vec.stripe_status(0), StripeStatus::NotFetched);
        assert_eq!(flusher.stripe_sector_count(), stripe_sector_count);

        let stripes_to_fetch = [0, 3, 7, 8];
        for stripe_id in stripes_to_fetch.iter() {
            assert_eq!(
                stripe_status_vec.stripe_status(*stripe_id),
                StripeStatus::NotFetched
            );
            stripe_status_vec.set_stripe_status(*stripe_id, StripeStatus::Queued);
            assert_eq!(
                stripe_status_vec.stripe_status(*stripe_id),
                StripeStatus::Queued
            );
            stripe_status_vec.set_stripe_status(*stripe_id, StripeStatus::Fetching);
            assert_eq!(
                stripe_status_vec.stripe_status(*stripe_id),
                StripeStatus::Fetching
            );
            stripe_status_vec.set_stripe_status(*stripe_id, StripeStatus::Fetched);
            flusher.set_stripe_fetched(*stripe_id);
            assert_eq!(
                stripe_status_vec.stripe_status(*stripe_id),
                StripeStatus::Fetched
            );
        }
        assert_eq!(stripe_status_vec.stripe_count, stripe_count);

        assert_eq!(metadata_dev.flushes(), 1);
        flusher.request_flush();
        flusher.update();
        assert!(!flusher.pending_flush_requests);
        while flusher.shared_flush_state().needs_flush() {
            flusher.update();
        }
        assert_eq!(metadata_dev.flushes(), 2);

        for i in 0..UBI_MAX_STRIPES {
            let offset = metadata.stripe_headers_offset(i);
            let mut header_buf = [0u8; 1];
            metadata_dev.read(offset, &mut header_buf, 1);
            let expected_header = if stripes_to_fetch.contains(&i) {
                [1]
            } else {
                [0]
            };
            assert_eq!(header_buf, expected_header);
        }

        let mut magic_buf = [0u8; UBI_MAGIC_SIZE];
        metadata_dev.read(0, &mut magic_buf, UBI_MAGIC_SIZE);
        assert_eq!(magic_buf, *UBI_MAGIC);
        Ok(())
    }

    #[test]
    fn test_metadata_magic_mismatch() -> Result<()> {
        let metadata_dev = TestBlockDevice::new(40 * 1024 * 1024);
        let stripe_shift = 11u8;

        let mut ch = metadata_dev.create_channel()?;
        let metadata = UbiMetadata::new(stripe_shift);
        init_metadata(&metadata, &mut ch).unwrap();
        let bad_magic = [0u8; UBI_MAGIC_SIZE];
        metadata_dev.write(0, &bad_magic, UBI_MAGIC_SIZE);

        let result = MetadataFlusher::new(&metadata_dev);
        assert!(matches!(
            result,
            Err(VhostUserBlockError::MetadataError { .. })
        ));
        Ok(())
    }

    #[test]
    fn test_poll_flush_failed_write() -> Result<()> {
        let metadata_dev = FailingBlockDevice::new(40 * 1024 * 1024);
        let stripe_shift = 11u8;
        let stripe_sector_count = 1 << stripe_shift;
        let source_sector_count = 29 * stripe_sector_count + 4;

        {
            let mut ch = metadata_dev.create_channel()?;
            let metadata = UbiMetadata::new(stripe_shift);
            init_metadata(&metadata, &mut ch).unwrap();
        }

        let mut flusher = MetadataFlusher::new(&metadata_dev)?;
        let stripe_status_vec = StripeStatusVec::new(flusher.metadata(), source_sector_count)?;
        metadata_dev.fail_next_write();
        stripe_status_vec.set_stripe_status(0, StripeStatus::Fetched);
        flusher.set_stripe_fetched(0);
        flusher.request_flush();
        flusher.update();
        assert!(!flusher.pending_flush_requests);
        assert!(flusher.shared_flush_state().needs_flush());
        Ok(())
    }

    #[test]
    fn test_poll_flush_failed_flush() -> Result<()> {
        let metadata_dev = FailingBlockDevice::new(40 * 1024 * 1024);
        let stripe_shift = 11u8;
        let stripe_sector_count = 1 << stripe_shift;
        let source_sector_count = 29 * stripe_sector_count + 4;

        {
            let mut ch = metadata_dev.create_channel()?;
            let metadata = UbiMetadata::new(stripe_shift);
            init_metadata(&metadata, &mut ch).unwrap();
        }

        let mut flusher = MetadataFlusher::new(&metadata_dev)?;
        let stripe_status_vec = StripeStatusVec::new(flusher.metadata(), source_sector_count)?;
        stripe_status_vec.set_stripe_status(0, StripeStatus::Fetched);
        flusher.set_stripe_fetched(0);
        metadata_dev.fail_next_flush();
        flusher.request_flush();
        flusher.update();
        flusher.update();
        assert!(flusher.shared_flush_state().needs_flush());
        Ok(())
    }

    #[test]
    fn test_stripe_count_overflow() -> Result<()> {
        let metadata_dev = TestBlockDevice::new(40 * 1024 * 1024);
        let stripe_shift = 0u8;
        let stripe_sector_count = 1u64 << stripe_shift;
        let source_sector_count = (UBI_MAX_STRIPES as u64 + 1) * stripe_sector_count;

        let mut ch = metadata_dev.create_channel()?;
        let metadata = UbiMetadata::new(stripe_shift);
        init_metadata(&metadata, &mut ch).unwrap();

        let flusher = MetadataFlusher::new(&metadata_dev)?;
        let result = StripeStatusVec::new(flusher.metadata(), source_sector_count);
        assert!(matches!(
            result,
            Err(VhostUserBlockError::InvalidParameter { .. })
        ));
        Ok(())
    }
}
