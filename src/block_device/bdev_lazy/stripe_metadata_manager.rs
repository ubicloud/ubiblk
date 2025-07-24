use std::{
    cell::RefCell,
    mem::MaybeUninit,
    ptr::copy_nonoverlapping,
    rc::Rc,
    sync::{
        atomic::{AtomicU64, AtomicU8, Ordering},
        Arc,
    },
};

use super::super::*;
use crate::utils::aligned_buffer::AlignedBuf;
use crate::{vhost_backend::SECTOR_SIZE, Result, VhostUserBlockError};
use log::{debug, error, info};

#[repr(u8)]
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum StripeStatus {
    NotFetched,
    Queued,
    Fetching,
    Fetched,
    Failed,
}

const UBI_MAGIC_SIZE: usize = 9;
const UBI_MAX_STRIPES: usize = 2 * 1024 * 1024;
const UBI_MAGIC: &[u8] = b"BDEV_UBI\0"; // 9 bytes

const METADATA_WRITE_ID: usize = 0;
const METADATA_FLUSH_ID: usize = 1;

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
                other => panic!(
                    "Invalid stripe status value: {} for stripe_id: {}",
                    other, stripe_id
                ),
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
}

#[repr(C)]
#[derive(Debug, Clone)]
pub struct UbiMetadata {
    pub magic: [u8; UBI_MAGIC_SIZE],

    // Little-endian encoded u16 values as byte arrays
    pub version_major: [u8; 2],
    pub version_minor: [u8; 2],

    pub stripe_sector_count_shift: u8,

    // bit 0: fetched or not
    // bit 1: written or not
    pub stripe_headers: [u8; UBI_MAX_STRIPES],
}

impl UbiMetadata {
    #[cfg(test)]
    pub fn stripe_headers_offset(&self, stripe_id: usize) -> usize {
        stripe_id + UBI_MAGIC_SIZE + 5
    }

    pub fn new(stripe_sector_count_shift: u8) -> Box<Self> {
        let mut metadata: Box<MaybeUninit<Self>> = Box::new_uninit();
        unsafe {
            let metadata_ptr = metadata.assume_init_mut();
            metadata_ptr.magic.copy_from_slice(UBI_MAGIC);
            metadata_ptr.version_major.copy_from_slice(&[0, 0]);
            metadata_ptr.version_minor.copy_from_slice(&[0, 0]);
            metadata_ptr.stripe_sector_count_shift = stripe_sector_count_shift;
            metadata_ptr.stripe_headers.fill(0);
        }
        unsafe { metadata.assume_init() }
    }

    pub fn write(&self, ch: &mut Box<dyn IoChannel>) -> Result<()> {
        let metadata_size = std::mem::size_of::<UbiMetadata>();
        let sectors = metadata_size.div_ceil(SECTOR_SIZE);
        let buf = Rc::new(RefCell::new(AlignedBuf::new(sectors * SECTOR_SIZE)));

        unsafe {
            let src = self as *const UbiMetadata as *const u8;
            let dst = buf.borrow_mut().as_mut_ptr();
            copy_nonoverlapping(src, dst, metadata_size);
        }
        ch.add_write(0, sectors as u32, buf.clone(), METADATA_WRITE_ID);
        ch.submit()?;

        let timeout = std::time::Duration::from_secs(5);
        let start_time = std::time::Instant::now();
        let mut written = false;
        let mut flushed = false;
        while start_time.elapsed() < timeout && !flushed {
            std::thread::sleep(std::time::Duration::from_millis(1));
            if let Some((id, success)) = ch.poll().into_iter().next() {
                if id == METADATA_WRITE_ID {
                    if !success {
                        error!(
                            "Failed to write metadata after submitting {} sectors",
                            sectors
                        );
                        return Err(VhostUserBlockError::IoError {
                            source: std::io::Error::other("Failed to write metadata"),
                        });
                    } else if written {
                        error!("Write ID received multiple times");
                        return Err(VhostUserBlockError::IoError {
                            source: std::io::Error::other("Write ID received multiple times"),
                        });
                    }

                    info!("Metadata written successfully, flushing...");

                    ch.add_flush(METADATA_FLUSH_ID);
                    ch.submit()?;

                    written = true;
                } else if id == METADATA_FLUSH_ID {
                    if !success {
                        error!("Failed to flush metadata");
                        return Err(VhostUserBlockError::IoError {
                            source: std::io::Error::other("Failed to flush metadata"),
                        });
                    }
                    flushed = true;
                    info!("Metadata flushed successfully");
                } else {
                    error!("Unexpected completion ID: {}, expected 0", id);
                    return Err(VhostUserBlockError::IoError {
                        source: std::io::Error::other(format!("Unexpected ID: {}", id)),
                    });
                }
            }
        }

        if !written {
            error!(
                "Timeout while writing metadata after {} seconds",
                timeout.as_secs()
            );
            return Err(VhostUserBlockError::IoError {
                source: std::io::Error::new(
                    std::io::ErrorKind::TimedOut,
                    "Timeout while writing metadata",
                ),
            });
        }
        if !flushed {
            error!(
                "Timeout while flushing metadata after {} seconds",
                timeout.as_secs()
            );
            return Err(VhostUserBlockError::IoError {
                source: std::io::Error::new(
                    std::io::ErrorKind::TimedOut,
                    "Timeout while flushing metadata",
                ),
            });
        }

        Ok(())
    }
}

pub struct StripeMetadataManager {
    channel: Box<dyn IoChannel>,
    metadata: Box<UbiMetadata>,
    stripe_status_vec: StripeStatusVec,
    metadata_buf: SharedBuffer,
    metadata_version: Arc<AtomicU64>,
    metadata_version_flushed: u64,
    metadata_version_being_flushed: Option<u64>,
}

pub enum StartFlushResult {
    Started,
    NoChanges,
}

impl StripeMetadataManager {
    pub fn new(metadata_dev: &dyn BlockDevice, source_sector_count: u64) -> Result<Box<Self>> {
        let mut channel = metadata_dev.create_channel()?;
        let metadata = Self::load_metadata(&mut channel)?;
        let stripe_status_vec = Self::create_stripe_status_vec(&metadata, source_sector_count)?;
        let metadata_size = std::mem::size_of::<UbiMetadata>();
        let metadata_buf_size = metadata_size.div_ceil(SECTOR_SIZE) * SECTOR_SIZE;
        Ok(Box::new(StripeMetadataManager {
            channel,
            metadata,
            stripe_status_vec,
            metadata_buf: Rc::new(RefCell::new(AlignedBuf::new(metadata_buf_size))),
            metadata_version: Arc::new(AtomicU64::new(0)),
            metadata_version_flushed: 0,
            metadata_version_being_flushed: None,
        }))
    }

    pub fn stripe_sector_count(&self) -> u64 {
        1u64 << self.metadata.stripe_sector_count_shift
    }

    pub fn stripe_status(&self, stripe_id: usize) -> StripeStatus {
        self.stripe_status_vec.stripe_status(stripe_id)
    }

    pub fn set_stripe_status(&mut self, stripe_id: usize, status: StripeStatus) {
        let prev = self.stripe_status_vec.stripe_status(stripe_id);
        self.stripe_status_vec.set_stripe_status(stripe_id, status);
        match status {
            StripeStatus::NotFetched | StripeStatus::Failed => {
                self.metadata.stripe_headers[stripe_id] = 0;
            }
            StripeStatus::Fetched => {
                self.metadata.stripe_headers[stripe_id] = 1;
                if prev != StripeStatus::Fetched {
                    self.metadata_version.fetch_add(1, Ordering::SeqCst);
                }
            }
            _ => {}
        }
    }

    pub fn stripe_source_sector_offset(&self, stripe_id: usize) -> u64 {
        stripe_id as u64 * self.stripe_sector_count()
    }

    pub fn stripe_target_sector_offset(&self, stripe_id: usize) -> u64 {
        stripe_id as u64 * self.stripe_sector_count()
    }

    pub fn stripe_status_vec(&self) -> StripeStatusVec {
        self.stripe_status_vec.clone()
    }

    pub fn start_flush(&mut self) -> Result<StartFlushResult> {
        let current_version = self.metadata_version.load(Ordering::Acquire);
        if self.metadata_version_flushed == current_version {
            debug!("No changes to flush");
            return Ok(StartFlushResult::NoChanges);
        }

        if self.metadata_version_being_flushed.is_some() {
            return Err(VhostUserBlockError::MetadataError {
                description: "Flush already in progress".to_string(),
            });
        }

        debug!("Starting flush for metadata version {}", current_version);

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

        Ok(StartFlushResult::Started)
    }

    pub fn poll_flush(&mut self) -> Option<bool> {
        for (id, success) in self.channel.poll() {
            if id == METADATA_WRITE_ID {
                if !success {
                    error!("Metadata write failed");
                    self.metadata_version_being_flushed = None;
                    return Some(false);
                }

                self.channel.add_flush(METADATA_FLUSH_ID);
                if let Err(e) = self.channel.submit() {
                    error!("Failed to submit flush: {}", e);
                    self.metadata_version_being_flushed = None;
                    return Some(false);
                }
                return None;
            } else if id == METADATA_FLUSH_ID {
                match (self.metadata_version_being_flushed, success) {
                    (None, _) => {
                        error!("Flush completion received without a pending flush");
                        return Some(false);
                    }
                    (Some(version), false) => {
                        error!("Metadata flush for version {} failed", version);
                        self.metadata_version_being_flushed = None;
                        return Some(false);
                    }
                    (Some(version), true) => {
                        debug!("Metadata flush completed for version {}", version);
                        self.metadata_version_flushed = version;
                        self.metadata_version_being_flushed = None;
                        return Some(true);
                    }
                }
            }
        }
        None
    }

    fn load_metadata(io_channel: &mut Box<dyn IoChannel>) -> Result<Box<UbiMetadata>> {
        info!("Loading metadata from device");

        let sector_count = std::mem::size_of::<UbiMetadata>().div_ceil(SECTOR_SIZE);
        let buf: Rc<RefCell<AlignedBuf>> =
            Rc::new(RefCell::new(AlignedBuf::new(sector_count * SECTOR_SIZE)));
        io_channel.add_read(0, sector_count as u32, buf.clone(), 0);
        io_channel.submit()?;

        let mut results = io_channel.poll();
        while io_channel.busy() {
            std::thread::sleep(std::time::Duration::from_millis(1));
            results.extend(io_channel.poll());
        }

        if results.len() != 1 {
            error!(
                "Failed to read metadata: expected 1 result, got {}",
                results.len()
            );
            return Err(VhostUserBlockError::MetadataError {
                description: format!("Expected 1 result, got {}", results.len()),
            });
        }

        let (id, success) = results.pop().unwrap();
        if !success || id != 0 {
            error!("Failed to read metadata: id {}, success {}", id, success);
            return Err(VhostUserBlockError::MetadataError {
                description: format!("Failed to read metadata, id: {}, success: {}", id, success),
            });
        }

        let mut metadata: Box<MaybeUninit<UbiMetadata>> = Box::new_uninit();

        unsafe {
            copy_nonoverlapping(
                buf.borrow().as_ptr(),
                metadata.as_mut_ptr() as *mut u8,
                std::mem::size_of::<UbiMetadata>(),
            );
        }

        let metadata: Box<UbiMetadata> = unsafe { metadata.assume_init() };

        if metadata.magic != *UBI_MAGIC {
            error!(
                "Metadata magic mismatch: expected {:?}, found {:?}",
                UBI_MAGIC, metadata.magic
            );
            return Err(VhostUserBlockError::MetadataError {
                description: format!(
                    "Metadata magic mismatch! Expected: {:?}, Found: {:?}",
                    UBI_MAGIC, metadata.magic
                ),
            });
        }

        info!("Metadata loaded successfully");

        Ok(metadata)
    }

    fn create_stripe_status_vec(
        metadata: &UbiMetadata,
        source_sector_count: u64,
    ) -> Result<StripeStatusVec> {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block_device::bdev_failing::FailingBlockDevice;
    use crate::block_device::bdev_test::TestBlockDevice;
    use crate::VhostUserBlockError;

    #[test]
    fn test_stripe_metadata_manager() -> Result<()> {
        let metadata_dev = TestBlockDevice::new(40 * 1024 * 1024);
        let stripe_sector_count_shift = 11;
        let stripe_sector_count = 1 << stripe_sector_count_shift;
        let source_sector_count = 29 * stripe_sector_count + 4;
        let stripe_count = (source_sector_count + stripe_sector_count - 1) / stripe_sector_count;

        let mut ch = metadata_dev.create_channel()?;
        UbiMetadata::new(stripe_sector_count_shift)
            .write(&mut ch)
            .unwrap();

        let mut manager = StripeMetadataManager::new(&metadata_dev, source_sector_count)?;

        assert_eq!(manager.stripe_status(0), StripeStatus::NotFetched);
        assert_eq!(manager.stripe_source_sector_offset(0), 0);
        assert_eq!(manager.stripe_target_sector_offset(0), 0);

        let stripes_to_fetch = vec![0, 3, 7, 8];

        for stripe_id in stripes_to_fetch.iter() {
            assert_eq!(manager.stripe_status(*stripe_id), StripeStatus::NotFetched);

            manager.set_stripe_status(*stripe_id, StripeStatus::Queued);
            assert_eq!(manager.stripe_status(*stripe_id), StripeStatus::Queued);

            manager.set_stripe_status(*stripe_id, StripeStatus::Fetching);
            assert_eq!(manager.stripe_status(*stripe_id), StripeStatus::Fetching);

            manager.set_stripe_status(*stripe_id, StripeStatus::Fetched);
            assert_eq!(manager.stripe_status(*stripe_id), StripeStatus::Fetched);
        }

        let stripe_status_vec = manager.stripe_status_vec();
        assert_eq!(stripe_status_vec.stripe_count, stripe_count as u64);

        assert_eq!(metadata_dev.flushes(), 1);
        manager.start_flush().unwrap();
        assert_eq!(manager.poll_flush(), None);
        assert_eq!(manager.poll_flush(), Some(true));
        assert_eq!(metadata_dev.flushes(), 2);

        for i in 0..UBI_MAX_STRIPES {
            let offset = manager.metadata.stripe_headers_offset(i);
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
        let stripe_sector_count_shift = 11;
        let stripe_sector_count = 1 << stripe_sector_count_shift;
        let source_sector_count = 29 * stripe_sector_count + 4;

        let mut ch = metadata_dev.create_channel()?;
        UbiMetadata::new(stripe_sector_count_shift)
            .write(&mut ch)
            .unwrap();

        // Corrupt the magic bytes
        let bad_magic = [0u8; UBI_MAGIC_SIZE];
        metadata_dev.write(0, &bad_magic, UBI_MAGIC_SIZE);

        let result = StripeMetadataManager::new(&metadata_dev, source_sector_count);
        assert!(matches!(
            result,
            Err(VhostUserBlockError::MetadataError { .. })
        ));

        Ok(())
    }

    #[test]
    fn test_poll_flush_failed_write() -> Result<()> {
        let metadata_dev = FailingBlockDevice::new(40 * 1024 * 1024);
        let stripe_sector_count_shift = 11;
        let stripe_sector_count = 1 << stripe_sector_count_shift;
        let source_sector_count = 29 * stripe_sector_count + 4;

        {
            let mut ch = metadata_dev.create_channel()?;
            UbiMetadata::new(stripe_sector_count_shift)
                .write(&mut ch)
                .unwrap();
        }

        let mut manager = StripeMetadataManager::new(&metadata_dev, source_sector_count)?;

        metadata_dev.fail_next_write();

        manager.set_stripe_status(0, StripeStatus::Fetched);

        manager.start_flush().unwrap();
        assert_eq!(manager.poll_flush(), Some(false));

        Ok(())
    }

    #[test]
    fn test_poll_flush_failed_flush() -> Result<()> {
        let metadata_dev = FailingBlockDevice::new(40 * 1024 * 1024);
        let stripe_sector_count_shift = 11;
        let stripe_sector_count = 1 << stripe_sector_count_shift;
        let source_sector_count = 29 * stripe_sector_count + 4;

        {
            let mut ch = metadata_dev.create_channel()?;
            UbiMetadata::new(stripe_sector_count_shift)
                .write(&mut ch)
                .unwrap();
        }

        let mut manager = StripeMetadataManager::new(&metadata_dev, source_sector_count)?;

        manager.set_stripe_status(0, StripeStatus::Fetched);
        metadata_dev.fail_next_flush();

        manager.start_flush().unwrap();
        assert_eq!(manager.poll_flush(), None);
        assert_eq!(manager.poll_flush(), Some(false));

        Ok(())
    }

    #[test]
    fn test_stripe_count_overflow() -> Result<()> {
        let metadata_dev = TestBlockDevice::new(40 * 1024 * 1024);
        let stripe_sector_count_shift = 0u8;
        let stripe_sector_count = 1u64 << stripe_sector_count_shift;
        let source_sector_count = (UBI_MAX_STRIPES as u64 + 1) * stripe_sector_count;

        let mut ch = metadata_dev.create_channel()?;
        UbiMetadata::new(stripe_sector_count_shift)
            .write(&mut ch)
            .unwrap();

        let result = StripeMetadataManager::new(&metadata_dev, source_sector_count);
        assert!(matches!(
            result,
            Err(VhostUserBlockError::InvalidParameter { .. })
        ));

        Ok(())
    }
}
