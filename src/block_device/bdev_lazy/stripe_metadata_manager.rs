use std::{cell::RefCell, mem::MaybeUninit, ptr::copy_nonoverlapping, rc::Rc};

use super::super::*;
use crate::{vhost_backend::SECTOR_SIZE, Result, VhostUserBlockError};
use log::{debug, error, info};

#[repr(u8)]
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum StripeStatus {
    NotFetched,
    Queued,
    Fetching,
    Fetched,
}

const UBI_MAGIC_SIZE: usize = 9;
const UBI_MAX_STRIPES: usize = 2 * 1024 * 1024;
const UBI_MAGIC: &[u8] = b"BDEV_UBI\0"; // 9 bytes

const METADATA_WRITE_ID: usize = 0;
const METADATA_FLUSH_ID: usize = 1;

#[derive(Debug, Clone)]
pub struct StripeStatusVec {
    pub data: Vec<StripeStatus>,
    pub stripe_sector_count: u64,
    pub source_sector_count: u64,
    pub stripe_count: u64,
}

impl StripeStatusVec {
    pub fn sector_to_stripe_id(&self, sector: u64) -> usize {
        let stripe_id = (sector / self.stripe_sector_count) as usize;
        stripe_id
    }

    pub fn stripe_status(&self, stripe_id: usize) -> StripeStatus {
        if (stripe_id as u64) < self.stripe_count {
            self.data[stripe_id]
        } else {
            StripeStatus::Fetched
        }
    }

    pub fn set_stripe_status(&mut self, stripe_id: usize, status: StripeStatus) {
        self.data[stripe_id] = status;
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
        let sectors = (metadata_size + SECTOR_SIZE - 1) / SECTOR_SIZE;
        let buf = Rc::new(RefCell::new(vec![0u8; sectors * SECTOR_SIZE]));
        unsafe {
            let src = &*self as *const UbiMetadata as *const u8;
            let dst = buf.borrow_mut().as_mut_ptr();
            copy_nonoverlapping(src, dst, metadata_size);
        }
        ch.add_write(0, sectors as u32, buf.clone(), 0);
        ch.submit()?;

        let timeout = std::time::Duration::from_secs(5);
        let start_time = std::time::Instant::now();
        let mut completed = false;
        while start_time.elapsed() < timeout && !completed {
            std::thread::sleep(std::time::Duration::from_millis(1));
            for (id, success) in ch.poll() {
                if id == 0 {
                    if !success {
                        error!("Failed to write metadata");
                        return Err(VhostUserBlockError::IoError {
                            source: std::io::Error::new(
                                std::io::ErrorKind::Other,
                                "Failed to write metadata",
                            ),
                        });
                    }

                    completed = true;
                    break;
                } else {
                    error!("Unexpected ID: {}", id);
                    return Err(VhostUserBlockError::IoError {
                        source: std::io::Error::new(
                            std::io::ErrorKind::Other,
                            format!("Unexpected ID: {}", id),
                        ),
                    });
                }
            }
        }

        if !completed {
            error!("Timeout while writing metadata");
            return Err(VhostUserBlockError::IoError {
                source: std::io::Error::new(
                    std::io::ErrorKind::TimedOut,
                    "Timeout while writing metadata",
                ),
            });
        }
        info!("Metadata written successfully");

        Ok(())
    }
}

pub struct StripeMetadataManager {
    channel: Box<dyn IoChannel>,
    metadata: Box<UbiMetadata>,
    stripe_status_vec: StripeStatusVec,
    metadata_buf: SharedBuffer,
    metadata_version_current: u64,
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
        let stripe_status_vec = Self::create_stripe_status_vec(&metadata, source_sector_count);
        let metadata_size = std::mem::size_of::<UbiMetadata>();
        let metadata_buf_size = ((metadata_size + SECTOR_SIZE - 1) / SECTOR_SIZE) * SECTOR_SIZE;
        Ok(Box::new(StripeMetadataManager {
            channel,
            metadata,
            stripe_status_vec,
            metadata_buf: Rc::new(RefCell::new(vec![0u8; metadata_buf_size])),
            metadata_version_current: 0,
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
        self.metadata_version_current += 1;
        self.stripe_status_vec.set_stripe_status(stripe_id, status);
        match status {
            StripeStatus::NotFetched => {
                self.metadata.stripe_headers[stripe_id] = 0;
            }
            StripeStatus::Fetched => {
                self.metadata.stripe_headers[stripe_id] = 1;
            }
            _ => {}
        }
    }

    pub fn stripe_source_sector_offset(&self, stripe_id: usize) -> u64 {
        stripe_id as u64 * self.stripe_sector_count() as u64
    }

    pub fn stripe_target_sector_offset(&self, stripe_id: usize) -> u64 {
        stripe_id as u64 * self.stripe_sector_count() as u64
    }

    pub fn stripe_status_vec(&self) -> StripeStatusVec {
        self.stripe_status_vec.clone()
    }

    pub fn start_flush(&mut self) -> Result<StartFlushResult> {
        if self.metadata_version_flushed == self.metadata_version_current {
            debug!("No changes to flush");
            return Ok(StartFlushResult::NoChanges);
        }

        if self.metadata_version_being_flushed.is_some() {
            return Err(VhostUserBlockError::MetadataError {
                description: "Flush already in progress".to_string(),
            });
        }

        debug!(
            "Starting flush for metadata version {}",
            self.metadata_version_current
        );

        self.metadata_version_being_flushed = Some(self.metadata_version_current);

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
                        error!("Flush ID received without a pending flush");
                        return Some(false);
                    }
                    (Some(_), false) => {
                        error!("Metadata flush failed");
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

        let sector_count = (std::mem::size_of::<UbiMetadata>() + SECTOR_SIZE - 1) / SECTOR_SIZE;
        let buf: Rc<RefCell<Vec<u8>>> =
            Rc::new(RefCell::new(vec![0u8; sector_count * SECTOR_SIZE]));
        io_channel.add_read(0, sector_count as u32, buf.clone(), 0);
        io_channel.submit()?;

        let mut results = io_channel.poll();
        while io_channel.busy() {
            std::thread::sleep(std::time::Duration::from_millis(1));
            for result in io_channel.poll() {
                results.push(result);
            }
        }

        if results.len() != 1 {
            error!("Failed to read metadata");
            return Err(VhostUserBlockError::MetadataError {
                description: format!("Expected 1 result, got {}", results.len()),
            });
        }

        let (id, success) = results.pop().unwrap();
        if !success || id != 0 {
            error!("Failed to read metadata");
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
            error!("Metadata magic mismatch!");
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
        metadata: &Box<UbiMetadata>,
        source_sector_count: u64,
    ) -> StripeStatusVec {
        let v = metadata
            .stripe_headers
            .iter()
            .map(|header| {
                if *header == 0 {
                    StripeStatus::NotFetched
                } else {
                    StripeStatus::Fetched
                }
            })
            .collect::<Vec<StripeStatus>>();
        let stripe_sector_count = 1u64 << metadata.stripe_sector_count_shift;
        let stripe_count = (source_sector_count + stripe_sector_count - 1) / stripe_sector_count;

        StripeStatusVec {
            data: v,
            stripe_sector_count,
            source_sector_count,
            stripe_count,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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

        assert_eq!(metadata_dev.flushes(), 0);
        manager.start_flush().unwrap();
        assert_eq!(manager.poll_flush(), None);
        assert_eq!(manager.poll_flush(), Some(true));
        assert_eq!(metadata_dev.flushes(), 1);

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
        assert!(matches!(result, Err(VhostUserBlockError::MetadataError { .. })));

        Ok(())
    }
}
