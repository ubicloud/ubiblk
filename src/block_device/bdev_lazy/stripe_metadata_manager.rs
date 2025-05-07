use std::{cell::RefCell, mem::MaybeUninit, ptr::copy_nonoverlapping, rc::Rc};

use super::super::*;
use crate::{vhost_backend::SECTOR_SIZE, Result};
use log::{error, info};

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
const UBI_METADATA_SIZE: usize = 8388608; // 8MB
const UBI_METADATA_SECTOR_COUNT: u32 = (UBI_METADATA_SIZE / SECTOR_SIZE) as u32;
const UBI_MAGIC: &[u8] = b"BDEV_UBI\0"; // 9 bytes
const _STRIPE_SIZE: usize = 1024 * 1024; // 1MB
const STRIPE_SECTOR_COUNT: u32 = (_STRIPE_SIZE / SECTOR_SIZE) as u32;

const METADATA_WRITE_ID: usize = 0;
const METADATA_FLUSH_ID: usize = 1;

#[derive(Debug, Clone)]
pub struct StripeStatusVec {
    pub data: Vec<StripeStatus>,
    pub stripe_sector_count: u64,
    pub device_sector_count: u64,
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
            .min(self.device_sector_count - (stripe_id as u64 * self.stripe_sector_count))
            as usize;
        stripe_sector_count as u32
    }

    pub fn translate_sector(&self, sector: u64) -> u64 {
        UBI_METADATA_SECTOR_COUNT as u64 + sector
    }
}

#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct UbiMetadata {
    pub magic: [u8; UBI_MAGIC_SIZE],

    // Little-endian encoded u16 values as byte arrays
    pub version_major: [u8; 2],
    pub version_minor: [u8; 2],

    pub reserved: u8,

    // Each header is 2 bytes, 32 stripes
    pub stripe_headers: [[u8; 2]; UBI_MAX_STRIPES],
}

impl UbiMetadata {
    #[cfg(test)]
    pub fn stripe_headers_offset(&self, stripe_id: usize) -> usize {
        stripe_id * std::mem::size_of::<u16>() + UBI_MAGIC_SIZE + 5
    }
}

pub struct StripeMetadataManager {
    channel: Box<dyn IoChannel>,
    metadata: Box<UbiMetadata>,
    stripe_status_vec: StripeStatusVec,
    metadata_buf: SharedBuffer,
}

impl StripeMetadataManager {
    pub fn new(source: &dyn BlockDevice, target: &dyn BlockDevice) -> Result<Box<Self>> {
        let mut channel = target.create_channel()?;
        let metadata = Self::load_metadata(&mut channel);
        let stripe_status_vec = Self::create_stripe_status_vec(&metadata, source.sector_count());
        Ok(Box::new(StripeMetadataManager {
            channel,
            metadata,
            stripe_status_vec,
            metadata_buf: Rc::new(RefCell::new(vec![0u8; UBI_METADATA_SIZE])),
        }))
    }

    pub fn metadata_sector_count(&self) -> u64 {
        UBI_METADATA_SECTOR_COUNT as u64
    }

    pub fn stripe_status(&self, stripe_id: usize) -> StripeStatus {
        self.stripe_status_vec.stripe_status(stripe_id)
    }

    pub fn set_stripe_status(&mut self, stripe_id: usize, status: StripeStatus) {
        self.stripe_status_vec.set_stripe_status(stripe_id, status);
        match status {
            StripeStatus::NotFetched => {
                self.metadata.stripe_headers[stripe_id] = [0, 0];
            }
            StripeStatus::Fetched => {
                self.metadata.stripe_headers[stripe_id] = [1, 0];
            }
            _ => {}
        }
    }

    pub fn stripe_source_sector_offset(&self, stripe_id: usize) -> u64 {
        stripe_id as u64 * STRIPE_SECTOR_COUNT as u64
    }

    pub fn stripe_target_sector_offset(&self, stripe_id: usize) -> u64 {
        stripe_id as u64 * STRIPE_SECTOR_COUNT as u64 + UBI_METADATA_SECTOR_COUNT as u64
    }

    pub fn stripe_sector_count(&self, stripe_id: usize) -> u32 {
        self.stripe_status_vec.stripe_sector_count(stripe_id)
    }

    pub fn stripe_status_vec(&self) -> StripeStatusVec {
        self.stripe_status_vec.clone()
    }

    pub fn start_flush(&mut self) -> Result<()> {
        let metadata_buf = self.metadata_buf.clone();
        let metadata_size = std::mem::size_of::<UbiMetadata>();
        unsafe {
            let src = &*self.metadata as *const UbiMetadata as *const u8;
            let dst = metadata_buf.borrow_mut().as_mut_ptr();
            copy_nonoverlapping(src, dst, metadata_size);
        }

        self.channel.add_write(
            0,
            UBI_METADATA_SECTOR_COUNT,
            metadata_buf,
            METADATA_WRITE_ID,
        );

        self.channel.submit()?;

        Ok(())
    }

    pub fn poll_flush(&mut self) -> Option<bool> {
        for (id, success) in self.channel.poll() {
            if id == METADATA_WRITE_ID {
                if !success {
                    error!("Metadata write failed");
                    return Some(false);
                }

                self.channel.add_flush(METADATA_FLUSH_ID);
                if let Err(e) = self.channel.submit() {
                    error!("Failed to submit flush: {}", e);
                    return Some(false);
                }
                return None;
            } else if id == METADATA_FLUSH_ID {
                if !success {
                    error!("Metadata flush failed");
                    return Some(false);
                }

                return Some(true);
            }
        }
        None
    }

    fn load_metadata(io_channel: &mut Box<dyn IoChannel>) -> Box<UbiMetadata> {
        info!("Loading metadata from device");
        let buf: Rc<RefCell<Vec<u8>>> = Rc::new(RefCell::new(vec![0u8; UBI_METADATA_SIZE]));

        io_channel.add_read(0, UBI_METADATA_SECTOR_COUNT, buf.clone(), 0);
        io_channel.submit().unwrap();

        let mut results = io_channel.poll();
        while io_channel.busy() {
            std::thread::sleep(std::time::Duration::from_millis(1));
            for result in io_channel.poll() {
                results.push(result);
            }
        }

        if results.len() != 1 {
            panic!("Failed to read metadata");
        }

        let (id, success) = results.pop().unwrap();
        if !success || id != 0 {
            panic!("Failed to read metadata");
        }

        let mut metadata: Box<MaybeUninit<UbiMetadata>> = Box::new_uninit();

        unsafe {
            copy_nonoverlapping(
                buf.borrow().as_ptr(),
                metadata.as_mut_ptr() as *mut u8,
                std::mem::size_of::<UbiMetadata>(),
            );
        }

        let mut metadata: Box<UbiMetadata> = unsafe { metadata.assume_init() };

        if metadata.magic != *UBI_MAGIC {
            info!("Metadata magic mismatch, assuming new device");
            metadata.magic.copy_from_slice(UBI_MAGIC);
            metadata.version_major.copy_from_slice(&[0, 0]);
            metadata.version_minor.copy_from_slice(&[0, 0]);
            metadata.reserved = 0;
            metadata.stripe_headers = [[0; 2]; UBI_MAX_STRIPES];
        }

        info!("Metadata loaded successfully");

        metadata
    }

    fn create_stripe_status_vec(
        metadata: &Box<UbiMetadata>,
        device_sector_count: u64,
    ) -> StripeStatusVec {
        let v = metadata
            .stripe_headers
            .iter()
            .map(|header| {
                let stripe_id = u16::from_le_bytes(*header);
                if stripe_id == 0 {
                    StripeStatus::NotFetched
                } else {
                    StripeStatus::Fetched
                }
            })
            .collect::<Vec<StripeStatus>>();
        let stripe_sector_count = STRIPE_SECTOR_COUNT as u64;
        let stripe_count = (device_sector_count + stripe_sector_count - 1) / stripe_sector_count;
        StripeStatusVec {
            data: v,
            stripe_sector_count,
            device_sector_count,
            stripe_count,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block_device::bdev_test::TestBlockDevice;

    #[test]
    fn test_stripe_metadata_manager() -> Result<()> {
        let source = TestBlockDevice::new(29 * 1024 * 1024 + 3 * 1024);
        let target = TestBlockDevice::new(40 * 1024 * 1024);
        let mut manager = StripeMetadataManager::new(&source, &target)?;

        assert_eq!(
            manager.metadata_sector_count(),
            UBI_METADATA_SECTOR_COUNT as u64
        );
        assert_eq!(manager.stripe_status(0), StripeStatus::NotFetched);
        assert_eq!(manager.stripe_source_sector_offset(0), 0);
        assert_eq!(
            manager.stripe_target_sector_offset(0),
            UBI_METADATA_SECTOR_COUNT as u64
        );

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
        assert_eq!(stripe_status_vec.stripe_count, 30);

        for stripe_id in 0..30 {
            let expected_sector_count = if stripe_id == 29 {
                6
            } else {
                STRIPE_SECTOR_COUNT
            };
            assert_eq!(
                manager.stripe_sector_count(stripe_id),
                expected_sector_count
            );
        }

        assert_eq!(target.flushes(), 0);
        manager.start_flush().unwrap();
        assert_eq!(manager.poll_flush(), None);
        assert_eq!(manager.poll_flush(), Some(true));
        assert_eq!(target.flushes(), 1);

        for i in 0..UBI_MAX_STRIPES {
            let offset = manager.metadata.stripe_headers_offset(i);
            let mut header_buf = [0u8; 2];
            target.read(offset, &mut header_buf, 2);
            let expected_header = if stripes_to_fetch.contains(&i) {
                [1, 0]
            } else {
                [0, 0]
            };
            assert_eq!(header_buf, expected_header);
        }

        let mut magic_buf = [0u8; UBI_MAGIC_SIZE];
        target.read(0, &mut magic_buf, UBI_MAGIC_SIZE);
        assert_eq!(magic_buf, *UBI_MAGIC);

        Ok(())
    }
}
