use std::{cell::RefCell, ptr::copy_nonoverlapping, rc::Rc};

use super::super::*;
use crate::Result;
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
const UBI_MAGIC: &[u8] = b"BDEV_UBI\0"; // 9 bytes
const STRIPE_SIZE: usize = 1024 * 1024; // 1MB

const METADATA_WRITE_ID: usize = 0;
const METADATA_FLUSH_ID: usize = 1;

#[derive(Debug, Clone)]
pub struct StripeStatusVec {
    data: Vec<StripeStatus>,
    stripe_size: u64,
    device_size: u64,
    stripe_count: u64,
}

impl StripeStatusVec {
    pub fn sector_to_stripe_id(&self, sector: u64) -> usize {
        let stripe_id = (sector / (self.stripe_size / 512)) as usize;
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

    pub fn stripe_size(&self, stripe_id: usize) -> usize {
        self.stripe_size
            .min(self.device_size - (stripe_id as u64 * self.stripe_size)) as usize
    }

    pub fn translate_sector(&self, sector: u64) -> u64 {
        UBI_METADATA_SIZE as u64 / 512 + sector
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

pub struct StripeMetadataManger {
    channel: Box<dyn IoChannel>,
    metadata: Box<UbiMetadata>,
    stripe_status_vec: StripeStatusVec,
    metadata_buf: SharedBuffer,
}

impl StripeMetadataManger {
    pub fn new(source: &dyn BlockDevice, target: &dyn BlockDevice) -> Result<Self> {
        let mut channel = target.create_channel()?;
        let metadata = Self::load_metadata(&mut channel);
        let stripe_status_vec = Self::create_stripe_status_vec(&metadata, source.size());
        Ok(StripeMetadataManger {
            channel,
            metadata,
            stripe_status_vec,
            metadata_buf: Rc::new(RefCell::new(vec![0u8; UBI_METADATA_SIZE])),
        })
    }

    pub fn metadata_size(&self) -> usize {
        UBI_METADATA_SIZE
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
                self.metadata.stripe_headers[stripe_id] = [3, 0];
            }
            _ => {}
        }
    }

    pub fn stripe_source_offset(&self, stripe_id: usize) -> u64 {
        (stripe_id * STRIPE_SIZE) as u64
    }

    pub fn stripe_target_offset(&self, stripe_id: usize) -> u64 {
        (stripe_id * STRIPE_SIZE + UBI_METADATA_SIZE) as u64
    }

    pub fn stripe_size(&self, stripe_id: usize) -> usize {
        self.stripe_status_vec.stripe_size(stripe_id)
    }

    pub fn stripe_status_vec(&self) -> StripeStatusVec {
        self.stripe_status_vec.clone()
    }

    pub fn start_flush(&mut self) -> Result<()> {
        // copy metadata to metadata buffer
        let metadata_buf = self.metadata_buf.clone();
        let metadata_size = std::mem::size_of::<UbiMetadata>();
        unsafe {
            let src = &*self.metadata as *const UbiMetadata as *const u8;
            let dst = metadata_buf.borrow_mut().as_mut_ptr();
            copy_nonoverlapping(src, dst, metadata_size);
        }

        self.channel
            .add_write(0, metadata_buf, metadata_size, METADATA_WRITE_ID);

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

        io_channel.add_read(0, buf.clone(), UBI_METADATA_SIZE, 0);
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

        let mut metadata = Box::new(UbiMetadata {
            magic: [0; UBI_MAGIC_SIZE],
            version_major: [0; 2],
            version_minor: [0; 2],
            reserved: 0,
            stripe_headers: [[0; 2]; UBI_MAX_STRIPES],
        });

        unsafe {
            let src = buf.borrow().as_ptr();
            let dst = &mut *metadata as *mut UbiMetadata as *mut u8;
            copy_nonoverlapping(src, dst, std::mem::size_of::<UbiMetadata>());
        }

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

    fn create_stripe_status_vec(metadata: &Box<UbiMetadata>, device_size: u64) -> StripeStatusVec {
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
        let stripe_size = STRIPE_SIZE as u64;
        let stripe_count = (device_size + stripe_size - 1) / stripe_size;
        StripeStatusVec {
            data: v,
            stripe_size,
            device_size,
            stripe_count,
        }
    }
}
