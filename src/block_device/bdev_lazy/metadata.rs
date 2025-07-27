use std::{
    cell::RefCell,
    mem::MaybeUninit,
    rc::Rc,
    sync::atomic::{AtomicU8, Ordering},
    sync::Arc,
};

use super::super::*;
use crate::utils::aligned_buffer::AlignedBuf;
use crate::{vhost_backend::SECTOR_SIZE, Result};
use log::error;

use super::metadata_flush::MetadataFlusher;

#[repr(u8)]
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum StripeStatus {
    NotFetched,
    Queued,
    Fetching,
    Fetched,
    Failed,
}

pub const UBI_MAGIC_SIZE: usize = 9;
pub const UBI_MAX_STRIPES: usize = 2 * 1024 * 1024;
pub const UBI_MAGIC: &[u8] = b"BDEV_UBI\0"; // 9 bytes

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
                other => {
                    error!(
                        "Invalid stripe status value: {} for stripe_id: {}. Defaulting to Failed.",
                        other, stripe_id
                    );
                    StripeStatus::Failed
                }
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
}

pub struct MetadataManager {
    pub(super) channel: Box<dyn IoChannel>,
    pub(crate) metadata: Box<UbiMetadata>,
    pub(super) stripe_status_vec: StripeStatusVec,
    pub(super) metadata_buf: SharedBuffer,
    pub(super) flush_state: MetadataFlusher,
    pub(super) metadata_version_being_flushed: Option<u64>,
}

pub enum StartFlushResult {
    Started,
    NoChanges,
}

impl MetadataManager {
    pub fn new(metadata_dev: &dyn BlockDevice, source_sector_count: u64) -> Result<Box<Self>> {
        let mut channel = metadata_dev.create_channel()?;
        let metadata = Self::load_metadata(&mut channel)?;
        let stripe_status_vec = Self::create_stripe_status_vec(&metadata, source_sector_count)?;
        let metadata_size = std::mem::size_of::<UbiMetadata>();
        let metadata_buf_size = metadata_size.div_ceil(SECTOR_SIZE) * SECTOR_SIZE;
        Ok(Box::new(MetadataManager {
            channel,
            metadata,
            stripe_status_vec,
            metadata_buf: Rc::new(RefCell::new(AlignedBuf::new(metadata_buf_size))),
            flush_state: MetadataFlusher::new(),
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
                    self.flush_state.increment_version();
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
}
