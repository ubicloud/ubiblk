use crate::utils::aligned_buffer::AlignedBuf;
use crate::Result;
use std::{cell::RefCell, rc::Rc};

pub type SharedBuffer = Rc<RefCell<AlignedBuf>>;

pub fn shared_buffer(size: usize) -> SharedBuffer {
    Rc::new(RefCell::new(AlignedBuf::new(size)))
}

pub trait IoChannel {
    fn add_read(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize);
    fn add_write(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize);
    fn add_flush(&mut self, id: usize);
    fn submit(&mut self) -> Result<()>;

    fn poll(&mut self) -> Vec<(usize, bool)>;
    fn busy(&self) -> bool;
}

pub trait BlockDevice: Send + Sync {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>>;
    fn sector_count(&self) -> u64;
    fn clone(&self) -> Box<dyn BlockDevice>;

    fn stripe_count(&self, stripe_sector_count: u64) -> usize {
        self.sector_count().div_ceil(stripe_sector_count) as usize
    }
}

impl Clone for Box<dyn BlockDevice> {
    fn clone(&self) -> Box<dyn BlockDevice> {
        self.as_ref().clone()
    }
}

mod bdev_crypt;
mod bdev_lazy;
mod bdev_null;
pub mod bdev_snapshot;
mod bdev_sync;
mod bdev_uring;
mod wait_for_completion;

#[cfg(test)]
pub(crate) mod bdev_test;

pub use bdev_lazy::{
    bgworker::{BgWorker, BgWorkerRequest},
    device::{LazyBlockDevice, SwappableMetadataState, SwappableSender},
    metadata::{
        save::DEFAULT_STRIPE_SECTOR_COUNT_SHIFT,
        shared_state::SharedMetadataState,
        types::{metadata_flags, UbiMetadata},
    },
    status_report::{StatusReport, StatusReporter},
};

pub use bdev_crypt::CryptBlockDevice;
pub use bdev_snapshot::{device::SnapshotBlockDevice, handle::SnapshotHandle};
pub use bdev_null::NullBlockDevice;
pub use bdev_sync::SyncBlockDevice;
pub use bdev_uring::UringBlockDevice;
pub use wait_for_completion::wait_for_completion;
