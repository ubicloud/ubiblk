use crate::utils::aligned_buffer::AlignedBuf;
use crate::Result;
use std::{cell::RefCell, rc::Rc};

pub type SharedBuffer = Rc<RefCell<AlignedBuf>>;

pub trait IoChannel {
    fn add_read(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize);
    fn add_write(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize);
    fn add_flush(&mut self, id: usize);
    fn submit(&mut self) -> Result<()>;

    fn poll(&mut self) -> Vec<(usize, bool)>;
    fn busy(&self) -> bool;
}

pub trait BlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>>;
    fn sector_count(&self) -> u64;
}

mod bdev_crypt;
mod bdev_lazy;
mod bdev_sync;
mod bdev_uring;

#[cfg(test)]
pub(crate) mod bdev_test;

pub use bdev_crypt::CryptBlockDevice;
pub use bdev_lazy::init_metadata;
pub use bdev_lazy::LazyBlockDevice;
pub use bdev_lazy::UbiMetadata;
pub use bdev_lazy::{BgWorker, BgWorkerRequest, SharedBgWorker};
pub use bdev_sync::SyncBlockDevice;
pub use bdev_uring::UringBlockDevice;
