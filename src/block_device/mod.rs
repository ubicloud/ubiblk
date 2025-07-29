use crate::utils::aligned_buffer::AlignedBuf;
use crate::Result;
use std::{
    cell::{Ref, RefCell, RefMut},
    ops::{Deref, DerefMut},
    rc::Rc,
};

#[derive(Debug, Clone)]
pub struct SharedBuffer(Rc<RefCell<AlignedBuf>>);

impl SharedBuffer {
    pub fn new(buf: AlignedBuf) -> Self {
        SharedBuffer(Rc::new(RefCell::new(buf)))
    }

    pub fn borrow(&self) -> Ref<'_, AlignedBuf> {
        self.0.borrow()
    }

    pub fn borrow_mut(&self) -> RefMut<'_, AlignedBuf> {
        self.0.borrow_mut()
    }
}

impl Deref for SharedBuffer {
    type Target = Rc<RefCell<AlignedBuf>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for SharedBuffer {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

unsafe impl Send for SharedBuffer {}
unsafe impl Sync for SharedBuffer {}

pub trait IoChannel: Send {
    fn add_read(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize);
    fn add_write(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize);
    fn add_flush(&mut self, id: usize);
    fn submit(&mut self) -> Result<()>;

    fn poll(&mut self) -> Vec<(usize, bool)>;
    fn busy(&mut self) -> bool;
}

pub trait BlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel + Send>>;
    fn sector_count(&self) -> u64;
}

mod bdev_crypt;
mod bdev_lazy;
mod bdev_sync;
mod bdev_uring;

#[cfg(test)]
pub(crate) mod bdev_test;

#[cfg(test)]
pub(crate) mod bdev_failing;

pub use bdev_crypt::CryptBlockDevice;
pub use bdev_lazy::init_metadata;
pub use bdev_lazy::LazyBlockDevice;
pub use bdev_lazy::UbiMetadata;
pub use bdev_lazy::{BgWorker, BgWorkerRequest, SharedBgWorker};
pub use bdev_sync::SyncBlockDevice;
pub use bdev_uring::UringBlockDevice;
