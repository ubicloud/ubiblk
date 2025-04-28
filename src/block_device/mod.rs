use crate::Result;
use std::{cell::RefCell, rc::Rc};

pub type SharedBuffer = Rc<RefCell<Vec<u8>>>;

pub trait IoChannel {
    fn add_read(&mut self, sector: u64, buf: SharedBuffer, len: usize, id: usize);
    fn add_write(&mut self, sector: u64, buf: SharedBuffer, len: usize, id: usize);
    fn add_flush(&mut self, id: usize);
    fn submit(&mut self) -> Result<()>;

    fn poll(&mut self) -> Vec<(usize, bool)>;
    fn busy(&mut self) -> bool;
}

pub trait BlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>>;
    fn size(&self) -> u64;
}

mod bdev_crypt;
mod bdev_lazy;
mod bdev_sync;
mod bdev_uring;

pub use bdev_crypt::CryptBlockDevice;
pub use bdev_lazy::LazyBlockDevice;
pub use bdev_lazy::StripeFetcher;
pub use bdev_sync::SyncBlockDevice;
pub use bdev_uring::UringBlockDevice;
