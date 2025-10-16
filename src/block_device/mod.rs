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

    fn stripe_has_data(&self, _stripe_id: u64) -> bool {
        true
    }
}

pub trait BlockDevice: Send + Sync {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>>;
    fn sector_count(&self) -> u64;
    fn clone(&self) -> Box<dyn BlockDevice>;
}

impl Clone for Box<dyn BlockDevice> {
    fn clone(&self) -> Box<dyn BlockDevice> {
        self.as_ref().clone()
    }
}

mod bdev_crypt;
mod bdev_lazy;
mod bdev_null;
mod bdev_remote;
mod bdev_sync;
mod bdev_uring;

#[cfg(test)]
pub(crate) mod bdev_test;

pub use bdev_crypt::{decrypt_with_kek, CryptBlockDevice};
pub use bdev_lazy::init_metadata;
pub use bdev_lazy::load_metadata;
pub use bdev_lazy::LazyBlockDevice;
pub use bdev_lazy::UbiMetadata;
pub use bdev_lazy::{BgWorker, BgWorkerRequest, SharedMetadataState, StatusReport, StatusReporter};
pub use bdev_null::NullBlockDevice;
pub use bdev_remote::{RemoteBlockDevice, RemoteTlsConfig};
pub use bdev_sync::SyncBlockDevice;
pub use bdev_uring::UringBlockDevice;
