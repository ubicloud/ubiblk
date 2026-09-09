//! A device that presents more space than the disk under it holds, keeping the
//! rest in an object store.

mod channel;
mod device;
mod evictor;
mod map;
mod shared;

#[cfg(test)]
mod bdev_spill_tests;

pub use device::{SpillBlockDevice, StoreFactory};
pub use evictor::Evictor;
