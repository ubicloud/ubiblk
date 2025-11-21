mod backend;
mod backend_loop;
mod io_tracking;
mod options;
mod request;
mod rpc;
pub use backend_loop::{block_backend_loop, init_metadata};
pub use options::{CipherMethod, IoEngine, KeyEncryptionCipher, Options};
mod backend_thread;

pub const SECTOR_SIZE: usize = 512;

#[cfg(test)]
mod backend_tests;

#[cfg(test)]
mod backend_thread_tests;

#[cfg(test)]
pub use backend::UbiBlkBackend;
