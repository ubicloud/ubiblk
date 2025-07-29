mod backend;
mod options;
mod request;
pub use backend::{block_backend_loop, init_metadata};
pub use options::{CipherMethod, KeyEncryptionCipher, Options};
mod backend_thread;

pub const SECTOR_SIZE: usize = 512;

#[cfg(test)]
mod backend_tests;

#[cfg(test)]
mod backend_thread_tests;

#[cfg(test)]
pub use backend::{start_block_backend, UbiBlkBackend};
