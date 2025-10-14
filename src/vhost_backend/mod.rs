mod backend;
mod backend_loop;
mod options;
mod request;
pub use backend::init_metadata;
pub use backend_loop::block_backend_loop;
pub use options::{CipherMethod, KeyEncryptionCipher, Options};
mod backend_thread;

pub const SECTOR_SIZE: usize = 512;

#[cfg(test)]
mod backend_tests;

#[cfg(test)]
mod backend_thread_tests;

#[cfg(test)]
pub use backend::UbiBlkBackend;
