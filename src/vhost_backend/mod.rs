mod backend;
mod options;
mod request;
pub use backend::{block_backend_loop, init_metadata};
pub use options::{CipherMethod, KeyEncryptionCipher, Options};
mod backend_thread;

pub const SECTOR_SIZE: usize = 512;
