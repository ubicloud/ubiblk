#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

pub mod block_device;
pub mod error;
pub mod key_encryption;
pub mod stripe_server;
pub mod utils;
pub mod vhost_backend;

pub use error::{Result, VhostUserBlockError};
pub use key_encryption::{CipherMethod, KeyEncryptionCipher};
