#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

pub mod archive;
pub mod block_device;
pub mod cli;
pub mod crypt;
pub mod error;
pub mod stripe_server;
pub mod stripe_source;
pub mod utils;
pub mod vhost_backend;

pub use crypt::{CipherMethod, KeyEncryptionCipher};
pub use error::{Error, Result, UbiblkError};
