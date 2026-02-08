#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

pub mod archive;
pub mod backends;
pub mod block_device;
pub mod cli;
pub mod config;
pub mod crypt;
pub mod error;
pub mod rekey;
pub mod stripe_server;
pub mod stripe_source;
pub mod utils;

pub use crypt::{CipherMethod, KeyEncryptionCipher};
pub use error::{Error, ErrorLocation, ErrorMeta, Result, ResultExt, UbiblkError};
pub use ubiblk_macros::error_context;
