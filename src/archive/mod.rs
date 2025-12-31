use crate::{
    crypt::{decode_xts_keys, encode_xts_keys},
    Result,
};
use serde::{Deserialize, Serialize};

/// Abstraction over a backend that can store and retrieve archived objects.
pub trait ArchiveStore {
    /// Store an object under the given `name`.
    fn put_object(&mut self, name: &str, data: &[u8]) -> Result<()>;
    /// Retrieve an object by its `name`.
    fn get_object(&self, name: &str) -> Result<Vec<u8>>;
    /// List all stored object names.
    fn list_objects(&self) -> Result<Vec<String>>;
}

/// Representation of `metadata.yaml` stored alongside archived stripes.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct ArchiveMetadata {
    /// Number of sectors per stripe.
    pub stripe_sector_count: u64,
    /// Optional encrypted keys used for encrypting the archived data.
    #[serde(
        default,
        deserialize_with = "decode_xts_keys",
        serialize_with = "encode_xts_keys"
    )]
    pub encryption_key: Option<(Vec<u8>, Vec<u8>)>,
}

mod archiver;
mod fs_store;

pub use archiver::StripeArchiver;
pub use fs_store::FileSystemStore;

#[cfg(test)]
mod mem_store;
