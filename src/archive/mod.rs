use serde::{Deserialize, Serialize};

use crate::Result;

pub trait ArchiveStore {
    fn put_object(&mut self, name: &str, data: &[u8]) -> Result<()>;
    fn get_object(&self, name: &str) -> Result<Vec<u8>>;
    fn list_objects(&self) -> Result<Vec<String>>;
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct ArchiveMetadata {
    pub stripe_sector_count: u32,
    #[serde(
        default,
        deserialize_with = "crate::vhost_backend::decode_encryption_keys"
    )]
    pub encryption_key: Option<(Vec<u8>, Vec<u8>)>,
}

mod archiver;
mod fs_store;

#[cfg(test)]
mod mem_store;
