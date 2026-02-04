use std::time::{Duration, Instant};

use crate::{
    crypt::{decode_key, decode_optional_key_pair, encode_key, encode_optional_key_pair},
    Result,
};
use serde::{Deserialize, Serialize};

pub const DEFAULT_ARCHIVE_TIMEOUT: Duration = Duration::from_secs(30);
pub const ARCHIVE_FORMAT_VERSION: u32 = 1;
pub const ARCHIVE_FORMAT_VERSION_MIN: u32 = 1;
pub const ARCHIVE_FORMAT_VERSION_MAX: u32 = ARCHIVE_FORMAT_VERSION;

/// Abstraction over a backend that can store and retrieve archived objects.
pub trait ArchiveStore {
    /// Asynchronously store an object under the given `name`. Completion can be
    /// polled via `poll_puts`.
    fn start_put_object(&mut self, name: &str, data: Vec<u8>);
    /// Asynchronously retrieve an object by its `name`. Completion can be
    /// polled via `poll_gets`.
    fn start_get_object(&mut self, name: &str);
    /// Poll for completed put operations. Each returned tuple contains the
    /// object name and the result of the operation.
    fn poll_puts(&mut self) -> Vec<(String, Result<()>)>;
    /// Poll for completed get operations. Each returned tuple contains the
    /// object name and the result of the operation.
    fn poll_gets(&mut self) -> Vec<(String, Result<Vec<u8>>)>;

    /// Convenience method to synchronously put an object.
    /// NOTE: Asynchronous and synchronous operations should not be mixed.
    fn put_object(&mut self, name: &str, data: &[u8], timeout: Duration) -> Result<()> {
        self.start_put_object(name, data.to_vec());
        let start_time = Instant::now();

        while start_time.elapsed() < timeout {
            let results = self.poll_puts();
            for (obj_name, result) in results {
                if obj_name == name {
                    return result;
                }
            }
            std::thread::sleep(std::time::Duration::from_millis(1));
        }

        Err(crate::ubiblk_error!(ArchiveError {
            description: format!("Timeout while putting object {}", name),
        }))
    }

    /// Convenience method to synchronously get an object.
    /// NOTE: Asynchronous and synchronous operations should not be mixed.
    fn get_object(&mut self, name: &str, timeout: Duration) -> Result<Vec<u8>> {
        self.start_get_object(name);
        let start_time = Instant::now();

        while start_time.elapsed() < timeout {
            let results = self.poll_gets();
            for (obj_name, result) in results {
                if obj_name == name {
                    return result;
                }
            }
            std::thread::sleep(std::time::Duration::from_millis(1));
        }

        Err(crate::ubiblk_error!(ArchiveError {
            description: format!("Timeout while getting object {}", name),
        }))
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
#[serde(rename_all = "snake_case")]
pub enum ArchiveCompressionAlgorithm {
    #[default]
    None,
    Snappy,
}

/// Representation of `metadata.json` stored alongside archived stripes.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ArchiveMetadata {
    /// Archive format version.
    pub format_version: u32,
    /// Number of sectors per stripe.
    pub stripe_sector_count: u64,
    /// Optional encrypted keys used for encrypting the archived data.
    #[serde(
        default,
        deserialize_with = "decode_optional_key_pair",
        serialize_with = "encode_optional_key_pair"
    )]
    pub encryption_key: Option<(Vec<u8>, Vec<u8>)>,
    #[serde(default)]
    pub compression: ArchiveCompressionAlgorithm,
    #[serde(
        default,
        deserialize_with = "decode_key",
        serialize_with = "encode_key"
    )]
    pub hmac_key: Vec<u8>,
}

pub fn validate_format_version(version: u32) -> Result<()> {
    if !(ARCHIVE_FORMAT_VERSION_MIN..=ARCHIVE_FORMAT_VERSION_MAX).contains(&version) {
        return Err(crate::ubiblk_error!(MetadataError {
            description: format!(
                "unsupported archive format version {} (supported {}..={})",
                version, ARCHIVE_FORMAT_VERSION_MIN, ARCHIVE_FORMAT_VERSION_MAX
            ),
        }));
    }
    Ok(())
}

mod archiver;
mod bytes32;
mod compression;
mod fs_store;
mod s3_store;
mod stripe_hashes;

pub use archiver::StripeArchiver;
pub use fs_store::FileSystemStore;
pub use s3_store::S3Store;
pub use stripe_hashes::{compute_manifest_hmac_tag, verify_manifest_hmac_tag};
pub use stripe_hashes::{
    deserialize_stripe_mapping, serialize_stripe_mapping, StripeContentMap, StripeContentSpecifier,
};

#[cfg(test)]
mod mem_store;

#[cfg(test)]
pub use mem_store::MemStore;
