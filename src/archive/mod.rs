use std::time::{Duration, Instant};

use crate::{
    crypt::{decode_key, decode_optional_key_pair, encode_key, encode_optional_key_pair},
    Result,
};
use serde::{Deserialize, Serialize};

pub const DEFAULT_ARCHIVE_TIMEOUT: Duration = Duration::from_secs(30);
pub const ARCHIVE_FORMAT_VERSION: u32 = 2;
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
    Zstd {
        level: i32,
    },
}

const METADATA_HMAC_DOMAIN: &[u8] = b"ubiblk-archive-metadata";

/// Representation of `metadata.json` stored alongside archived stripes.
#[derive(Clone, Serialize, Deserialize)]
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
    /// HMAC-SHA256 tag over all metadata fields (v2+). Absent in v1.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub metadata_hmac: Option<String>,
}

/// Build the canonical byte string for metadata HMAC computation.
/// Covers: domain || format_version || stripe_sector_count || compression_json || encryption_key_bytes || hmac_key_bytes
fn metadata_hmac_input(metadata: &ArchiveMetadata) -> Vec<u8> {
    let compression_json = serde_json::to_string(&metadata.compression)
        .expect("compression serialization cannot fail");
    let encryption_key_bytes: Vec<u8> = match &metadata.encryption_key {
        Some((a, b)) => {
            let mut v = Vec::with_capacity(a.len() + b.len());
            v.extend_from_slice(a);
            v.extend_from_slice(b);
            v
        }
        None => Vec::new(),
    };
    let mut data = Vec::new();
    data.extend_from_slice(METADATA_HMAC_DOMAIN);
    data.extend_from_slice(&metadata.format_version.to_le_bytes());
    data.extend_from_slice(&metadata.stripe_sector_count.to_le_bytes());
    data.extend_from_slice(compression_json.as_bytes());
    data.extend_from_slice(&encryption_key_bytes);
    data.extend_from_slice(&metadata.hmac_key);
    data
}

/// Compute the metadata HMAC tag for a v2 archive.
pub fn compute_metadata_hmac(hmac_key: &[u8], metadata: &ArchiveMetadata) -> Result<String> {
    let input = metadata_hmac_input(metadata);
    let tag = compute_manifest_hmac_tag(hmac_key, &input)?;
    Ok(hex::encode(tag))
}

/// Verify the metadata HMAC tag. Returns Ok(()) on match, Err on mismatch.
pub fn verify_metadata_hmac(
    hmac_key: &[u8],
    metadata: &ArchiveMetadata,
    tag_hex: &str,
) -> Result<()> {
    let input = metadata_hmac_input(metadata);
    let tag_bytes = hex::decode(tag_hex).map_err(|e| {
        crate::ubiblk_error!(MetadataError {
            description: format!("invalid metadata HMAC hex encoding: {e}"),
        })
    })?;
    verify_manifest_hmac_tag(hmac_key, &input, &tag_bytes).map_err(|_| {
        crate::ubiblk_error!(MetadataError {
            description: "metadata HMAC verification failed: metadata may have been tampered with"
                .to_string(),
        })
    })
}

impl std::fmt::Debug for ArchiveMetadata {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ArchiveMetadata")
            .field("format_version", &self.format_version)
            .field("stripe_sector_count", &self.stripe_sector_count)
            .field(
                "encryption_key",
                &self.encryption_key.as_ref().map(|_| "[REDACTED]"),
            )
            .field("compression", &self.compression)
            .field("hmac_key", &"[REDACTED]")
            .finish()
    }
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

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_archive_metadata_debug_redaction() {
        let metadata = ArchiveMetadata {
            format_version: 1,
            stripe_sector_count: 128,
            encryption_key: Some((vec![123u8; 32], vec![234u8; 32])),
            compression: ArchiveCompressionAlgorithm::Zstd { level: 3 },
            hmac_key: vec![178u8; 32],
        };
        let debug_str = format!("{:?}", metadata);
        assert!(debug_str.contains("format_version: 1"));
        assert!(debug_str.contains("stripe_sector_count: 128"));
        assert!(debug_str.contains("encryption_key: Some(\"[REDACTED]\")"));
        assert!(debug_str.contains("compression: Zstd { level: 3 }"));
        assert!(debug_str.contains("hmac_key: \"[REDACTED]\""));
        assert!(!debug_str.contains("123"));
        assert!(!debug_str.contains("234"));
        assert!(!debug_str.contains("178"));
    }
}
