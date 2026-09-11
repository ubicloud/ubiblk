//! The `[spill]` section: a device larger than the disk under it.

use std::path::PathBuf;

use serde::Deserialize;

use super::stripe_source::ArchiveStorageConfig;

fn default_chunk_kb() -> u32 {
    128
}

#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct SpillSection {
    /// What the guest sees, which is normally much larger than `data_path`.
    pub size_mb: u64,
    /// Where the authority map lives. Next to the data it describes.
    pub map_path: PathBuf,
    /// The namespace objects are written under. Never share one between
    /// devices: an object name belongs to exactly one map.
    pub prefix: String,
    /// This device's identity, checked against the map on every open.
    pub device_uuid: String,
    #[serde(default = "default_chunk_kb")]
    pub chunk_kb: u32,
    /// Where the cold tier lives.
    pub store: ArchiveStorageConfig,
}

impl SpillSection {
    pub fn chunk_bytes(&self) -> u64 {
        u64::from(self.chunk_kb) * 1024
    }

    pub fn uuid_bytes(&self) -> crate::Result<[u8; 16]> {
        let hex = self.device_uuid.replace('-', "");
        if hex.len() != 32 || !hex.chars().all(|c| c.is_ascii_hexdigit()) {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: format!(
                    "device_uuid must be 32 hex digits, not {:?}",
                    self.device_uuid
                ),
            }));
        }
        let mut bytes = [0u8; 16];
        for (i, byte) in bytes.iter_mut().enumerate() {
            *byte = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16).expect("checked above");
        }
        Ok(bytes)
    }

    /// What the map records about where the cold tier is, so the same map is
    /// never opened against a different one. The same prefix in another bucket
    /// is a different namespace.
    pub fn store_digest(&self) -> [u8; 32] {
        use sha2::{Digest, Sha256};
        let where_it_is = match &self.store {
            ArchiveStorageConfig::Filesystem { path, .. } => {
                format!("fs:{}", path.display())
            }
            ArchiveStorageConfig::S3 {
                bucket,
                prefix,
                endpoint,
                region,
                ..
            } => format!(
                "s3:{}:{}:{}:{}",
                endpoint.clone().unwrap_or_default(),
                region.clone().unwrap_or_default(),
                bucket,
                prefix.clone().unwrap_or_default()
            ),
        };
        Sha256::digest(format!("{where_it_is}|{}", self.prefix).as_bytes()).into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn section(uuid: &str) -> SpillSection {
        SpillSection {
            size_mb: 1024,
            map_path: PathBuf::from("map"),
            prefix: "dev".to_string(),
            device_uuid: uuid.to_string(),
            chunk_kb: 128,
            store: ArchiveStorageConfig::Filesystem {
                path: PathBuf::from("/tmp/store"),
                archive_kek: None,
                autofetch: false,
            },
        }
    }

    #[test]
    fn a_uuid_is_read_with_or_without_its_dashes() {
        let plain = section("0123456789abcdef0123456789abcdef");
        let dashed = section("01234567-89ab-cdef-0123-456789abcdef");
        assert_eq!(plain.uuid_bytes().unwrap(), dashed.uuid_bytes().unwrap());
        assert_eq!(plain.uuid_bytes().unwrap()[0], 0x01);
    }

    #[test]
    fn a_uuid_that_is_not_one_is_refused() {
        assert!(section("nope").uuid_bytes().is_err());
        assert!(section("0123456789abcdef0123456789abcdeg")
            .uuid_bytes()
            .is_err());
        assert!(section("0123456789abcdef0123456789abcde")
            .uuid_bytes()
            .is_err());
    }

    #[test]
    fn the_same_prefix_in_another_store_is_another_namespace() {
        let here = section("0123456789abcdef0123456789abcdef");
        let mut elsewhere = here.clone();
        elsewhere.store = ArchiveStorageConfig::Filesystem {
            path: PathBuf::from("/tmp/other"),
            archive_kek: None,
            autofetch: false,
        };

        assert_ne!(here.store_digest(), elsewhere.store_digest());
    }
}
