use std::path::{Path, PathBuf};

use serde::{Deserialize, Deserializer, Serialize};
use virtio_bindings::virtio_blk::VIRTIO_BLK_ID_BYTES;

use crate::config::stripe_source::{RawStripeSourceConfig, StripeSourceConfig};
use crate::crypt::{decode_optional_key_pair, KeyEncryptionCipher};

fn default_poll_queue_timeout_us() -> u128 {
    1000
}

fn default_num_queues() -> usize {
    1
}

fn default_queue_size() -> usize {
    64
}

fn default_seg_size_max() -> u32 {
    65536
}

fn default_seg_count_max() -> u32 {
    4
}

fn default_copy_on_read() -> bool {
    false
}

fn default_track_written() -> bool {
    false
}

fn default_write_through() -> bool {
    false
}

fn default_autofetch() -> bool {
    false
}

fn default_device_id() -> String {
    "ubiblk".to_string()
}

fn deserialize_device_id<'de, D>(deserializer: D) -> Result<String, D::Error>
where
    D: Deserializer<'de>,
{
    let s = String::deserialize(deserializer)?;
    if s.len() > VIRTIO_BLK_ID_BYTES as usize {
        return Err(serde::de::Error::custom(format!(
            "device_id exceeds maximum of {VIRTIO_BLK_ID_BYTES} bytes"
        )));
    }
    Ok(s)
}

#[derive(Debug, Clone, Deserialize, Default)]
pub struct DeviceConfig {
    pub path: String,
    #[deprecated(note = "use stripe_source with source: raw and path field instead")]
    pub image_path: Option<String>,
    #[serde(default)]
    pub stripe_source: Option<StripeSourceConfig>,
    pub metadata_path: Option<String>,
    pub rpc_socket_path: Option<String>,
    pub socket: Option<String>,

    #[serde(default)]
    pub cpus: Option<Vec<usize>>,

    #[serde(default = "default_num_queues")]
    pub num_queues: usize,

    #[serde(default = "default_queue_size")]
    pub queue_size: usize,

    #[serde(default = "default_seg_size_max")]
    pub seg_size_max: u32,

    #[serde(default = "default_seg_count_max")]
    pub seg_count_max: u32,

    #[serde(default = "default_poll_queue_timeout_us")]
    pub poll_queue_timeout_us: u128,

    #[serde(default = "default_copy_on_read")]
    pub copy_on_read: bool,

    #[serde(default = "default_track_written")]
    pub track_written: bool,

    #[serde(default = "default_write_through")]
    pub write_through: bool,

    #[serde(default = "default_autofetch")]
    pub autofetch: bool,

    #[serde(default, deserialize_with = "decode_optional_key_pair")]
    pub encryption_key: Option<(Vec<u8>, Vec<u8>)>,

    #[serde(
        default = "default_device_id",
        deserialize_with = "deserialize_device_id"
    )]
    pub device_id: String,

    #[serde(default)]
    pub io_engine: IoEngine,
}

impl DeviceConfig {
    #[allow(deprecated)]
    fn validate(&self) -> crate::Result<()> {
        if self.image_path.is_some() && self.stripe_source.is_some() {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: "Only one stripe source may be specified".to_string(),
            }));
        }

        if let Some(stripe_source) = &self.stripe_source {
            match stripe_source {
                StripeSourceConfig::Remote { config } => {
                    config.validate()?;
                    if !self.copy_on_read {
                        return Err(crate::ubiblk_error!(InvalidParameter {
                            description:
                                "copy_on_read must be enabled when using remote stripe source."
                                    .to_string(),
                        }));
                    }
                }
                StripeSourceConfig::Archive { .. } if !self.copy_on_read => {
                    return Err(crate::ubiblk_error!(InvalidParameter {
                        description:
                            "copy_on_read must be enabled when using archive stripe source."
                                .to_string(),
                    }));
                }
                _ => {}
            }
        }

        if self.resolved_stripe_source().is_some() && self.metadata_path.is_none() {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: "metadata_path must be specified when using a stripe source."
                    .to_string(),
            }));
        }

        Ok(())
    }

    pub fn load_from_str(yaml_str: &str) -> crate::Result<Self> {
        Self::load_from_str_with_kek(yaml_str, &KeyEncryptionCipher::default())
    }

    pub fn load_from_str_with_kek(
        yaml_str: &str,
        kek: &KeyEncryptionCipher,
    ) -> crate::Result<Self> {
        let mut config: DeviceConfig = serde_yaml::from_str(yaml_str).map_err(|e| {
            crate::ubiblk_error!(InvalidParameter {
                description: format!("Failed to parse device config YAML: {}", e),
            })
        })?;
        config.decrypt_with_kek(kek)?;
        config.validate()?;
        Ok(config)
    }

    pub fn load_from_file(path: &Path) -> crate::Result<Self> {
        Self::load_from_file_with_kek(path, &KeyEncryptionCipher::default())
    }

    pub fn load_from_file_with_kek(path: &Path, kek: &KeyEncryptionCipher) -> crate::Result<Self> {
        let contents = std::fs::read_to_string(path).map_err(|e| {
            crate::ubiblk_error!(InvalidParameter {
                description: format!(
                    "Failed to read device config file {}: {}",
                    path.display(),
                    e
                ),
            })
        })?;
        Self::load_from_str_with_kek(&contents, kek)
    }

    #[allow(deprecated)]
    pub fn has_stripe_source(&self) -> bool {
        self.stripe_source.is_some() || self.image_path.is_some()
    }

    #[allow(deprecated)]
    pub fn resolved_stripe_source(&self) -> Option<StripeSourceConfig> {
        self.stripe_source.clone().or_else(|| {
            self.image_path
                .as_ref()
                .map(|path| StripeSourceConfig::Raw {
                    config: RawStripeSourceConfig {
                        path: PathBuf::from(path),
                    },
                })
        })
    }

    #[allow(deprecated)]
    pub fn raw_image_path(&self) -> Option<PathBuf> {
        match self.stripe_source.as_ref() {
            Some(StripeSourceConfig::Raw { config }) => Some(config.path.clone()),
            _ => self.image_path.as_ref().map(PathBuf::from),
        }
    }

    fn decrypt_with_kek(&mut self, kek: &KeyEncryptionCipher) -> crate::Result<()> {
        if let Some((key1, key2)) = self.encryption_key.take() {
            let (key1, key2) = kek.decrypt_xts_keys(key1, key2)?;
            self.encryption_key = Some((key1.to_vec(), key2.to_vec()));
        }

        if let Some(stripe_source) = self.stripe_source.as_mut() {
            match stripe_source {
                StripeSourceConfig::Remote { config } => config.decrypt_with_kek(kek)?,
                StripeSourceConfig::Archive { config } => {
                    config.decrypt_with_kek(kek)?;
                }
                StripeSourceConfig::Raw { .. } => {}
            }
        }

        Ok(())
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Default)]
#[serde(rename_all = "snake_case")]
pub enum IoEngine {
    #[default]
    IoUring,
    Sync,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::stripe_source::{RawStripeSourceConfig, StripeSourceConfig};
    use crate::crypt::{CipherMethod, KeyEncryptionCipher};
    use base64::{engine::general_purpose::STANDARD, Engine};
    use serde_yaml::from_str;

    #[test]
    fn test_key_encryption_cipher() {
        let yaml = r#"
        method: aes256-gcm
        key: "uCvGiJ+tlAL0635kGhUaOhmgseSkoCK1HDhxJGgujSI="
        init_vector: "UEt+wI+Ldq1UgQ/P"
        auth_data: "dm0zamdlejhfMA=="
        "#;

        let cipher: KeyEncryptionCipher = from_str(yaml).unwrap();
        assert_eq!(cipher.method, CipherMethod::Aes256Gcm);
        assert_eq!(
            cipher.key,
            Some(vec![
                0xb8, 0x2b, 0xc6, 0x88, 0x9f, 0xad, 0x94, 0x02, 0xf4, 0xeb, 0x7e, 0x64, 0x1a, 0x15,
                0x1a, 0x3a, 0x19, 0xa0, 0xb1, 0xe4, 0xa4, 0xa0, 0x22, 0xb5, 0x1c, 0x38, 0x71, 0x24,
                0x68, 0x2e, 0x8d, 0x22,
            ])
        );
        assert_eq!(
            cipher.init_vector,
            Some(vec![
                0x50, 0x4b, 0x7e, 0xc0, 0x8f, 0x8b, 0x76, 0xad, 0x54, 0x81, 0x0f, 0xcf,
            ])
        );
        assert_eq!(
            cipher.auth_data,
            Some(vec![
                0x76, 0x6d, 0x33, 0x6a, 0x67, 0x65, 0x7a, 56, 0x5f, 0x30
            ])
        );
    }

    #[test]
    fn test_decode_encryption_keys() {
        let kek_key = [0x11u8; 32];
        let iv = [0x22u8; 12];
        let aad = b"test-aad";
        let kek = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(kek_key.to_vec()),
            init_vector: Some(iv.to_vec()),
            auth_data: Some(aad.to_vec()),
        };
        let key1 = vec![0xAAu8; 32];
        let key2 = vec![0xBBu8; 32];
        let (enc1, enc2) = kek.encrypt_xts_keys(&key1, &key2).unwrap();

        let yaml = format!(
            r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        encryption_key:
          - "{}"
          - "{}"
        "#,
            STANDARD.encode(enc1),
            STANDARD.encode(enc2),
        );
        let config = DeviceConfig::load_from_str_with_kek(&yaml, &kek).unwrap();
        assert_eq!(config.encryption_key, Some((key1, key2)));
    }

    #[test]
    fn test_missing_encryption_key() {
        let yaml = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        "#;
        let config = DeviceConfig::load_from_str(yaml).unwrap();
        assert!(config.encryption_key.is_none());
    }

    #[test]
    fn test_default_values() {
        let yaml = r#"
        path: "/path/to/disk"
        "#;
        let config = DeviceConfig::load_from_str(yaml).unwrap();
        assert!(!config.copy_on_read);
        assert!(!config.track_written);
        assert!(!config.write_through);
        assert_eq!(config.device_id, "ubiblk".to_string());
        assert!(config.rpc_socket_path.is_none());
        assert!(config.socket.is_none());
        assert!(!config.autofetch);
        assert_eq!(config.io_engine, IoEngine::IoUring);
    }

    #[test]
    fn test_device_id_length() {
        let yaml = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        device_id: "12345678901234567890"
        "#;
        let config = DeviceConfig::load_from_str(yaml).unwrap();
        assert_eq!(config.device_id, "12345678901234567890".to_string());

        let yaml_too_long = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        device_id: "123456789012345678901"
        "#;
        assert!(from_str::<DeviceConfig>(yaml_too_long).is_err());
    }

    #[test]
    fn test_write_through_enabled() {
        let yaml = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        write_through: true
        "#;
        let config = DeviceConfig::load_from_str(yaml).unwrap();
        assert!(config.write_through);
    }

    #[test]
    fn test_cpus_parsing() {
        let yaml = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        num_queues: 2
        cpus:
          - 1
          - 2
        "#;
        let config = DeviceConfig::load_from_str(yaml).unwrap();
        assert_eq!(config.cpus, Some(vec![1, 2]));
    }

    #[test]
    fn test_io_engine_parsing() {
        let yaml_uring = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        io_engine: io_uring
        "#;
        let config_uring = DeviceConfig::load_from_str(yaml_uring).unwrap();
        assert_eq!(config_uring.io_engine, IoEngine::IoUring);

        let yaml_sync = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        io_engine: sync
        "#;
        let config_sync = DeviceConfig::load_from_str(yaml_sync).unwrap();
        assert_eq!(config_sync.io_engine, IoEngine::Sync);
    }

    #[test]
    fn test_error_on_two_stripe_sources() {
        let yaml = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        image_path: "/path/to/image_path"
        stripe_source:
          source: remote
          address: "1.2.3.4:4567"
        "#;
        let result = DeviceConfig::load_from_str(yaml);
        assert!(result.is_err());
    }

    #[test]
    fn test_error_on_remote_image_without_copy_on_read() {
        let yaml = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        stripe_source:
          source: remote
          address: "1.2.3.4:4567"
        "#;
        let result = DeviceConfig::load_from_str(yaml);
        assert!(result.is_err());
    }

    #[test]
    fn test_valid_remote_image_with_copy_on_read() {
        let yaml = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        metadata_path: "/path/to/metadata"
        stripe_source:
          source: remote
          address: "1.2.3.4:4567"
          allow_insecure: true
        copy_on_read: true
        "#;
        let result = DeviceConfig::load_from_str(yaml);
        assert!(result.is_ok());
        let config = result.unwrap();
        assert!(matches!(
            config.resolved_stripe_source(),
            Some(StripeSourceConfig::Remote { .. })
        ));
        assert_eq!(config.raw_image_path(), None);
    }

    #[test]
    fn test_error_on_archive_and_not_copy_on_read() {
        let yaml = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        metadata_path: "/path/to/metadata"
        copy_on_read: false
        stripe_source:
          source: archive
          type: filesystem
          path: "/path/to/archive"
        "#;

        let result = DeviceConfig::load_from_str(yaml);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("copy_on_read must be enabled when using archive stripe source"));
    }

    #[test]
    fn test_error_on_archive_and_image_path() {
        let yaml = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        metadata_path: "/path/to/metadata"
        copy_on_read: true
        stripe_source:
          source: archive
          type: filesystem
          path: "/path/to/archive"
        image_path: "/path/to/image_path"
        "#;
        let result = DeviceConfig::load_from_str(yaml);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Only one stripe source may be specified"));
    }

    #[test]
    fn test_raw_image_path_old_style() {
        let yaml = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        metadata_path: "/path/to/metadata"
        image_path: "/path/to/image"
        "#;
        let config = DeviceConfig::load_from_str(yaml).unwrap();
        assert_eq!(
            config.resolved_stripe_source(),
            Some(StripeSourceConfig::Raw {
                config: RawStripeSourceConfig {
                    path: PathBuf::from("/path/to/image")
                }
            })
        );
        assert_eq!(
            config.raw_image_path(),
            Some(PathBuf::from("/path/to/image"))
        );
    }

    #[test]
    fn test_raw_image_path_new_style() {
        let yaml = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        metadata_path: "/path/to/metadata"
        stripe_source:
            source: raw
            path: "/path/to/image"
        "#;
        let config = DeviceConfig::load_from_str(yaml).unwrap();
        assert_eq!(
            config.resolved_stripe_source(),
            Some(StripeSourceConfig::Raw {
                config: RawStripeSourceConfig {
                    path: PathBuf::from("/path/to/image")
                }
            })
        );
        assert_eq!(
            config.raw_image_path(),
            Some(PathBuf::from("/path/to/image"))
        );
    }

    #[test]
    fn test_stripe_source_requires_metadata_path() {
        let yaml = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        copy_on_read: true
        stripe_source:
          source: raw
          path: "/path/to/image"
        "#;

        let result = DeviceConfig::load_from_str(yaml);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("metadata_path must be specified when using a stripe source"));
    }

    #[test]
    fn test_load_from_str_with_kek_invalid_yaml() {
        let invalid_yaml = "xyz: [unclosed_list";
        let result =
            DeviceConfig::load_from_str_with_kek(invalid_yaml, &KeyEncryptionCipher::default());
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Failed to parse device config YAML"));
    }

    #[test]
    fn test_load_from_file_missing_file() {
        let missing_path = Path::new("/non/existent/config.yaml");
        let result = DeviceConfig::load_from_file(missing_path);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Failed to read device config file"));
    }
}
