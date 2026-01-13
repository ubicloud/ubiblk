use std::path::{Path, PathBuf};

use crate::crypt::{
    decode_key, decode_optional_key, decode_optional_key_pair, KeyEncryptionCipher,
};
use serde::{Deserialize, Deserializer, Serialize};
use virtio_bindings::virtio_blk::VIRTIO_BLK_ID_BYTES;

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

fn default_s3_connections() -> usize {
    16
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
pub struct Options {
    pub path: String,
    #[deprecated(note = "use stripe_source with source: raw and path field instead")]
    pub image_path: Option<String>,
    #[serde(default)]
    pub stripe_source: Option<StripeSourceConfig>,
    pub metadata_path: Option<String>,
    pub rpc_socket_path: Option<String>,
    pub socket: String,

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

impl Options {
    #[allow(deprecated)]
    fn validate(&self) -> crate::Result<()> {
        if self.image_path.is_some() && self.stripe_source.is_some() {
            return Err(crate::UbiblkError::InvalidParameter {
                description: "Only one stripe source may be specified".to_string(),
            });
        }

        if let Some(stripe_source) = &self.stripe_source {
            match stripe_source {
                StripeSourceConfig::Remote {
                    address: _,
                    psk_identity,
                    psk_secret,
                } => {
                    if !self.copy_on_read {
                        return Err(crate::UbiblkError::InvalidParameter {
                            description:
                                "copy_on_read must be enabled when using remote stripe source."
                                    .to_string(),
                        });
                    }
                    if psk_identity.is_some() ^ psk_secret.is_some() {
                        return Err(crate::UbiblkError::InvalidParameter {
                            description:
                                "Both psk_identity and psk_secret must be specified together."
                                    .to_string(),
                        });
                    }
                }
                StripeSourceConfig::Archive { .. } if !self.copy_on_read => {
                    return Err(crate::UbiblkError::InvalidParameter {
                        description:
                            "copy_on_read must be enabled when using archive stripe source."
                                .to_string(),
                    });
                }
                _ => {}
            }
        }

        if self.resolved_stripe_source().is_some() && self.metadata_path.is_none() {
            return Err(crate::UbiblkError::InvalidParameter {
                description: "metadata_path must be specified when using a stripe source."
                    .to_string(),
            });
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
        let mut options: Options =
            serde_yaml::from_str(yaml_str).map_err(|e| crate::UbiblkError::InvalidParameter {
                description: format!("Failed to parse options YAML: {}", e),
            })?;
        options.decrypt_with_kek(kek)?;
        options.validate()?;
        Ok(options)
    }

    pub fn load_from_file(path: &Path) -> crate::Result<Self> {
        Self::load_from_file_with_kek(path, &KeyEncryptionCipher::default())
    }

    pub fn load_from_file_with_kek(path: &Path, kek: &KeyEncryptionCipher) -> crate::Result<Self> {
        let contents =
            std::fs::read_to_string(path).map_err(|e| crate::UbiblkError::InvalidParameter {
                description: format!("Failed to read options file {}: {}", path.display(), e),
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
                    path: PathBuf::from(path),
                })
        })
    }

    #[allow(deprecated)]
    pub fn raw_image_path(&self) -> Option<PathBuf> {
        match self.stripe_source.as_ref() {
            Some(StripeSourceConfig::Raw { path }) => Some(path.clone()),
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
                StripeSourceConfig::Remote { psk_secret, .. } => {
                    if let Some(secret) = psk_secret.take() {
                        *psk_secret = Some(kek.decrypt_psk_secret(secret)?);
                    }
                }
                StripeSourceConfig::Archive { config } => {
                    let archive_kek = config.archive_kek_mut();
                    Self::decrypt_archive_kek(kek, archive_kek)?;
                    if let ArchiveStripeSourceConfig::S3 { credentials, .. } = config {
                        if let Some(creds) = credentials.as_mut() {
                            let access_key_id = kek
                                .decrypt_aws_credential(std::mem::take(&mut creds.access_key_id))?;
                            let secret_access_key = kek.decrypt_aws_credential(std::mem::take(
                                &mut creds.secret_access_key,
                            ))?;
                            creds.access_key_id = access_key_id.into_bytes();
                            creds.secret_access_key = secret_access_key.into_bytes();
                        }
                    }
                }
                StripeSourceConfig::Raw { .. } => {}
            }
        }

        Ok(())
    }

    fn decrypt_archive_kek(
        kek: &KeyEncryptionCipher,
        archive_kek: &mut KeyEncryptionCipher,
    ) -> crate::Result<()> {
        Self::decrypt_optional_secret(kek, &mut archive_kek.key)?;
        Self::decrypt_optional_secret(kek, &mut archive_kek.init_vector)?;
        Self::decrypt_optional_secret(kek, &mut archive_kek.auth_data)?;
        Ok(())
    }

    fn decrypt_optional_secret(
        kek: &KeyEncryptionCipher,
        secret: &mut Option<Vec<u8>>,
    ) -> crate::Result<()> {
        if let Some(value) = secret.take() {
            *secret = Some(kek.decrypt_psk_secret(value)?);
        }
        Ok(())
    }
}

impl ArchiveStripeSourceConfig {
    pub fn archive_kek(&self) -> &KeyEncryptionCipher {
        match self {
            ArchiveStripeSourceConfig::Filesystem { archive_kek, .. } => archive_kek,
            ArchiveStripeSourceConfig::S3 { archive_kek, .. } => archive_kek,
        }
    }

    pub fn archive_kek_mut(&mut self) -> &mut KeyEncryptionCipher {
        match self {
            ArchiveStripeSourceConfig::Filesystem { archive_kek, .. } => archive_kek,
            ArchiveStripeSourceConfig::S3 { archive_kek, .. } => archive_kek,
        }
    }
}

#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case")]
pub struct AwsCredentials {
    #[serde(deserialize_with = "decode_key")]
    pub access_key_id: Vec<u8>,
    #[serde(deserialize_with = "decode_key")]
    pub secret_access_key: Vec<u8>,
}

#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case", tag = "source")]
pub enum StripeSourceConfig {
    /// Use a raw image file as the stripe source.
    Raw { path: PathBuf },

    /// Use a remote stripe server (identified by address or URL).
    Remote {
        address: String,
        #[serde(default)]
        psk_identity: Option<String>,
        #[serde(default, deserialize_with = "decode_optional_key")]
        psk_secret: Option<Vec<u8>>,
    },

    /// Use an archive store (e.g. directory or S3 bucket) as the stripe source.
    Archive {
        #[serde(flatten)]
        config: ArchiveStripeSourceConfig,
    },
}

#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case", tag = "type")]
pub enum ArchiveStripeSourceConfig {
    Filesystem {
        path: String,
        #[serde(default)]
        archive_kek: KeyEncryptionCipher,
    },
    S3 {
        bucket: String,
        #[serde(default)]
        prefix: Option<String>,
        #[serde(default)]
        endpoint: Option<String>,
        #[serde(default)]
        region: Option<String>,
        #[serde(default)]
        profile: Option<String>,
        #[serde(default)]
        credentials: Option<AwsCredentials>,
        #[serde(default = "default_s3_connections")]
        connections: usize,
        #[serde(default)]
        archive_kek: KeyEncryptionCipher,
    },
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
        let options = Options::load_from_str_with_kek(&yaml, &kek).unwrap();
        assert_eq!(options.encryption_key, Some((key1, key2)));
    }

    #[test]
    fn test_missing_encryption_key() {
        let yaml = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        "#;
        let options = Options::load_from_str(yaml).unwrap();
        assert!(options.encryption_key.is_none());
    }

    #[test]
    fn test_psk_fields() {
        let yaml = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        metadata_path: "/path/to/metadata"
        copy_on_read: true
        stripe_source:
          source: remote
          address: "1.2.3.4:4567"
          psk_identity: client1
          psk_secret: "MDEyMzQ1Njc4OUFCQ0RFRg=="
        "#;

        let options = Options::load_from_str(yaml).unwrap();
        assert!(matches!(
            options.resolved_stripe_source(),
            Some(StripeSourceConfig::Remote { .. })
        ));
        assert_eq!(options.raw_image_path(), None);

        let stripe_source = options.stripe_source.expect("stripe_source to be set");
        match stripe_source {
            StripeSourceConfig::Remote {
                psk_identity,
                psk_secret,
                ..
            } => {
                assert_eq!(psk_identity.as_deref(), Some("client1"));
                assert_eq!(psk_secret.as_deref(), Some(b"0123456789ABCDEF".as_ref()));
            }
            other => panic!("Unexpected stripe source: {other:?}"),
        }
    }

    #[test]
    fn test_psk_fields_missing_pair() {
        let yaml_secret_only = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        copy_on_read: true
        metadata_path: "/path/to/metadata"
        stripe_source:
          source: remote
          address: "1.2.3.4:4567"
          psk_secret: "MDEyMzQ1Njc4OUFCQ0RFRg=="
        "#;
        let result = Options::load_from_str(yaml_secret_only);
        assert!(result.is_err());
        assert!(result
            .err()
            .unwrap()
            .to_string()
            .contains("Both psk_identity and psk_secret must be specified together."));

        let yaml_identity_only = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        copy_on_read: true
        metadata_path: "/path/to/metadata"
        stripe_source:
          source: remote
          address: "1.2.3.4:4567"
          psk_identity: client1
        "#;
        let result = Options::load_from_str(yaml_identity_only);
        assert!(result.is_err());
        assert!(result
            .err()
            .unwrap()
            .to_string()
            .contains("Both psk_identity and psk_secret must be specified together."));
    }

    #[test]
    fn test_default_values() {
        let yaml = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        "#;
        let options = Options::load_from_str(yaml).unwrap();
        assert!(!options.copy_on_read);
        assert!(!options.track_written);
        assert!(!options.write_through);
        assert_eq!(options.device_id, "ubiblk".to_string());
        assert!(options.rpc_socket_path.is_none());
        assert!(!options.autofetch);
        assert_eq!(options.io_engine, IoEngine::IoUring);
    }

    #[test]
    fn test_device_id_length() {
        let yaml = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        device_id: "12345678901234567890"
        "#;
        let options = Options::load_from_str(yaml).unwrap();
        assert_eq!(options.device_id, "12345678901234567890".to_string());

        let yaml_too_long = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        device_id: "123456789012345678901"
        "#;
        assert!(from_str::<Options>(yaml_too_long).is_err());
    }

    #[test]
    fn test_write_through_enabled() {
        let yaml = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        write_through: true
        "#;
        let options = Options::load_from_str(yaml).unwrap();
        assert!(options.write_through);
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
        let options = Options::load_from_str(yaml).unwrap();
        assert_eq!(options.cpus, Some(vec![1, 2]));
    }

    #[test]
    fn test_io_engine_parsing() {
        let yaml_uring = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        io_engine: io_uring
        "#;
        let options_uring = Options::load_from_str(yaml_uring).unwrap();
        assert_eq!(options_uring.io_engine, IoEngine::IoUring);

        let yaml_sync = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        io_engine: sync
        "#;
        let options_sync = Options::load_from_str(yaml_sync).unwrap();
        assert_eq!(options_sync.io_engine, IoEngine::Sync);
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
        let result = Options::load_from_str(yaml);
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
        let result = Options::load_from_str(yaml);
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
        copy_on_read: true
        "#;
        let result = Options::load_from_str(yaml);
        assert!(result.is_ok());
        let options = result.unwrap();
        assert!(matches!(
            options.resolved_stripe_source(),
            Some(StripeSourceConfig::Remote { .. })
        ));
        assert_eq!(options.raw_image_path(), None);
    }

    #[test]
    fn test_filesystem_archive_source_parsing() {
        let yaml = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        metadata_path: "/path/to/metadata"
        copy_on_read: true
        stripe_source:
          source: archive
          type: filesystem
          path: "/path/to/archive"
        "#;

        let options = Options::load_from_str(yaml).unwrap();

        assert_eq!(
            options.stripe_source,
            Some(StripeSourceConfig::Archive {
                config: ArchiveStripeSourceConfig::Filesystem {
                    path: "/path/to/archive".to_string(),
                    archive_kek: KeyEncryptionCipher::default(),
                }
            })
        );

        assert!(matches!(
            options.resolved_stripe_source(),
            Some(StripeSourceConfig::Archive { .. })
        ));
        assert_eq!(options.raw_image_path(), None);
    }

    #[test]
    fn test_s3_archive_source_parsing() {
        let yaml = r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        metadata_path: "/path/to/metadata"
        copy_on_read: true
        stripe_source:
          source: archive
          type: s3
          bucket: backups
          prefix: images
          endpoint: https://account.r2.cloudflarestorage.com
          region: auto
          profile: r2
          credentials:
            access_key_id: "QUtJQUlBQUFBQUFBQQ=="
            secret_access_key: "c2VjcmV0S2V5MTIzNDU2"
        "#;

        let options = Options::load_from_str(yaml).unwrap();

        assert!(matches!(
            options.resolved_stripe_source(),
            Some(StripeSourceConfig::Archive { .. })
        ));
        assert_eq!(options.raw_image_path(), None);

        assert_eq!(
            options.stripe_source,
            Some(StripeSourceConfig::Archive {
                config: ArchiveStripeSourceConfig::S3 {
                    bucket: "backups".to_string(),
                    prefix: Some("images".to_string()),
                    endpoint: Some("https://account.r2.cloudflarestorage.com".to_string()),
                    profile: Some("r2".to_string()),
                    region: Some("auto".to_string()),
                    credentials: Some(AwsCredentials {
                        access_key_id: b"AKIAIAAAAAAAA".to_vec(),
                        secret_access_key: b"secretKey123456".to_vec(),
                    }),
                    connections: 16,
                    archive_kek: KeyEncryptionCipher::default(),
                }
            })
        );
    }

    #[test]
    fn test_archive_kek_decryption() {
        use aes_gcm::{
            aead::{Aead, KeyInit, Payload},
            Aes256Gcm, Nonce,
        };

        let kek_key = [0x11u8; 32];
        let iv = [0x22u8; 12];
        let aad = b"test-aad";
        let kek = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(kek_key.to_vec()),
            init_vector: Some(iv.to_vec()),
            auth_data: Some(aad.to_vec()),
        };

        let archive_key = [0x33u8; 32];
        let archive_iv = [0x44u8; 12];
        let archive_aad = b"archive-aad";

        let cipher = Aes256Gcm::new_from_slice(&kek_key).unwrap();
        let nonce = Nonce::from_slice(&iv);
        let enc_key = cipher
            .encrypt(
                nonce,
                Payload {
                    msg: &archive_key,
                    aad,
                },
            )
            .unwrap();
        let enc_iv = cipher
            .encrypt(
                nonce,
                Payload {
                    msg: &archive_iv,
                    aad,
                },
            )
            .unwrap();
        let enc_aad = cipher
            .encrypt(
                nonce,
                Payload {
                    msg: archive_aad,
                    aad,
                },
            )
            .unwrap();

        let yaml = format!(
            r#"
        path: "/path/to/disk"
        socket: "/path/to/socket"
        metadata_path: "/path/to/metadata"
        copy_on_read: true
        stripe_source:
          source: archive
          type: filesystem
          path: "/path/to/archive"
          archive_kek:
            method: aes256-gcm
            key: "{}"
            init_vector: "{}"
            auth_data: "{}"
        "#,
            STANDARD.encode(enc_key),
            STANDARD.encode(enc_iv),
            STANDARD.encode(enc_aad),
        );

        let options = Options::load_from_str_with_kek(&yaml, &kek).unwrap();
        let config = match options.resolved_stripe_source() {
            Some(StripeSourceConfig::Archive { config }) => config,
            _ => panic!("Expected archive stripe source"),
        };

        let archive_kek = config.archive_kek();
        assert_eq!(archive_kek.method, CipherMethod::Aes256Gcm);
        assert_eq!(archive_kek.key, Some(archive_key.to_vec()));
        assert_eq!(archive_kek.init_vector, Some(archive_iv.to_vec()));
        assert_eq!(archive_kek.auth_data, Some(archive_aad.to_vec()));
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

        let result = Options::load_from_str(yaml);
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
        let result = Options::load_from_str(yaml);
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
        let options = Options::load_from_str(yaml).unwrap();
        assert_eq!(
            options.resolved_stripe_source(),
            Some(StripeSourceConfig::Raw {
                path: PathBuf::from("/path/to/image")
            })
        );
        assert_eq!(
            options.raw_image_path(),
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
        let options = Options::load_from_str(yaml).unwrap();
        assert_eq!(
            options.resolved_stripe_source(),
            Some(StripeSourceConfig::Raw {
                path: PathBuf::from("/path/to/image")
            })
        );
        assert_eq!(
            options.raw_image_path(),
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

        let result = Options::load_from_str(yaml);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("metadata_path must be specified when using a stripe source"));
    }
}
