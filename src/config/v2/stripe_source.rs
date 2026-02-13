use std::{
    collections::HashMap,
    path::{Component, Path, PathBuf},
};

use serde::Deserialize;

use super::{secrets::SecretRef, DangerZone};
use crate::{config::v2::secrets::ResolvedSecret, ubiblk_error, Result};

/// Stripe source configuration for TOML format.
///
/// Discriminated by `type` field: "raw", "archive", or "remote".
/// Archive sources have a second discriminator `storage`: "filesystem" or "s3".
#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(tag = "type", rename_all = "snake_case", deny_unknown_fields)]
pub enum StripeSourceConfig {
    Raw {
        image_path: PathBuf,
        #[serde(default)]
        autofetch: bool,
        #[serde(default)]
        copy_on_read: bool,
    },
    Archive(ArchiveStorageConfig),
    Remote {
        address: String,
        #[serde(flatten)]
        psk: Option<PskConfig>,
        #[serde(default)]
        autofetch: bool,
    },
}

impl StripeSourceConfig {
    pub fn autofetch(&self) -> bool {
        match self {
            StripeSourceConfig::Raw { autofetch, .. } => *autofetch,
            StripeSourceConfig::Archive(ArchiveStorageConfig::Filesystem { autofetch, .. }) => {
                *autofetch
            }
            StripeSourceConfig::Archive(ArchiveStorageConfig::S3 { autofetch, .. }) => *autofetch,
            StripeSourceConfig::Remote { autofetch, .. } => *autofetch,
        }
    }

    pub fn copy_on_read(&self) -> bool {
        match self {
            StripeSourceConfig::Raw { copy_on_read, .. } => *copy_on_read,
            _ => true, // archive and remote always use copy_on_read semantics
        }
    }

    pub fn raw_image_path(&self) -> Option<&Path> {
        match self {
            StripeSourceConfig::Raw { image_path, .. } => Some(image_path),
            _ => None,
        }
    }

    pub fn validate(&self, danger_zone: &DangerZone) -> Result<()> {
        match self {
            StripeSourceConfig::Remote { psk, .. } => {
                if psk.is_none()
                    && !(danger_zone.enabled && danger_zone.allow_unencrypted_connection)
                {
                    return Err(ubiblk_error!(
                                InvalidParameter {
                                   description: "Remote stripe source requires PSK unless danger_zone.allow_unencrypted_connection is enabled".to_string()
                           }));
                }
            }
            StripeSourceConfig::Archive(storage) => storage.validate()?,
            StripeSourceConfig::Raw { .. } => (),
        }
        Ok(())
    }

    pub fn validate_secrets(&self, secret_defs: &HashMap<String, ResolvedSecret>) -> Result<()> {
        match self {
            StripeSourceConfig::Remote { psk, .. } => {
                if let Some(psk) = psk {
                    validate_psk_secret(self.get_secret(&psk.psk_secret, secret_defs)?)?;
                }
            }
            StripeSourceConfig::Archive(ArchiveStorageConfig::Filesystem {
                archive_kek, ..
            }) => {
                validate_archive_kek(self.get_secret(archive_kek, secret_defs)?)?;
            }
            StripeSourceConfig::Archive(ArchiveStorageConfig::S3 {
                access_key_id,
                secret_access_key,
                archive_kek,
                ..
            }) => {
                validate_archive_kek(self.get_secret(archive_kek, secret_defs)?)?;
                validate_aws_access_key_id(self.get_secret(access_key_id, secret_defs)?)?;
                validate_aws_secret_access_key(self.get_secret(secret_access_key, secret_defs)?)?;
            }
            StripeSourceConfig::Raw { .. } => (),
        }
        Ok(())
    }

    fn get_secret<'a>(
        &'a self,
        secret_ref: &SecretRef,
        secret_defs: &'a HashMap<String, ResolvedSecret>,
    ) -> Result<&'a ResolvedSecret> {
        let secret_id = secret_ref.id();
        secret_defs.get(secret_id).ok_or_else(|| {
            ubiblk_error!(InvalidParameter {
                description: format!(
                    "Secret reference '{}' not found in configuration",
                    secret_id
                ),
            })
        })
    }
}

fn validate_psk_secret(secret: &ResolvedSecret) -> Result<()> {
    if secret.as_bytes().len() < 16 {
        return Err(ubiblk_error!(InvalidParameter {
            description: format!(
                "PSK secret must be at least 16 bytes (got {} bytes)",
                secret.as_bytes().len()
            ),
        }));
    }
    Ok(())
}

fn validate_archive_kek(archive_kek_secret: &ResolvedSecret) -> Result<()> {
    if archive_kek_secret.as_bytes().len() != 32 {
        return Err(ubiblk_error!(InvalidParameter {
            description: format!(
                "Archive KEK secret must be exactly 32 bytes for AES-256-GCM (got {} bytes)",
                archive_kek_secret.as_bytes().len()
            ),
        }));
    }
    Ok(())
}

fn validate_aws_secret_access_key(secret_key: &ResolvedSecret) -> Result<()> {
    if secret_key.as_bytes().is_empty() {
        return Err(ubiblk_error!(InvalidParameter {
            description: "AWS secret_access_key cannot be empty".to_string(),
        }));
    }
    Ok(())
}

fn validate_aws_access_key_id(access_key_id: &ResolvedSecret) -> Result<()> {
    if access_key_id.as_bytes().is_empty() {
        return Err(ubiblk_error!(InvalidParameter {
            description: "AWS access_key_id cannot be empty".to_string(),
        }));
    }
    Ok(())
}

#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(tag = "storage", rename_all = "snake_case", deny_unknown_fields)]
pub enum ArchiveStorageConfig {
    Filesystem {
        path: PathBuf,
        archive_kek: SecretRef,
        #[serde(default)]
        autofetch: bool,
    },
    S3 {
        bucket: String,
        #[serde(default)]
        prefix: Option<String>,
        region: String,
        access_key_id: SecretRef,
        secret_access_key: SecretRef,
        archive_kek: SecretRef,
        #[serde(default)]
        autofetch: bool,
    },
}

impl ArchiveStorageConfig {
    pub fn validate(&self) -> Result<()> {
        match self {
            ArchiveStorageConfig::Filesystem { .. } => Ok(()),
            ArchiveStorageConfig::S3 { prefix, .. } => Self::validate_prefix(prefix),
        }
    }

    fn validate_prefix(prefix: &Option<String>) -> crate::Result<()> {
        if let Some(p) = prefix {
            if Path::new(p)
                .components()
                .any(|c| matches!(c, Component::CurDir | Component::ParentDir))
            {
                return Err(crate::ubiblk_error!(InvalidParameter {
                    description: format!("Invalid S3 prefix (contains . or .. components): {}", p),
                }));
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Deserialize, PartialEq)]
pub struct PskConfig {
    pub psk_identity: String,
    pub psk_secret: SecretRef,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn raw_stripe_source() {
        let toml = r#"
            type = "raw"
            image_path = "/path/to/image.raw"
            autofetch = false
            copy_on_read = false
        "#;
        let config: StripeSourceConfig = toml::from_str(toml).unwrap();
        assert_eq!(
            config,
            StripeSourceConfig::Raw {
                image_path: PathBuf::from("/path/to/image.raw"),
                autofetch: false,
                copy_on_read: false,
            }
        );
    }

    #[test]
    fn raw_stripe_source_defaults() {
        let toml = r#"
            type = "raw"
            image_path = "/path/to/image.raw"
        "#;
        let config: StripeSourceConfig = toml::from_str(toml).unwrap();
        assert_eq!(
            config,
            StripeSourceConfig::Raw {
                image_path: PathBuf::from("/path/to/image.raw"),
                autofetch: false,
                copy_on_read: false,
            }
        );
    }

    #[test]
    fn archive_filesystem() {
        let toml = r#"
            type = "archive"
            storage = "filesystem"
            path = "/path/to/archive/root"
            archive_kek.ref = "archive-kek"
            autofetch = false
        "#;
        let config: StripeSourceConfig = toml::from_str(toml).unwrap();
        assert_eq!(
            config,
            StripeSourceConfig::Archive(ArchiveStorageConfig::Filesystem {
                path: PathBuf::from("/path/to/archive/root"),
                archive_kek: SecretRef::Ref("archive-kek".to_string()),
                autofetch: false,
            })
        );
    }

    #[test]
    fn archive_s3() {
        let toml = r#"
            type = "archive"
            storage = "s3"
            bucket = "encrypted-stripes"
            prefix = "v1/"
            region = "eu-west-1"
            access_key_id.ref = "aws-access-key-id"
            secret_access_key.ref = "aws-secret-access-key"
            archive_kek.ref = "archive-kek"
            autofetch = false
        "#;
        let config: StripeSourceConfig = toml::from_str(toml).unwrap();
        assert_eq!(
            config,
            StripeSourceConfig::Archive(ArchiveStorageConfig::S3 {
                bucket: "encrypted-stripes".to_string(),
                prefix: Some("v1/".to_string()),
                region: "eu-west-1".to_string(),
                access_key_id: SecretRef::Ref("aws-access-key-id".to_string()),
                secret_access_key: SecretRef::Ref("aws-secret-access-key".to_string()),
                archive_kek: SecretRef::Ref("archive-kek".to_string()),
                autofetch: false,
            })
        );
    }

    #[test]
    fn archive_s3_optional_prefix() {
        let toml = r#"
            type = "archive"
            storage = "s3"
            bucket = "encrypted-stripes"
            region = "eu-west-1"
            access_key_id.ref = "aws-access-key-id"
            secret_access_key.ref = "aws-secret-access-key"
            archive_kek.ref = "archive-kek"
        "#;
        let config: StripeSourceConfig = toml::from_str(toml).unwrap();
        assert_eq!(
            config,
            StripeSourceConfig::Archive(ArchiveStorageConfig::S3 {
                bucket: "encrypted-stripes".to_string(),
                prefix: None,
                region: "eu-west-1".to_string(),
                access_key_id: SecretRef::Ref("aws-access-key-id".to_string()),
                secret_access_key: SecretRef::Ref("aws-secret-access-key".to_string()),
                archive_kek: SecretRef::Ref("archive-kek".to_string()),
                autofetch: false,
            })
        );
    }

    #[test]
    fn remote_stripe_source() {
        let toml = r#"
            type = "remote"
            address = "1.2.3.4:4555"
            psk_identity = "client1"
            psk_secret.ref = "psk-secret"
            autofetch = false
        "#;
        let config: StripeSourceConfig = toml::from_str(toml).unwrap();
        assert_eq!(
            config,
            StripeSourceConfig::Remote {
                address: "1.2.3.4:4555".to_string(),
                psk: Some(PskConfig {
                    psk_identity: "client1".to_string(),
                    psk_secret: SecretRef::Ref("psk-secret".to_string()),
                }),
                autofetch: false,
            }
        );
    }

    #[test]
    fn remote_autofetch_default() {
        let toml = r#"
            type = "remote"
            address = "1.2.3.4:4555"
            psk_identity = "client1"
            psk_secret.ref = "psk-secret"
        "#;
        let config: StripeSourceConfig = toml::from_str(toml).unwrap();
        assert_eq!(
            config,
            StripeSourceConfig::Remote {
                address: "1.2.3.4:4555".to_string(),
                psk: Some(PskConfig {
                    psk_identity: "client1".to_string(),
                    psk_secret: SecretRef::Ref("psk-secret".to_string()),
                }),
                autofetch: false,
            }
        );
    }

    // --- Secret fields store raw ref: strings ---

    #[test]
    fn secret_fields_store_raw_ref_strings() {
        let toml = r#"
            type = "archive"
            storage = "s3"
            bucket = "bucket"
            region = "us-east-1"
            access_key_id.ref = "my-access-key"
            secret_access_key.ref = "my-secret-key"
            archive_kek.ref = "my-kek"
        "#;
        let config: StripeSourceConfig = toml::from_str(toml).unwrap();
        match config {
            StripeSourceConfig::Archive(ArchiveStorageConfig::S3 {
                access_key_id,
                secret_access_key,
                archive_kek,
                ..
            }) => {
                assert_eq!(access_key_id, SecretRef::Ref("my-access-key".to_string()));
                assert_eq!(
                    secret_access_key,
                    SecretRef::Ref("my-secret-key".to_string())
                );
                assert_eq!(archive_kek, SecretRef::Ref("my-kek".to_string()));
            }
            _ => panic!("expected archive s3"),
        }
    }

    #[test]
    fn unknown_type_rejected() {
        let toml = r#"
            type = "ftp"
            path = "/something"
        "#;
        let result = toml::from_str::<StripeSourceConfig>(toml);
        assert!(result.is_err());
    }

    #[test]
    fn archive_missing_storage_rejected() {
        let toml = r#"
            type = "archive"
            path = "/path"
            archive_kek = "ref:kek"
        "#;
        let result = toml::from_str::<StripeSourceConfig>(toml);
        assert!(result.is_err());
    }

    #[test]
    fn archive_unknown_storage_rejected() {
        let toml = r#"
            type = "archive"
            storage = "gcs"
            bucket = "bucket"
        "#;
        let result = toml::from_str::<StripeSourceConfig>(toml);
        assert!(result.is_err());
    }

    #[test]
    fn raw_missing_image_path_rejected() {
        let toml = r#"
            type = "raw"
        "#;
        let result = toml::from_str::<StripeSourceConfig>(toml);
        assert!(result.is_err());
    }

    #[test]
    fn remote_missing_address_rejected() {
        let toml = r#"
            type = "remote"
            psk_identity = "client1"
            psk_secret.ref = "psk"
        "#;
        let result = toml::from_str::<StripeSourceConfig>(toml);
        assert!(result.is_err());
    }

    #[test]
    fn raw_rejects_unknown_field() {
        let toml = r#"
            type = "raw"
            image_path = "/path"
            extra_field = "bad"
        "#;
        let result = toml::from_str::<StripeSourceConfig>(toml);
        assert!(result.is_err());
    }

    #[test]
    fn s3_missing_required_field_rejected() {
        let toml = r#"
            type = "archive"
            storage = "s3"
            bucket = "bucket"
            region = "us-east-1"
            access_key_id.ref = "key"
            archive_kek.ref = "kek"
        "#;
        let result = toml::from_str::<StripeSourceConfig>(toml);
        assert!(result.is_err(), "should reject missing secret_access_key");
    }

    #[test]
    fn deserialize_from_stripe_source_table() {
        let toml = r#"
            [stripe_source]
            type = "raw"
            image_path = "/path/to/image.raw"
        "#;

        #[derive(Deserialize)]
        struct Wrapper {
            stripe_source: StripeSourceConfig,
        }

        let wrapper: Wrapper = toml::from_str(toml).unwrap();
        assert_eq!(
            wrapper.stripe_source,
            StripeSourceConfig::Raw {
                image_path: PathBuf::from("/path/to/image.raw"),
                autofetch: false,
                copy_on_read: false,
            }
        );
    }

    #[test]
    fn validate_rejects_remote_without_psk_when_danger_zone_disabled() {
        let config = StripeSourceConfig::Remote {
            address: "127.0.0.1:1234".to_string(),
            psk: None,
            autofetch: false,
        };
        let danger_zone = DangerZone {
            enabled: false,
            ..Default::default()
        };
        let result = config.validate(&danger_zone);
        assert!(result.is_err());
        let error_msg = result.err().unwrap().to_string();
        assert!(error_msg.contains("Remote stripe source requires PSK unless danger_zone.allow_unencrypted_connection is enabled"));

        let danger_zone_enabled = DangerZone {
            enabled: true,
            allow_unencrypted_connection: true,
            ..Default::default()
        };
        let result_enabled = config.validate(&danger_zone_enabled);
        assert!(result_enabled.is_ok());
    }

    #[test]
    fn validate_rejects_invalid_s3_prefix() {
        let config = StripeSourceConfig::Archive(ArchiveStorageConfig::S3 {
            bucket: "bucket".to_string(),
            prefix: Some("valid/../invalid/.".to_string()),
            region: "us-east-1".to_string(),
            access_key_id: SecretRef::Ref("key".to_string()),
            secret_access_key: SecretRef::Ref("secret".to_string()),
            archive_kek: SecretRef::Ref("kek".to_string()),
            autofetch: false,
        });
        let danger_zone = DangerZone::default();
        let result = config.validate(&danger_zone);
        assert!(result.is_err());
        let error_msg = result.err().unwrap().to_string();
        assert!(error_msg.contains("Invalid S3 prefix (contains . or .. components)"));
    }
}
