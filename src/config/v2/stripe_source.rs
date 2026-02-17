use std::{
    collections::HashMap,
    path::{Component, Path, PathBuf},
};

use serde::Deserialize;

use super::{secrets::SecretRef, DangerZone};
use crate::{
    config::v2::{
        load::resolve_path,
        secrets::{get_resolved_secret, ResolvedSecret},
    },
    ubiblk_error, Result,
};

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
    Remote(RemoteStripeConfig),
}

impl StripeSourceConfig {
    pub fn autofetch(&self) -> bool {
        match self {
            StripeSourceConfig::Raw { autofetch, .. } => *autofetch,
            StripeSourceConfig::Archive(ArchiveStorageConfig::Filesystem { autofetch, .. }) => {
                *autofetch
            }
            StripeSourceConfig::Archive(ArchiveStorageConfig::S3 { autofetch, .. }) => *autofetch,
            StripeSourceConfig::Remote(RemoteStripeConfig { autofetch, .. }) => *autofetch,
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

    pub fn resolve_paths(&mut self, config_dir: &Path) {
        match self {
            StripeSourceConfig::Raw { image_path, .. } => {
                *image_path = resolve_path(image_path.clone(), config_dir);
            }
            StripeSourceConfig::Archive(ArchiveStorageConfig::Filesystem { path, .. }) => {
                *path = resolve_path(path.clone(), config_dir);
            }
            _ => {}
        }
    }

    pub fn validate(
        &self,
        danger_zone: &DangerZone,
        resolved_secrets: &HashMap<String, ResolvedSecret>,
    ) -> Result<()> {
        match self {
            StripeSourceConfig::Remote(config) => {
                config.validate(danger_zone, resolved_secrets)?;
            }
            StripeSourceConfig::Archive(storage) => storage.validate(resolved_secrets)?,
            StripeSourceConfig::Raw { .. } => (),
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct RemoteStripeConfig {
    pub address: String,
    pub psk: Option<PskConfig>,
    #[serde(default)]
    pub autofetch: bool,
}

impl RemoteStripeConfig {
    pub fn validate(
        &self,
        danger_zone: &DangerZone,
        resolved_secrets: &HashMap<String, ResolvedSecret>,
    ) -> Result<()> {
        if self.psk.is_none() && !(danger_zone.enabled && danger_zone.allow_unencrypted_connection)
        {
            return Err(ubiblk_error!(
                InvalidParameter {
                    description: "Remote stripe source requires PSK unless danger_zone.allow_unencrypted_connection is enabled".to_string()
                }
            ));
        }
        if let Some(psk) = &self.psk {
            Self::validate_psk_secret(get_resolved_secret(&psk.secret, resolved_secrets)?)?;
        }
        Ok(())
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
}

#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(tag = "storage", rename_all = "snake_case", deny_unknown_fields)]
pub enum ArchiveStorageConfig {
    Filesystem {
        path: PathBuf,
        archive_kek: Option<SecretRef>,
        #[serde(default)]
        autofetch: bool,
    },
    S3 {
        bucket: String,
        #[serde(default)]
        prefix: Option<String>,
        region: Option<String>,
        access_key_id: SecretRef,
        secret_access_key: SecretRef,
        #[serde(default)]
        session_token: Option<SecretRef>,
        endpoint: Option<String>,
        #[serde(default = "default_connections")]
        connections: usize,
        archive_kek: Option<SecretRef>,
        #[serde(default)]
        autofetch: bool,
    },
}

fn default_connections() -> usize {
    16
}

impl ArchiveStorageConfig {
    pub fn validate(&self, resolved_secrets: &HashMap<String, ResolvedSecret>) -> Result<()> {
        match self {
            ArchiveStorageConfig::Filesystem { archive_kek, .. } => {
                if let Some(archive_kek) = archive_kek {
                    Self::validate_archive_kek(get_resolved_secret(archive_kek, resolved_secrets)?)
                } else {
                    Ok(())
                }
            }
            ArchiveStorageConfig::S3 {
                prefix,
                connections,
                access_key_id,
                secret_access_key,
                session_token,
                archive_kek,
                ..
            } => {
                if let Some(archive_kek) = archive_kek {
                    Self::validate_archive_kek(get_resolved_secret(
                        archive_kek,
                        resolved_secrets,
                    )?)?;
                }
                Self::validate_aws_access_key_id(get_resolved_secret(
                    access_key_id,
                    resolved_secrets,
                )?)?;
                Self::validate_aws_secret_access_key(get_resolved_secret(
                    secret_access_key,
                    resolved_secrets,
                )?)?;
                if let Some(session_token) = session_token {
                    Self::validate_aws_session_token(get_resolved_secret(
                        session_token,
                        resolved_secrets,
                    )?)?;
                }
                Self::validate_prefix(prefix)?;
                Self::validate_connections(connections)
            }
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

    fn validate_connections(connections: &usize) -> crate::Result<()> {
        if *connections == 0 {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: "S3 connections must be greater than 0".to_string(),
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

    fn validate_aws_session_token(session_token: &ResolvedSecret) -> Result<()> {
        if session_token.as_bytes().is_empty() {
            return Err(ubiblk_error!(InvalidParameter {
                description: "AWS session_token cannot be empty".to_string(),
            }));
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct PskConfig {
    pub identity: String,
    pub secret: SecretRef,
}

#[cfg(test)]
mod tests {
    use crate::config::v2::secrets::{resolve_secrets, SecretDef, SecretEncoding, SecretSource};

    use super::*;
    use base64::{engine::general_purpose::STANDARD as b64_engine, Engine};

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
                archive_kek: Some(SecretRef::Ref("archive-kek".to_string())),
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
            session_token.ref = "aws-session-token"
            archive_kek.ref = "archive-kek"
            autofetch = false
        "#;
        let config: StripeSourceConfig = toml::from_str(toml).unwrap();
        assert_eq!(
            config,
            StripeSourceConfig::Archive(ArchiveStorageConfig::S3 {
                bucket: "encrypted-stripes".to_string(),
                prefix: Some("v1/".to_string()),
                region: Some("eu-west-1".to_string()),
                access_key_id: SecretRef::Ref("aws-access-key-id".to_string()),
                secret_access_key: SecretRef::Ref("aws-secret-access-key".to_string()),
                session_token: Some(SecretRef::Ref("aws-session-token".to_string())),
                archive_kek: Some(SecretRef::Ref("archive-kek".to_string())),
                autofetch: false,
                connections: 16,
                endpoint: None,
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
                region: Some("eu-west-1".to_string()),
                access_key_id: SecretRef::Ref("aws-access-key-id".to_string()),
                secret_access_key: SecretRef::Ref("aws-secret-access-key".to_string()),
                session_token: None,
                archive_kek: Some(SecretRef::Ref("archive-kek".to_string())),
                autofetch: false,
                connections: 16,
                endpoint: None,
            })
        );
    }

    #[test]
    fn remote_stripe_source() {
        let toml = r#"
            type = "remote"
            address = "1.2.3.4:4555"
            psk.identity = "client1"
            psk.secret.ref = "psk-secret"
            autofetch = false
        "#;
        let config: StripeSourceConfig = toml::from_str(toml).unwrap();
        assert_eq!(
            config,
            StripeSourceConfig::Remote(RemoteStripeConfig {
                address: "1.2.3.4:4555".to_string(),
                psk: Some(PskConfig {
                    identity: "client1".to_string(),
                    secret: SecretRef::Ref("psk-secret".to_string()),
                }),
                autofetch: false,
            })
        );
    }

    #[test]
    fn remote_autofetch_default() {
        let toml = r#"
            type = "remote"
            address = "1.2.3.4:4555"
            psk.identity = "client1"
            psk.secret.ref = "psk-secret"
        "#;
        let config: StripeSourceConfig = toml::from_str(toml).unwrap();
        assert_eq!(
            config,
            StripeSourceConfig::Remote(RemoteStripeConfig {
                address: "1.2.3.4:4555".to_string(),
                psk: Some(PskConfig {
                    identity: "client1".to_string(),
                    secret: SecretRef::Ref("psk-secret".to_string()),
                }),
                autofetch: false,
            })
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
                session_token,
                ..
            }) => {
                assert_eq!(access_key_id, SecretRef::Ref("my-access-key".to_string()));
                assert_eq!(
                    secret_access_key,
                    SecretRef::Ref("my-secret-key".to_string())
                );
                assert_eq!(archive_kek, Some(SecretRef::Ref("my-kek".to_string())));
                assert_eq!(session_token, None);
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
            psk.identity = "client1"
            psk.secret.ref = "psk"
        "#;
        let result = toml::from_str::<StripeSourceConfig>(toml);
        assert!(result.is_err());
        let error_msg = result.err().unwrap().to_string();
        assert!(error_msg.contains("missing field `address`"));
    }

    #[test]
    fn remote_partial_psk_rejected() {
        let toml_identity_only = r#"
            type = "remote"
            address = "127.0.0.1:1234"
            psk.identity = "client1"
        "#;
        let result = toml::from_str::<StripeSourceConfig>(toml_identity_only);
        let error_msg = result.err().unwrap().to_string();
        assert!(error_msg.contains("missing field `secret`"));
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
        let config = StripeSourceConfig::Remote(RemoteStripeConfig {
            address: "127.0.0.1:1234".to_string(),
            psk: None,
            autofetch: false,
        });
        let danger_zone = DangerZone {
            enabled: false,
            ..Default::default()
        };
        let result = config.validate(&danger_zone, &HashMap::new());
        assert!(result.is_err());
        let error_msg = result.err().unwrap().to_string();
        assert!(error_msg.contains("Remote stripe source requires PSK unless danger_zone.allow_unencrypted_connection is enabled"));

        let danger_zone_enabled = DangerZone {
            enabled: true,
            allow_unencrypted_connection: true,
            ..Default::default()
        };
        let result_enabled = config.validate(&danger_zone_enabled, &HashMap::new());
        assert!(result_enabled.is_ok());
    }

    fn valid_s3_secrets() -> HashMap<String, ResolvedSecret> {
        let secret_defs = HashMap::from([
            (
                "key".to_string(),
                SecretDef {
                    source: SecretSource::Inline(
                        b64_engine.encode("AKIA1234567890123456".as_bytes()),
                    ),
                    kek: None,
                    encoding: SecretEncoding::Base64,
                },
            ),
            (
                "secret".to_string(),
                SecretDef {
                    source: SecretSource::Inline(b64_engine.encode("super-secret-key")),
                    kek: None,
                    encoding: SecretEncoding::Base64,
                },
            ),
            (
                "kek".to_string(),
                SecretDef {
                    source: SecretSource::Inline(
                        b64_engine.encode("0123456789abcdef0123456789abcdef"),
                    ),
                    kek: None,
                    encoding: SecretEncoding::Base64,
                },
            ),
        ]);

        resolve_secrets(
            &secret_defs,
            &DangerZone {
                enabled: true,
                allow_inline_plaintext_secrets: true,
                ..Default::default()
            },
        )
        .unwrap()
    }

    #[test]
    fn validate_rejects_invalid_s3_prefix() {
        let config = StripeSourceConfig::Archive(ArchiveStorageConfig::S3 {
            bucket: "bucket".to_string(),
            prefix: Some("valid/../invalid/.".to_string()),
            region: Some("us-east-1".to_string()),
            access_key_id: SecretRef::Ref("key".to_string()),
            secret_access_key: SecretRef::Ref("secret".to_string()),
            session_token: None,
            archive_kek: Some(SecretRef::Ref("kek".to_string())),
            autofetch: false,
            connections: 16,
            endpoint: None,
        });
        let danger_zone = DangerZone::default();
        let result = config.validate(&danger_zone, &valid_s3_secrets());
        assert!(result.is_err());
        let error_msg = result.err().unwrap().to_string();
        assert!(error_msg.contains("Invalid S3 prefix (contains . or .. components)"));
    }

    #[test]
    fn validate_rejects_empty_s3_session_token() {
        let mut secrets = valid_s3_secrets();
        let empty_defs = HashMap::from([(
            "session".to_string(),
            SecretDef {
                source: SecretSource::Inline(b64_engine.encode("".as_bytes())),
                kek: None,
                encoding: SecretEncoding::Base64,
            },
        )]);
        secrets.extend(
            resolve_secrets(
                &empty_defs,
                &DangerZone {
                    enabled: true,
                    allow_inline_plaintext_secrets: true,
                    ..Default::default()
                },
            )
            .unwrap(),
        );

        let config = StripeSourceConfig::Archive(ArchiveStorageConfig::S3 {
            bucket: "bucket".to_string(),
            prefix: None,
            region: Some("us-east-1".to_string()),
            access_key_id: SecretRef::Ref("key".to_string()),
            secret_access_key: SecretRef::Ref("secret".to_string()),
            session_token: Some(SecretRef::Ref("session".to_string())),
            archive_kek: Some(SecretRef::Ref("kek".to_string())),
            autofetch: false,
            connections: 16,
            endpoint: None,
        });

        let result = config.validate(&DangerZone::default(), &secrets);
        assert!(result.is_err());
        let error_msg = result.err().unwrap().to_string();
        assert!(error_msg.contains("AWS session_token cannot be empty"));
    }

    #[test]
    fn validate_rejects_invalid_s3_connections() {
        let config = StripeSourceConfig::Archive(ArchiveStorageConfig::S3 {
            bucket: "bucket".to_string(),
            prefix: None,
            region: Some("us-east-1".to_string()),
            access_key_id: SecretRef::Ref("key".to_string()),
            secret_access_key: SecretRef::Ref("secret".to_string()),
            session_token: None,
            archive_kek: Some(SecretRef::Ref("kek".to_string())),
            autofetch: false,
            connections: 0,
            endpoint: None,
        });
        let danger_zone = DangerZone::default();
        let result = config.validate(&danger_zone, &valid_s3_secrets());
        assert!(result.is_err());
        let error_msg = result.err().unwrap().to_string();
        assert!(error_msg.contains("S3 connections must be greater than 0"));
    }
}
