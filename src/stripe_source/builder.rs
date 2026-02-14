use log::info;
use ubiblk_macros::error_context;

use crate::{
    archive::{ArchiveStore, FileSystemStore, S3Store},
    backends::build_raw_image_device,
    block_device::NullBlockDevice,
    config::v2::{self, stripe_source::ArchiveStorageConfig},
    stripe_server::connect_to_stripe_server,
    utils::s3::{build_s3_client, create_runtime},
    CipherMethod, KeyEncryptionCipher, Result,
};

use super::*;

pub struct StripeSourceBuilder {
    device_config: v2::Config,
    stripe_sector_count: u64,
    has_fetched_all_stripes: bool,
}

impl StripeSourceBuilder {
    pub fn new(
        device_config: v2::Config,
        stripe_sector_count: u64,
        has_fetched_all_stripes: bool,
    ) -> Self {
        Self {
            device_config,
            stripe_sector_count,
            has_fetched_all_stripes,
        }
    }

    #[error_context("Failed to build stripe source")]
    pub fn build(&self) -> Result<Box<dyn StripeSource>> {
        // If already fetched all stripes, no need to build a real source
        if self.has_fetched_all_stripes {
            info!("All stripes have been fetched; using NullBlockDevice as stripe source");
            return Ok(Box::new(BlockDeviceStripeSource::new(
                NullBlockDevice::new(),
                self.stripe_sector_count,
            )?));
        }

        if let Some(stripe_source) = self.device_config.stripe_source.as_ref() {
            match stripe_source {
                v2::stripe_source::StripeSourceConfig::Archive(config) => {
                    let store = Self::build_archive_store(config, &self.device_config.secrets)?;
                    let stripe_source = ArchiveStripeSource::new(
                        store,
                        Self::build_archive_kek(config, &self.device_config.secrets)?,
                    )?;
                    return Ok(Box::new(stripe_source));
                }
                v2::stripe_source::StripeSourceConfig::Remote { .. } => {
                    let client =
                        connect_to_stripe_server(stripe_source, &self.device_config.secrets)?;
                    let stripe_source =
                        RemoteStripeSource::new(Box::new(client), self.stripe_sector_count)?;
                    return Ok(Box::new(stripe_source));
                }
                v2::stripe_source::StripeSourceConfig::Raw { .. } => {}
            }
        }

        let source_block_device =
            build_raw_image_device(&self.device_config)?.unwrap_or(NullBlockDevice::new());

        Ok(Box::new(BlockDeviceStripeSource::new(
            source_block_device,
            self.stripe_sector_count,
        )?))
    }

    fn build_aws_credentials(
        access_key_id: &v2::secrets::SecretRef,
        secret_access_key: &v2::secrets::SecretRef,
        secrets: &std::collections::HashMap<String, v2::secrets::ResolvedSecret>,
    ) -> Result<Option<aws_sdk_s3::config::Credentials>> {
        let access_key_id = String::from_utf8(
            secrets
                .get(access_key_id.id())
                .ok_or_else(|| {
                    crate::ubiblk_error!(InvalidParameter {
                        description: format!(
                            "AWS access_key_id secret '{}' not found",
                            access_key_id.id()
                        ),
                    })
                })?
                .as_bytes()
                .to_vec(),
        )
        .map_err(|e| {
            crate::ubiblk_error!(InvalidParameter {
                description: format!("AWS access_key_id is not valid UTF-8: {e}"),
            })
        })?;
        let secret_access_key = String::from_utf8(
            secrets
                .get(secret_access_key.id())
                .ok_or_else(|| {
                    crate::ubiblk_error!(InvalidParameter {
                        description: format!(
                            "AWS secret_access_key secret '{}' not found",
                            secret_access_key.id()
                        ),
                    })
                })?
                .as_bytes()
                .to_vec(),
        )
        .map_err(|e| {
            crate::ubiblk_error!(InvalidParameter {
                description: format!("AWS secret_access_key is not valid UTF-8: {e}"),
            })
        })?;

        Ok(Some(
            aws_sdk_s3::config::Credentials::builder()
                .access_key_id(access_key_id)
                .secret_access_key(secret_access_key)
                .provider_name("ubiblk_archive")
                .build(),
        ))
    }

    pub fn build_archive_kek(
        config: &ArchiveStorageConfig,
        secrets: &std::collections::HashMap<String, v2::secrets::ResolvedSecret>,
    ) -> Result<KeyEncryptionCipher> {
        let archive_kek = match config {
            ArchiveStorageConfig::Filesystem { archive_kek, .. } => archive_kek,
            ArchiveStorageConfig::S3 { archive_kek, .. } => archive_kek,
        };
        let key = secrets
            .get(archive_kek.id())
            .ok_or_else(|| {
                crate::ubiblk_error!(InvalidParameter {
                    description: format!("Archive KEK secret '{}' not found", archive_kek.id()),
                })
            })?
            .as_bytes()
            .to_vec();
        Ok(KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(key),
            auth_data: Some(b"ubiblk_archive".to_vec()),
        })
    }

    pub fn build_archive_store(
        config: &ArchiveStorageConfig,
        secrets: &std::collections::HashMap<String, v2::secrets::ResolvedSecret>,
    ) -> Result<Box<dyn ArchiveStore>> {
        match config {
            ArchiveStorageConfig::Filesystem { path, .. } => {
                Ok(Box::new(FileSystemStore::new(path.into())?))
            }
            ArchiveStorageConfig::S3 {
                bucket,
                prefix,
                region,
                access_key_id,
                secret_access_key,
                connections,
                endpoint,
                ..
            } => {
                let decrypted_credentials =
                    Self::build_aws_credentials(access_key_id, secret_access_key, secrets)?;
                let runtime = create_runtime()?;
                let client = build_s3_client(
                    &runtime,
                    None,
                    endpoint.as_deref(),
                    region.as_deref(),
                    decrypted_credentials,
                )?;

                Ok(Box::new(S3Store::new(
                    client,
                    bucket.to_string(),
                    prefix.clone(),
                    *connections,
                )?))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::v2::stripe_source::StripeSourceConfig;
    use crate::config::v2::DeviceSection;
    use std::fs::File;
    use std::path::PathBuf;
    use tempfile::tempdir;

    fn create_test_config(remote: Option<String>, path: Option<PathBuf>) -> v2::Config {
        let stripe_source = path
            .map(|path| StripeSourceConfig::Raw {
                image_path: path,
                autofetch: false,
                copy_on_read: false,
            })
            .or_else(|| {
                remote.map(|remote| StripeSourceConfig::Remote {
                    address: remote,
                    psk: None,
                    autofetch: false,
                })
            });

        v2::Config {
            device: DeviceSection {
                data_path: "/tmp/non-existent-disk".into(),
                metadata_path: None,
                vhost_socket: None,
                rpc_socket: None,
                device_id: "ubiblk".to_string(),
                track_written: false,
            },
            tuning: v2::tuning::TuningSection {
                queue_size: 64,
                ..Default::default()
            },
            encryption: None,
            danger_zone: v2::DangerZone {
                enabled: true,
                allow_unencrypted_disk: true,
                allow_inline_plaintext_secrets: true,
                allow_secret_over_regular_file: true,
                allow_unencrypted_connection: true,
            },
            stripe_source,
            secrets: std::collections::HashMap::new(),
        }
    }

    #[test]
    fn test_build_defaults_to_null_device() {
        let config = create_test_config(None, None);
        let builder = StripeSourceBuilder::new(config, 4096, false);

        let result = builder.build();

        assert!(
            result.is_ok(),
            "Should successfully build a NullBlockDevice source when no paths provided"
        );
    }

    #[test]
    fn test_build_local_block_device() {
        let temp_dir = tempdir().unwrap();
        let file_path = temp_dir.path().join("test.img");

        // Create a dummy 1MB file so build_block_device succeeds
        let f = File::create(&file_path).unwrap();
        f.set_len(1024 * 1024).unwrap();

        let config = create_test_config(None, Some(file_path));
        let builder = StripeSourceBuilder::new(config, 4096, false);

        let result = builder.build();
        assert!(
            result.is_ok(),
            "Should successfully build a BlockDeviceStripeSource with valid image_path"
        );
    }

    #[test]
    fn test_build_local_block_device_fails_on_missing_file() {
        let bad_path = PathBuf::from("/path/to/nonexistent/file.img");
        let config = create_test_config(None, Some(bad_path));
        let builder = StripeSourceBuilder::new(config, 4096, false);

        let result = builder.build();

        assert!(result.is_err());
        let err_msg = format!("{:?}", result.err().unwrap());
        assert!(
            err_msg.to_lowercase().contains("not found")
                || err_msg.to_lowercase().contains("no such file"),
            "Should return file not found error. Got: {}",
            err_msg
        );
    }

    #[test]
    fn test_connect_to_invalid_remote_server() {
        let config = create_test_config(Some("127.0.0.1:99999".to_string()), None);
        let builder = StripeSourceBuilder::new(config, 4096, false);

        let result = builder.build();

        assert!(
            result.is_err(),
            "Should fail to connect to invalid remote server"
        );
    }

    #[test]
    fn test_skips_building_real_source_when_all_stripes_fetched() {
        let config = create_test_config(None, None);
        let builder = StripeSourceBuilder::new(config, 4096, true);

        let result = builder.build();
        assert!(
            result.is_ok(),
            "Should successfully build a NullBlockDevice source when all stripes fetched"
        );

        let stripe_source = result.unwrap();
        // NullBlockDevice has sector_count of 0
        assert_eq!(stripe_source.sector_count(), 0);
    }
}
