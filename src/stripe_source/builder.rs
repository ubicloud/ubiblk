use crate::{
    archive::{ArchiveStore, FileSystemStore, S3Store},
    stripe_server::{connect_to_stripe_server, PskCredentials, StripeServerClient},
    utils::s3::{build_s3_client, create_runtime},
    vhost_backend::{build_source_device, ArchiveStripeSourceConfig, AwsCredentials, Options},
    KeyEncryptionCipher, Result,
};

use super::*;

pub struct StripeSourceBuilder {
    options: Options,
    kek: KeyEncryptionCipher,
    stripe_sector_count: u64,
}

impl StripeSourceBuilder {
    pub fn new(options: Options, kek: KeyEncryptionCipher, stripe_sector_count: u64) -> Self {
        Self {
            options,
            kek,
            stripe_sector_count,
        }
    }

    pub fn build(&self) -> Result<Box<dyn StripeSource>> {
        if let Some(archive_source) = &self.options.archive_stripe_source {
            let store = Self::build_archive_store(archive_source, &self.kek)?;
            let stripe_source = ArchiveStripeSource::new(store, self.kek.clone())?;
            return Ok(Box::new(stripe_source));
        }

        if let Some(remote_image) = &self.options.remote_image {
            let client = Self::build_remote_client(&self.options, &self.kek, remote_image)?;
            let stripe_source =
                RemoteStripeSource::new(Box::new(client), self.stripe_sector_count)?;
            return Ok(Box::new(stripe_source));
        }

        let block_device = build_source_device(&self.options)?;

        let stripe_source = BlockDeviceStripeSource::new(block_device, self.stripe_sector_count)?;
        Ok(Box::new(stripe_source))
    }

    fn build_remote_client(
        options: &Options,
        kek: &KeyEncryptionCipher,
        server_addr: &str,
    ) -> Result<StripeServerClient> {
        let psk = PskCredentials::from_options(options, kek)?;
        connect_to_stripe_server(server_addr, psk.as_ref())
    }

    fn decrypt_aws_credentials(
        credentials: &Option<AwsCredentials>,
        kek: &KeyEncryptionCipher,
    ) -> Result<Option<aws_sdk_s3::config::Credentials>> {
        if let Some(creds) = credentials {
            let access_key_id = kek.decrypt_aws_credential(creds.access_key_id.clone())?;
            let secret_access_key = kek.decrypt_aws_credential(creds.secret_access_key.clone())?;
            Ok(Some(
                aws_sdk_s3::config::Credentials::builder()
                    .access_key_id(access_key_id)
                    .secret_access_key(secret_access_key)
                    .provider_name("ubiblk_archive")
                    .build(),
            ))
        } else {
            Ok(None)
        }
    }

    pub fn build_archive_store(
        config: &ArchiveStripeSourceConfig,
        kek: &KeyEncryptionCipher,
    ) -> Result<Box<dyn ArchiveStore>> {
        match config {
            ArchiveStripeSourceConfig::Filesystem { path } => {
                Ok(Box::new(FileSystemStore::new(path.into())?))
            }
            ArchiveStripeSourceConfig::S3 {
                bucket,
                prefix,
                region,
                endpoint,
                profile,
                credentials,
            } => {
                let decrypted_credentials = Self::decrypt_aws_credentials(credentials, kek)?;
                let runtime = create_runtime()?;
                let client = build_s3_client(
                    &runtime,
                    profile.as_deref(),
                    endpoint.as_deref(),
                    region.as_deref(),
                    decrypted_credentials,
                )?;

                Ok(Box::new(S3Store::new(
                    client,
                    bucket.to_string(),
                    prefix.clone(),
                    runtime,
                )?))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::File;
    use std::path::PathBuf;
    use tempfile::tempdir;

    fn create_test_options(remote: Option<String>, path: Option<PathBuf>) -> Options {
        Options {
            remote_image: remote,
            image_path: path.map(|p| p.to_string_lossy().to_string()),
            queue_size: 64,
            ..Default::default()
        }
    }

    #[test]
    fn test_build_defaults_to_null_device() {
        let options = create_test_options(None, None);
        let kek = KeyEncryptionCipher::default();
        let builder = StripeSourceBuilder::new(options, kek, 4096);

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

        let options = create_test_options(None, Some(file_path));
        let kek = KeyEncryptionCipher::default();
        let builder = StripeSourceBuilder::new(options, kek, 4096);

        let result = builder.build();
        assert!(
            result.is_ok(),
            "Should successfully build a BlockDeviceStripeSource with valid image_path"
        );
    }

    #[test]
    fn test_build_local_block_device_fails_on_missing_file() {
        let bad_path = PathBuf::from("/path/to/nonexistent/file.img");
        let options = create_test_options(None, Some(bad_path));
        let kek = KeyEncryptionCipher::default();
        let builder = StripeSourceBuilder::new(options, kek, 4096);

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
        let options = create_test_options(Some("127.0.0.1:99999".to_string()), None);
        let kek = KeyEncryptionCipher::default();
        let builder = StripeSourceBuilder::new(options, kek, 4096);

        let result = builder.build();

        assert!(
            result.is_err(),
            "Should fail to connect to invalid remote server"
        );
    }

    #[test]
    fn test_decrypt_aws_credentials_none() {
        let result =
            StripeSourceBuilder::decrypt_aws_credentials(&None, &KeyEncryptionCipher::default())
                .unwrap();
        assert!(
            result.is_none(),
            "Decrypted credentials should be None when input is None"
        );
    }

    #[test]
    fn test_decrypt_aws_credentials_no_encryption() {
        let kek = KeyEncryptionCipher::default();
        let encrypted_access_key = "test_access_key".as_bytes().to_vec();
        let encrypted_secret_key = "test_secret_key".as_bytes().to_vec();
        let aws_creds = AwsCredentials {
            access_key_id: encrypted_access_key,
            secret_access_key: encrypted_secret_key,
        };
        let result = StripeSourceBuilder::decrypt_aws_credentials(&Some(aws_creds), &kek).unwrap();
        assert!(
            result.is_some(),
            "Decrypted credentials should be Some when input is Some"
        );
        let creds = result.unwrap();
        assert_eq!(creds.access_key_id(), "test_access_key");
        assert_eq!(creds.secret_access_key(), "test_secret_key");
    }

    #[test]
    fn test_build_archive_store_filesystem() {
        let temp_dir = tempdir().unwrap();
        let store = StripeSourceBuilder::build_archive_store(
            &ArchiveStripeSourceConfig::Filesystem {
                path: temp_dir.path().to_str().unwrap().to_string(),
            },
            &KeyEncryptionCipher::default(),
        );
        assert!(store.is_ok());
    }

    #[test]
    fn test_build_archive_store_s3() {
        let aws_creds = AwsCredentials {
            access_key_id: b"test_access_key".to_vec(),
            secret_access_key: b"test_secret_key".to_vec(),
        };
        let config = ArchiveStripeSourceConfig::S3 {
            bucket: "test-bucket".to_string(),
            prefix: Some("test-prefix".to_string()),
            endpoint: Some("http://localhost:9000".to_string()),
            region: Some("auto".to_string()),
            profile: Some("profile1".to_string()),
            credentials: Some(aws_creds),
        };
        let store =
            StripeSourceBuilder::build_archive_store(&config, &KeyEncryptionCipher::default());
        assert!(store.is_ok());
    }
}
