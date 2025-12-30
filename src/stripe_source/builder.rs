use crate::{
    block_device::NullBlockDevice,
    stripe_server::{connect_to_stripe_server, PskCredentials, StripeServerClient},
    vhost_backend::{build_block_device, Options},
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
        if let Some(remote_image) = &self.options.remote_image {
            let client = Self::build_remote_client(&self.options, &self.kek, remote_image)?;
            let stripe_source =
                RemoteStripeSource::new(Box::new(client), self.stripe_sector_count)?;
            return Ok(Box::new(stripe_source));
        }

        let block_device = if let Some(image_path) = &self.options.image_path {
            build_block_device(image_path, &self.options, self.kek.clone(), true)?
        } else {
            NullBlockDevice::new()
        };

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
}
