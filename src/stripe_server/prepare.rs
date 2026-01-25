use std::sync::Arc;

use crate::{
    block_device::{metadata_flags, UbiMetadata, DEFAULT_STRIPE_SECTOR_COUNT_SHIFT},
    config::DeviceConfig,
    stripe_server::StripeServer,
    vhost_backend::build_block_device,
    Result,
};

fn error_if_incomplete_metadata(metadata: &UbiMetadata) -> Result<()> {
    if !metadata.has_fetched_all_stripes() {
        return Err(crate::ubiblk_error!(InvalidParameter {
            description: "Not all source stripes have been fetched.".to_string()
        }));
    }
    Ok(())
}

pub fn prepare_stripe_server(config: &DeviceConfig) -> Result<Arc<StripeServer>> {
    let stripe_device = build_block_device(&config.path, config, false)?;
    let metadata: Arc<UbiMetadata> = if let Some(metadata_path) = config.metadata_path.as_deref() {
        let metadata_device = build_block_device(metadata_path, config, false)?;
        let metadata = UbiMetadata::load_from_bdev(metadata_device.as_ref())?;
        error_if_incomplete_metadata(&metadata)?;
        Arc::from(metadata)
    } else {
        let stripe_sector_count_shift = DEFAULT_STRIPE_SECTOR_COUNT_SHIFT;
        let stripe_sector_count = 1u64 << stripe_sector_count_shift;
        let stripe_count = stripe_device.stripe_count(stripe_sector_count);
        let mut metadata = UbiMetadata::new(stripe_sector_count_shift, stripe_count, stripe_count);
        for stripe_header in metadata.stripe_headers.iter_mut() {
            *stripe_header |= metadata_flags::WRITTEN | metadata_flags::FETCHED;
        }
        Arc::from(metadata)
    };

    Ok(Arc::new(StripeServer::new(
        Arc::from(stripe_device),
        metadata,
    )))
}

#[cfg(test)]
mod tests {
    use crate::vhost_backend::SECTOR_SIZE;

    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    const STRIPE_SIZE: u64 = (1 << DEFAULT_STRIPE_SECTOR_COUNT_SHIFT) * SECTOR_SIZE as u64;

    fn config(path: String, metadata_path: Option<String>) -> DeviceConfig {
        DeviceConfig {
            path,
            metadata_path,
            queue_size: 128,
            ..Default::default()
        }
    }

    #[test]
    fn test_prepare_stripe_server_without_metadata() -> Result<()> {
        let stripe_count = 16;
        let storage_file = NamedTempFile::new()?;
        storage_file.as_file().set_len(stripe_count * STRIPE_SIZE)?;

        let config = config(storage_file.path().to_str().unwrap().to_string(), None);

        let server = prepare_stripe_server(&config)?;

        let metadata = server.metadata.as_ref();
        assert_eq!(metadata.stripe_headers.len(), stripe_count as usize);

        for header in metadata.stripe_headers.iter() {
            assert_eq!(*header & metadata_flags::WRITTEN, metadata_flags::WRITTEN);
        }

        Ok(())
    }

    #[test]
    fn test_prepare_stripe_server_with_metadata() -> Result<()> {
        let stripe_count = 1024;
        let storage_file = NamedTempFile::new()?;
        let metadata_file = NamedTempFile::new()?;

        storage_file.as_file().set_len(stripe_count * STRIPE_SIZE)?;

        let mut metadata =
            UbiMetadata::new(DEFAULT_STRIPE_SECTOR_COUNT_SHIFT, stripe_count as usize, 0);

        for i in 0..stripe_count as usize {
            if i % 3 == 0 || i % 5 == 0 {
                metadata.stripe_headers[i] |= metadata_flags::WRITTEN;
            }
        }

        metadata_file.as_file().set_len(4 * 1024 * 1024)?;
        let mut buf = vec![0u8; metadata.metadata_size()];
        metadata.write_to_buf(&mut buf);
        metadata_file.as_file().write_all(&buf)?;

        let config = config(
            storage_file.path().to_str().unwrap().to_string(),
            Some(metadata_file.path().to_str().unwrap().to_string()),
        );

        let server = prepare_stripe_server(&config)?;

        let loaded_metadata = server.metadata.as_ref();
        for i in 0..stripe_count as usize {
            assert_eq!(
                loaded_metadata.stripe_headers[i],
                metadata.stripe_headers[i]
            );
        }

        Ok(())
    }

    #[test]
    fn test_error_if_incomplete_metadata() {
        let mut metadata = UbiMetadata::new(DEFAULT_STRIPE_SECTOR_COUNT_SHIFT, 16, 4);

        for i in 0..4 {
            let result = error_if_incomplete_metadata(&metadata);
            assert!(result.is_err());
            metadata.stripe_headers[i] |= metadata_flags::FETCHED;
        }

        let result = error_if_incomplete_metadata(&metadata);
        assert!(result.is_ok());
    }
}
