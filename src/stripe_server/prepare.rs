use std::sync::Arc;

use crate::{
    block_device::{
        UbiMetadata, DEFAULT_STRIPE_SECTOR_COUNT_SHIFT, METADATA_STRIPE_WRITTEN_BITMASK,
    },
    stripe_server::StripeServer,
    vhost_backend::{build_block_device, Options},
    KeyEncryptionCipher, Result,
};

pub fn prepare_stripe_server(
    options: &Options,
    kek: KeyEncryptionCipher,
) -> Result<Arc<StripeServer>> {
    let stripe_device = build_block_device(&options.path, options, kek.clone(), false)?;
    let metadata: Arc<UbiMetadata> = if let Some(metadata_path) = options.metadata_path.as_deref() {
        let metadata_device = build_block_device(metadata_path, options, kek, false)?;
        let metadata = UbiMetadata::load_from_bdev(metadata_device.as_ref())?;
        Arc::from(metadata)
    } else {
        let stripe_sector_count_shift = DEFAULT_STRIPE_SECTOR_COUNT_SHIFT;
        let stripe_sector_count = 1u64 << stripe_sector_count_shift;
        let stripe_count = stripe_device.stripe_count(stripe_sector_count);
        let mut metadata = UbiMetadata::new(stripe_sector_count_shift, stripe_count, stripe_count);
        for stripe_header in metadata.stripe_headers.iter_mut() {
            *stripe_header |= METADATA_STRIPE_WRITTEN_BITMASK;
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

    fn options(path: String, metadata_path: Option<String>) -> Options {
        Options {
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

        let options = options(storage_file.path().to_str().unwrap().to_string(), None);

        let kek = KeyEncryptionCipher::default();

        let server = prepare_stripe_server(&options, kek)?;

        let metadata = server.metadata.as_ref();
        assert_eq!(metadata.stripe_headers.len(), stripe_count as usize);

        for header in metadata.stripe_headers.iter() {
            assert_eq!(
                *header & METADATA_STRIPE_WRITTEN_BITMASK,
                METADATA_STRIPE_WRITTEN_BITMASK
            );
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
                metadata.stripe_headers[i] |= METADATA_STRIPE_WRITTEN_BITMASK;
            }
        }

        metadata_file.as_file().set_len(4 * 1024 * 1024)?;
        let mut buf = vec![0u8; metadata.metadata_size()];
        metadata.write_to_buf(&mut buf);
        metadata_file.as_file().write_all(&buf)?;

        let options = options(
            storage_file.path().to_str().unwrap().to_string(),
            Some(metadata_file.path().to_str().unwrap().to_string()),
        );

        let kek = KeyEncryptionCipher::default();
        let server = prepare_stripe_server(&options, kek)?;

        let loaded_metadata = server.metadata.as_ref();
        for i in 0..stripe_count as usize {
            assert_eq!(
                loaded_metadata.stripe_headers[i],
                metadata.stripe_headers[i]
            );
        }

        Ok(())
    }
}
