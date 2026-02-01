use crate::{
    backends::SECTOR_SIZE,
    block_device::{
        bdev_lazy::metadata::types::{METADATA_VERSION_MAJOR, METADATA_VERSION_MINOR, UBI_MAGIC},
        shared_buffer, wait_for_completion, BlockDevice, UbiMetadata,
    },
    Result,
};
use log::{error, info};
use ubiblk_macros::error_context;

impl UbiMetadata {
    #[error_context("Failed to load metadata")]
    pub fn load_from_bdev(bdev: &dyn BlockDevice) -> Result<Box<Self>> {
        info!("Loading metadata from device");

        let mut io_channel = bdev.create_channel()?;
        let sector_count = bdev.sector_count();

        let buf = shared_buffer(sector_count as usize * SECTOR_SIZE);
        let sector_count_u32 = sector_count.try_into().map_err(|_| {
            crate::ubiblk_error!(InvalidParameter {
                description: "Metadata file too large".to_string(),
            })
        })?;

        io_channel.add_read(0, sector_count_u32, buf.clone(), 0);
        io_channel.submit()?;

        wait_for_completion(io_channel.as_mut(), 0, std::time::Duration::from_secs(30))?;

        let metadata = UbiMetadata::from_bytes(buf.borrow().as_slice());

        if metadata.magic != *UBI_MAGIC {
            error!(
                "Metadata magic mismatch: expected {:?}, found {:?}",
                UBI_MAGIC, metadata.magic
            );
            return Err(crate::ubiblk_error!(MetadataError {
                description: format!(
                    "Metadata magic mismatch! Expected: {:?}, Found: {:?}",
                    UBI_MAGIC, metadata.magic
                ),
            }));
        }

        let version_major = metadata.version_major_u16();
        let version_minor = metadata.version_minor_u16();
        if version_major != METADATA_VERSION_MAJOR || version_minor != METADATA_VERSION_MINOR {
            error!(
                "Metadata version mismatch: expected {}.{}, found {}.{}",
                METADATA_VERSION_MAJOR, METADATA_VERSION_MINOR, version_major, version_minor
            );
            return Err(crate::ubiblk_error!(MetadataError {
                description: format!(
                    "Metadata version mismatch! Expected: {}.{}, Found: {}.{}",
                    METADATA_VERSION_MAJOR, METADATA_VERSION_MINOR, version_major, version_minor
                ),
            }));
        }

        info!("Metadata loaded successfully");

        Ok(metadata)
    }
}

#[cfg(test)]
mod tests {
    use crate::block_device::bdev_test::TestBlockDevice;

    use super::*;

    #[test]
    fn test_loads_metadata() {
        let device = TestBlockDevice::new(1024 * 1024);
        let mut metadata = UbiMetadata::new(11, 16, 16);

        for (i, header) in metadata.stripe_headers.iter_mut().enumerate() {
            *header = (i as u8) % 5;
        }

        metadata.save_to_bdev(&device).expect("save metadata");

        let loaded_metadata = UbiMetadata::load_from_bdev(&device).expect("load metadata");

        assert_eq!(metadata.magic, loaded_metadata.magic);
        assert_eq!(metadata.version_major, loaded_metadata.version_major);
        assert_eq!(metadata.version_minor, loaded_metadata.version_minor);
        assert_eq!(
            metadata.stripe_sector_count_shift,
            loaded_metadata.stripe_sector_count_shift
        );
        assert_eq!(
            metadata.stripe_headers,
            loaded_metadata.stripe_headers[..metadata.stripe_headers.len()]
        );
    }

    #[test]
    fn test_invalid_magic() {
        let device = TestBlockDevice::new(1024 * 1024);
        let result = UbiMetadata::load_from_bdev(&device);
        assert!(
            result.is_err()
                && result
                    .unwrap_err()
                    .to_string()
                    .contains("Metadata magic mismatch")
        );
    }

    #[test]
    fn test_invalid_version() {
        let device = TestBlockDevice::new(1024 * 1024);
        let mut metadata = UbiMetadata::new(11, 16, 16);
        metadata.version_minor = (METADATA_VERSION_MINOR + 1).to_le_bytes();
        metadata.save_to_bdev(&device).expect("save metadata");

        let result = UbiMetadata::load_from_bdev(&device);
        assert!(
            result.is_err()
                && result
                    .unwrap_err()
                    .to_string()
                    .contains("Metadata version mismatch")
        );
    }
}
