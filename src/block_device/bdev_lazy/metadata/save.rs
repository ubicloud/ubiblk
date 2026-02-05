use log::info;
use ubiblk_macros::error_context;

use crate::{
    backends::SECTOR_SIZE,
    block_device::{shared_buffer, wait_for_completion, BlockDevice, UbiMetadata},
    Result,
};

pub const METADATA_WRITE_ID: usize = 0;
pub const METADATA_FLUSH_ID: usize = 1;
pub const DEFAULT_STRIPE_SECTOR_COUNT_SHIFT: u8 = 11;

impl UbiMetadata {
    #[error_context("Failed to save metadata to block device")]
    pub fn save_to_bdev(&self, bdev: &dyn BlockDevice) -> Result<()> {
        let mut ch = bdev.create_channel()?;
        let metadata_size = self.metadata_size();
        let sector_count: u32 = bdev.sector_count().try_into().map_err(|_| {
            crate::ubiblk_error!(InvalidParameter {
                description: "Device sector count exceeds u32".to_string(),
            })
        })?;

        let total_size = bdev
            .sector_count()
            .checked_mul(SECTOR_SIZE as u64)
            .and_then(|size| usize::try_from(size).ok())
            .ok_or(crate::ubiblk_error!(InvalidParameter {
                description: "Metadata device too large".to_string(),
            }))?;

        if metadata_size > total_size {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: format!(
                    "Metadata size {metadata_size} exceeds device capacity {total_size}"
                ),
            }));
        }

        let buf = shared_buffer(total_size);

        self.write_to_buf(&mut buf.borrow_mut().as_mut_slice()[..metadata_size])?;

        let timeout = std::time::Duration::from_secs(30);

        info!(
            "Initializing metadata device with {} sectors",
            bdev.sector_count()
        );

        ch.add_write(0, sector_count, buf.clone(), METADATA_WRITE_ID);
        ch.submit()?;
        wait_for_completion(ch.as_mut(), METADATA_WRITE_ID, timeout)?;

        ch.add_flush(METADATA_FLUSH_ID);
        ch.submit()?;
        wait_for_completion(ch.as_mut(), METADATA_FLUSH_ID, timeout)?;

        info!("Metadata device initialized successfully");

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::block_device::NullBlockDevice;

    use super::*;

    #[test]
    fn test_errors_if_metadata_too_large() {
        let bdev = NullBlockDevice::new();
        let metadata = UbiMetadata::new(DEFAULT_STRIPE_SECTOR_COUNT_SHIFT, 4, 16);
        let result = metadata.save_to_bdev(bdev.as_ref());
        assert!(result.is_err());
        assert!(result
            .err()
            .unwrap()
            .to_string()
            .contains("exceeds device capacity"));
    }

    #[test]
    fn test_sector_count_exceeds_u32() {
        let bdev = NullBlockDevice::new_with_sector_count(u64::from(u32::MAX) + 1);
        let metadata = UbiMetadata::new(DEFAULT_STRIPE_SECTOR_COUNT_SHIFT, 4, 16);
        let result = metadata.save_to_bdev(bdev.as_ref());
        assert!(result.is_err());
        assert!(result
            .err()
            .unwrap()
            .to_string()
            .contains("Device sector count exceeds u32"));
    }
}
