use log::info;

use crate::{
    block_device::{shared_buffer, wait_for_completion, BlockDevice, UbiMetadata},
    vhost_backend::SECTOR_SIZE,
    Result, UbiblkError,
};

pub const METADATA_WRITE_ID: usize = 0;
pub const METADATA_FLUSH_ID: usize = 1;
pub const DEFAULT_STRIPE_SECTOR_COUNT_SHIFT: u8 = 11;

impl UbiMetadata {
    pub fn save_to_bdev(&self, bdev: &dyn BlockDevice) -> Result<()> {
        let mut ch = bdev.create_channel()?;
        let metadata_size = self.metadata_size();
        let total_size = bdev
            .sector_count()
            .checked_mul(SECTOR_SIZE as u64)
            .and_then(|size| usize::try_from(size).ok())
            .ok_or(UbiblkError::InvalidParameter {
                description: "Metadata device too large".to_string(),
            })?;

        if metadata_size > total_size {
            return Err(UbiblkError::InvalidParameter {
                description: format!(
                    "Metadata size {metadata_size} exceeds device capacity {total_size}"
                ),
            });
        }

        let buf = shared_buffer(total_size);

        self.write_to_buf(&mut buf.borrow_mut().as_mut_slice()[..metadata_size]);

        let timeout = std::time::Duration::from_secs(30);

        info!(
            "Initializing metadata device with {} sectors",
            bdev.sector_count()
        );

        let sector_count: u32 =
            bdev.sector_count()
                .try_into()
                .map_err(|_| UbiblkError::InvalidParameter {
                    description: "Device sector count exceeds u32".to_string(),
                })?;

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
