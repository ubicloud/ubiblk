use crate::{
    block_device::{
        bdev_lazy::metadata::types::UBI_MAGIC, shared_buffer, BlockDevice, UbiMetadata,
    },
    vhost_backend::SECTOR_SIZE,
    Result, UbiblkError,
};
use log::{error, info};

impl UbiMetadata {
    pub fn load_from_bdev(bdev: &dyn BlockDevice) -> Result<Box<Self>> {
        info!("Loading metadata from device");

        let mut io_channel = bdev.create_channel()?;
        let sector_count = bdev.sector_count();

        let buf = shared_buffer(sector_count as usize * SECTOR_SIZE);
        let sector_count_u32 =
            sector_count
                .try_into()
                .map_err(|_| UbiblkError::InvalidParameter {
                    description: "Metadata file too large".to_string(),
                })?;

        io_channel.add_read(0, sector_count_u32, buf.clone(), 0);
        io_channel.submit()?;

        let mut results = io_channel.poll();
        while io_channel.busy() {
            std::thread::sleep(std::time::Duration::from_millis(1));
            results.extend(io_channel.poll());
        }

        if results.len() != 1 {
            error!(
                "Failed to read metadata: expected 1 result, got {}",
                results.len()
            );
            return Err(UbiblkError::MetadataError {
                description: format!("Expected 1 result, got {}", results.len()),
            });
        }

        let (id, success) = results.pop().ok_or(UbiblkError::MetadataError {
            description: "Missing poll result".to_string(),
        })?;

        if !success || id != 0 {
            error!("Failed to read metadata: id {id}, success {success}");
            return Err(UbiblkError::MetadataError {
                description: format!("Failed to read metadata, id: {id}, success: {success}"),
            });
        }

        let metadata = UbiMetadata::from_bytes(buf.borrow().as_slice());

        if metadata.magic != *UBI_MAGIC {
            error!(
                "Metadata magic mismatch: expected {:?}, found {:?}",
                UBI_MAGIC, metadata.magic
            );
            return Err(UbiblkError::MetadataError {
                description: format!(
                    "Metadata magic mismatch! Expected: {:?}, Found: {:?}",
                    UBI_MAGIC, metadata.magic
                ),
            });
        }

        info!("Metadata loaded successfully");

        Ok(metadata)
    }
}
