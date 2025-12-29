use std::{cell::RefCell, rc::Rc};

use log::info;

use crate::{
    block_device::{wait_for_completion, IoChannel, UbiMetadata},
    utils::aligned_buffer::AlignedBuf,
    vhost_backend::SECTOR_SIZE,
    Result, UbiblkError,
};

pub const METADATA_WRITE_ID: usize = 0;
pub const METADATA_FLUSH_ID: usize = 1;
pub const DEFAULT_STRIPE_SECTOR_COUNT_SHIFT: u8 = 11;

pub fn init_metadata(
    metadata: &UbiMetadata,
    ch: &mut Box<dyn IoChannel>,
    metadata_sector_count: u64,
) -> Result<()> {
    let metadata_size = metadata.metadata_size();
    let total_size = metadata_sector_count
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

    let sectors: u32 =
        metadata_sector_count
            .try_into()
            .map_err(|_| UbiblkError::InvalidParameter {
                description: "Metadata sector count exceeds u32".to_string(),
            })?;

    let buf = Rc::new(RefCell::new(AlignedBuf::new(total_size)));

    metadata.write_to_buf(&mut buf.borrow_mut().as_mut_slice()[..metadata_size]);

    let timeout = std::time::Duration::from_secs(30);

    info!("Initializing metadata device with {} sectors", sectors);

    ch.add_write(0, sectors, buf.clone(), METADATA_WRITE_ID);
    ch.submit()?;
    wait_for_completion(ch.as_mut(), METADATA_WRITE_ID, timeout)?;

    ch.add_flush(METADATA_FLUSH_ID);
    ch.submit()?;
    wait_for_completion(ch.as_mut(), METADATA_FLUSH_ID, timeout)?;

    info!("Metadata device initialized successfully");

    Ok(())
}
