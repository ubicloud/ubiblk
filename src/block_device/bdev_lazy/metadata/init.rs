use std::{cell::RefCell, rc::Rc};

use crate::block_device::{IoChannel, UbiMetadata};
use crate::utils::aligned_buffer::AlignedBuf;
use crate::{vhost_backend::SECTOR_SIZE, Result, VhostUserBlockError};
use log::{error, info};

pub const METADATA_WRITE_ID: usize = 0;
pub const METADATA_FLUSH_ID: usize = 1;

fn wait_for_completion(ch: &mut Box<dyn IoChannel>, id: usize) -> Result<()> {
    let timeout = std::time::Duration::from_secs(5);
    let start = std::time::Instant::now();
    let op = if id == METADATA_WRITE_ID {
        "write"
    } else {
        "flush"
    };
    while start.elapsed() < timeout {
        std::thread::sleep(std::time::Duration::from_millis(1));
        if let Some((cid, success)) = ch.poll().into_iter().next() {
            if cid != id {
                error!("Unexpected completion ID: {cid}, expected {id}");
                return Err(VhostUserBlockError::IoError {
                    source: std::io::Error::other(format!("Unexpected ID: {cid}")),
                });
            }
            if !success {
                error!("Failed to {op} metadata");
                return Err(VhostUserBlockError::IoError {
                    source: std::io::Error::other(format!("Failed to {op} metadata")),
                });
            }
            if id == METADATA_WRITE_ID {
                info!("Metadata written successfully, flushing...");
            } else {
                info!("Metadata flushed successfully");
            }
            return Ok(());
        }
    }
    error!("Timeout while waiting for metadata {op}");
    Err(VhostUserBlockError::IoError {
        source: std::io::Error::new(
            std::io::ErrorKind::TimedOut,
            format!("Timeout while waiting for metadata {op}"),
        ),
    })
}

pub fn init_metadata(
    metadata: &UbiMetadata,
    ch: &mut Box<dyn IoChannel>,
    metadata_sector_count: u64,
) -> Result<()> {
    let metadata_size = metadata.metadata_size();
    let total_size = metadata_sector_count
        .checked_mul(SECTOR_SIZE as u64)
        .and_then(|size| usize::try_from(size).ok())
        .ok_or(VhostUserBlockError::InvalidParameter {
            description: "Metadata device too large".to_string(),
        })?;

    if metadata_size > total_size {
        return Err(VhostUserBlockError::InvalidParameter {
            description: format!(
                "Metadata size {metadata_size} exceeds device capacity {total_size}"
            ),
        });
    }

    let sectors: u32 =
        metadata_sector_count
            .try_into()
            .map_err(|_| VhostUserBlockError::InvalidParameter {
                description: "Metadata sector count exceeds u32".to_string(),
            })?;

    let buf = Rc::new(RefCell::new(AlignedBuf::new(total_size)));

    metadata.write_to_buf(&mut buf.borrow_mut().as_mut_slice()[..metadata_size]);

    ch.add_write(0, sectors, buf.clone(), METADATA_WRITE_ID);
    ch.submit()?;
    wait_for_completion(ch, METADATA_WRITE_ID)?;

    ch.add_flush(METADATA_FLUSH_ID);
    ch.submit()?;
    wait_for_completion(ch, METADATA_FLUSH_ID)?;
    Ok(())
}
