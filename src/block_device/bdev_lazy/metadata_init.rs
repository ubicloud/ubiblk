use std::{cell::RefCell, ptr::copy_nonoverlapping, rc::Rc};

use super::super::{IoChannel, UbiMetadata};
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
                error!("Unexpected completion ID: {}, expected {}", cid, id);
                return Err(VhostUserBlockError::IoError {
                    source: std::io::Error::other(format!("Unexpected ID: {}", cid)),
                });
            }
            if !success {
                error!("Failed to {} metadata", op);
                return Err(VhostUserBlockError::IoError {
                    source: std::io::Error::other(format!("Failed to {} metadata", op)),
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
    error!("Timeout while waiting for metadata {}", op);
    Err(VhostUserBlockError::IoError {
        source: std::io::Error::new(
            std::io::ErrorKind::TimedOut,
            format!("Timeout while waiting for metadata {}", op),
        ),
    })
}

pub fn init_metadata(metadata: &UbiMetadata, ch: &mut Box<dyn IoChannel>) -> Result<()> {
    let metadata_size = std::mem::size_of::<UbiMetadata>();
    let sectors = metadata_size.div_ceil(SECTOR_SIZE);
    let buf = Rc::new(RefCell::new(AlignedBuf::new(sectors * SECTOR_SIZE)));

    unsafe {
        let src = metadata as *const UbiMetadata as *const u8;
        let dst = buf.borrow_mut().as_mut_ptr();
        copy_nonoverlapping(src, dst, metadata_size);
    }

    ch.add_write(0, sectors as u32, buf.clone(), METADATA_WRITE_ID);
    ch.submit()?;
    wait_for_completion(ch, METADATA_WRITE_ID)?;

    ch.add_flush(METADATA_FLUSH_ID);
    ch.submit()?;
    wait_for_completion(ch, METADATA_FLUSH_ID)?;
    Ok(())
}
