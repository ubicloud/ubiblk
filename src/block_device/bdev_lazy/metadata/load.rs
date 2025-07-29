use crate::{
    block_device::{bdev_lazy::metadata::UBI_MAGIC, AlignedBuf, IoChannel, UbiMetadata},
    vhost_backend::SECTOR_SIZE,
    Result, VhostUserBlockError,
};
use log::{error, info};
use std::{cell::RefCell, mem::MaybeUninit, ptr::copy_nonoverlapping, rc::Rc};

pub fn load_metadata(io_channel: &mut Box<dyn IoChannel>) -> Result<Box<UbiMetadata>> {
    info!("Loading metadata from device");

    let sector_count = std::mem::size_of::<UbiMetadata>().div_ceil(SECTOR_SIZE);
    let buf: Rc<RefCell<AlignedBuf>> =
        Rc::new(RefCell::new(AlignedBuf::new(sector_count * SECTOR_SIZE)));
    io_channel.add_read(0, sector_count as u32, buf.clone(), 0);
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
        return Err(VhostUserBlockError::MetadataError {
            description: format!("Expected 1 result, got {}", results.len()),
        });
    }

    let (id, success) = match results.pop() {
        Some(v) => v,
        None => {
            return Err(VhostUserBlockError::MetadataError {
                description: "Missing poll result".to_string(),
            });
        }
    };
    if !success || id != 0 {
        error!("Failed to read metadata: id {id}, success {success}");
        return Err(VhostUserBlockError::MetadataError {
            description: format!("Failed to read metadata, id: {id}, success: {success}"),
        });
    }

    let mut metadata: Box<MaybeUninit<UbiMetadata>> = Box::new_uninit();

    unsafe {
        copy_nonoverlapping(
            buf.borrow().as_ptr(),
            metadata.as_mut_ptr() as *mut u8,
            std::mem::size_of::<UbiMetadata>(),
        );
    }

    let metadata: Box<UbiMetadata> = unsafe { metadata.assume_init() };

    if metadata.magic != *UBI_MAGIC {
        error!(
            "Metadata magic mismatch: expected {:?}, found {:?}",
            UBI_MAGIC, metadata.magic
        );
        return Err(VhostUserBlockError::MetadataError {
            description: format!(
                "Metadata magic mismatch! Expected: {:?}, Found: {:?}",
                UBI_MAGIC, metadata.magic
            ),
        });
    }

    info!("Metadata loaded successfully");

    Ok(metadata)
}
