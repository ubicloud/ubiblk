use std::{
    cell::RefCell,
    mem::MaybeUninit,
    ptr::copy_nonoverlapping,
    rc::Rc,
    sync::{atomic::AtomicU8, Arc},
};

use super::super::*;
use crate::utils::aligned_buffer::AlignedBuf;
use crate::{vhost_backend::SECTOR_SIZE, Result, VhostUserBlockError};
use log::{error, info};

use super::metadata::{
    StripeMetadataManager, StripeStatus, StripeStatusVec, UbiMetadata, UBI_MAGIC, UBI_MAX_STRIPES,
};

impl StripeMetadataManager {
    pub(crate) fn load_metadata(io_channel: &mut Box<dyn IoChannel>) -> Result<Box<UbiMetadata>> {
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

        let (id, success) = results.pop().unwrap();
        if !success || id != 0 {
            error!("Failed to read metadata: id {}, success {}", id, success);
            return Err(VhostUserBlockError::MetadataError {
                description: format!("Failed to read metadata, id: {}, success:{}", id, success),
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

    pub(crate) fn create_stripe_status_vec(
        metadata: &UbiMetadata,
        source_sector_count: u64,
    ) -> Result<StripeStatusVec> {
        let v = metadata
            .stripe_headers
            .iter()
            .map(|header| {
                if *header == 0 {
                    AtomicU8::new(StripeStatus::NotFetched as u8)
                } else {
                    AtomicU8::new(StripeStatus::Fetched as u8)
                }
            })
            .collect::<Vec<AtomicU8>>();
        let stripe_sector_count = 1u64 << metadata.stripe_sector_count_shift;
        let stripe_count = source_sector_count.div_ceil(stripe_sector_count);

        if stripe_count as usize > UBI_MAX_STRIPES {
            return Err(VhostUserBlockError::InvalidParameter {
                description: "source sector count exceeds maximum stripe count".to_string(),
            });
        }

        Ok(StripeStatusVec {
            data: Arc::new(v),
            stripe_sector_count,
            source_sector_count,
            stripe_count,
        })
    }
}
