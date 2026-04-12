use std::collections::HashMap;
use std::fs::File;
use std::io::{Seek, SeekFrom, Write};
use std::path::Path;

use log::info;
use ubiblk_macros::error_context;

use crate::{
    backends::SECTOR_SIZE,
    block_device::{shared_buffer, SharedBuffer},
    config::v2::ExportArchiveConfig,
    stripe_source::{ArchiveStripeSource, StripeSource, StripeSourceBuilder},
    Result,
};

const MAX_FETCHES: usize = 16;

#[error_context("Failed to export archive to raw image")]
pub fn export_archive(config: &ExportArchiveConfig, target: &Path) -> Result<()> {
    let store = StripeSourceBuilder::build_archive_store(&config.archive, &config.secrets)?;
    let kek = StripeSourceBuilder::build_archive_kek(&config.archive, &config.secrets)?;
    let mut source = ArchiveStripeSource::new(store, kek)?;

    let sector_count = source.sector_count();
    let stripe_sector_count = source.stripe_sector_count();
    let total_bytes = sector_count * SECTOR_SIZE as u64;
    info!(
        "exporting archive: {} sectors, {} bytes",
        sector_count, total_bytes
    );

    if sector_count == 0 {
        info!("archive is empty, writing empty file");
        File::create(target).map_err(|e| crate::ubiblk_error!(IoError { source: e }))?;
        return Ok(());
    }

    let stripe_count = sector_count.div_ceil(stripe_sector_count) as usize;
    let stripe_size = stripe_sector_count as usize * SECTOR_SIZE;

    let mut file = File::create(target).map_err(|e| crate::ubiblk_error!(IoError { source: e }))?;

    // Pre-allocate the file so stripes can be written out of order.
    file.set_len(total_bytes)
        .map_err(|e| crate::ubiblk_error!(IoError { source: e }))?;

    let mut next_submit = 0usize;
    let mut written = 0usize;
    let mut last_reported_written = 0usize;
    let mut in_flight: HashMap<usize, SharedBuffer> = HashMap::new();

    while written < stripe_count {
        // Fill up to MAX_FETCHES in-flight requests.
        while in_flight.len() < MAX_FETCHES && next_submit < stripe_count {
            let stripe_id = next_submit;
            next_submit += 1;

            if !source.has_stripe(stripe_id) {
                // File is pre-allocated with zeros, nothing to write.
                written += 1;
                continue;
            }

            let buffer = shared_buffer(stripe_size);
            source.request(stripe_id, buffer.clone())?;
            in_flight.insert(stripe_id, buffer);
        }

        // Poll for completions and write out of order.
        let completions = source.poll();
        for (completed_id, success) in &completions {
            if !success {
                return Err(crate::ubiblk_error!(ArchiveError {
                    description: format!("failed to fetch stripe {}", completed_id),
                }));
            }
            if let Some(buffer) = in_flight.remove(completed_id) {
                let offset = *completed_id as u64 * stripe_size as u64;
                file.seek(SeekFrom::Start(offset))
                    .map_err(|e| crate::ubiblk_error!(IoError { source: e }))?;
                file.write_all(buffer.borrow().as_slice())
                    .map_err(|e| crate::ubiblk_error!(IoError { source: e }))?;
                written += 1;
            }
        }

        if written - last_reported_written >= 100 || written == stripe_count {
            info!("exported {}/{} stripes", written, stripe_count);
            last_reported_written = written;
        }

        if completions.is_empty() && !in_flight.is_empty() {
            std::thread::sleep(std::time::Duration::from_millis(1));
        }
    }

    info!("export complete: {}", target.display());
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        archive::{ArchiveCompressionAlgorithm, MemStore, StripeArchiver},
        backends::SECTOR_SIZE,
        block_device::{
            bdev_test::TestBlockDevice, metadata_flags, shared_buffer, BlockDevice, UbiMetadata,
        },
        stripe_source::BlockDeviceStripeSource,
        KeyEncryptionCipher,
    };
    use std::rc::Rc;

    const STRIPE_SECTOR_COUNT_SHIFT: u8 = 4;
    const STRIPE_SECTOR_COUNT: u64 = 1 << STRIPE_SECTOR_COUNT_SHIFT;

    fn clone_memstore(store: &MemStore) -> Box<MemStore> {
        Box::new(MemStore::new_with_objects(Rc::clone(&store.objects)))
    }

    #[test]
    fn test_export_archive_roundtrip() {
        let kek = KeyEncryptionCipher::default();
        let bdev_stripe_count = 4;
        let image_stripe_count = 4;

        let mut metadata = UbiMetadata::new(
            STRIPE_SECTOR_COUNT_SHIFT,
            bdev_stripe_count,
            image_stripe_count,
        );
        for stripe_id in 0..bdev_stripe_count {
            metadata.stripe_headers[stripe_id] |= metadata_flags::WRITTEN;
        }

        let bdev_size = STRIPE_SECTOR_COUNT * (bdev_stripe_count * SECTOR_SIZE) as u64;
        let disk_bdev: Box<TestBlockDevice> = Box::new(TestBlockDevice::new(bdev_size));

        let image_bdev_size = STRIPE_SECTOR_COUNT * (image_stripe_count * SECTOR_SIZE) as u64;
        let image_bdev: Box<TestBlockDevice> = Box::new(TestBlockDevice::new(image_bdev_size));

        // Fill image with known data
        for stripe_id in 0..image_stripe_count {
            for sector in 0..STRIPE_SECTOR_COUNT {
                let offset = (stripe_id as u64 * STRIPE_SECTOR_COUNT + sector) * SECTOR_SIZE as u64;
                let byte = ((stripe_id + sector as usize) % 256) as u8;
                let buf = vec![byte; SECTOR_SIZE];
                let mut mem = image_bdev.mem.write().unwrap();
                mem[offset as usize..offset as usize + SECTOR_SIZE].copy_from_slice(&buf);
            }
        }

        // Fill disk with different data for written stripes
        for stripe_id in 0..bdev_stripe_count {
            for sector in 0..STRIPE_SECTOR_COUNT {
                let offset = (stripe_id as u64 * STRIPE_SECTOR_COUNT + sector) * SECTOR_SIZE as u64;
                let byte = ((3 + stripe_id + sector as usize) % 256) as u8;
                let buf = vec![byte; SECTOR_SIZE];
                let mut mem = disk_bdev.mem.write().unwrap();
                mem[offset as usize..offset as usize + SECTOR_SIZE].copy_from_slice(&buf);
            }
        }

        let stripe_source =
            BlockDeviceStripeSource::new(image_bdev.clone(), STRIPE_SECTOR_COUNT).unwrap();
        let store = Box::new(MemStore::new());

        let mut archiver = StripeArchiver::new(
            Box::new(stripe_source),
            disk_bdev.as_ref(),
            metadata,
            clone_memstore(store.as_ref()),
            false,
            ArchiveCompressionAlgorithm::None,
            kek.clone(),
            1,
        )
        .unwrap();

        archiver.archive_all().unwrap();

        // Now export via ArchiveStripeSource using the concurrent loop
        let mut source =
            ArchiveStripeSource::new(clone_memstore(store.as_ref()), kek.clone()).unwrap();
        let sector_count = source.sector_count();
        let stripe_sector_count = source.stripe_sector_count();
        let stripe_count = sector_count.div_ceil(stripe_sector_count) as usize;
        let stripe_size = stripe_sector_count as usize * SECTOR_SIZE;

        let mut exported = vec![0u8; sector_count as usize * SECTOR_SIZE];
        let mut next_submit = 0usize;
        let mut written = 0usize;
        let mut in_flight: HashMap<usize, SharedBuffer> = HashMap::new();

        while written < stripe_count {
            while in_flight.len() < MAX_FETCHES && next_submit < stripe_count {
                let stripe_id = next_submit;
                next_submit += 1;
                if !source.has_stripe(stripe_id) {
                    written += 1;
                    continue;
                }
                let buffer = shared_buffer(stripe_size);
                source.request(stripe_id, buffer.clone()).unwrap();
                in_flight.insert(stripe_id, buffer);
            }

            let completions = source.poll();
            for (completed_id, success) in &completions {
                assert!(success, "stripe fetch should succeed");
                if let Some(buffer) = in_flight.remove(completed_id) {
                    let offset = completed_id * stripe_size;
                    exported[offset..offset + stripe_size]
                        .copy_from_slice(buffer.borrow().as_slice());
                    written += 1;
                }
            }
        }

        // Verify: written stripes should have disk data, others have image data
        for stripe_id in 0..bdev_stripe_count {
            for sector in 0..STRIPE_SECTOR_COUNT {
                let offset = (stripe_id as u64 * STRIPE_SECTOR_COUNT + sector) * SECTOR_SIZE as u64;
                let expected = ((3 + stripe_id + sector as usize) % 256) as u8;
                for b in &exported[offset as usize..offset as usize + SECTOR_SIZE] {
                    assert_eq!(
                        *b, expected,
                        "mismatch at stripe {stripe_id}, sector {sector}"
                    );
                }
            }
        }
    }
}
