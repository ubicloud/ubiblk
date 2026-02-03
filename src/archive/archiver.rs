use std::collections::{HashMap, HashSet};

use log::{debug, info};

use super::ArchiveStore;
use crate::{
    archive::{
        ArchiveCompressionAlgorithm, ArchiveMetadata, ARCHIVE_FORMAT_VERSION,
        DEFAULT_ARCHIVE_TIMEOUT,
    },
    backends::SECTOR_SIZE,
    block_device::{metadata_flags, BlockDevice, IoChannel, SharedBuffer, UbiMetadata},
    crypt::XtsBlockCipher,
    stripe_source::StripeSource,
    utils::{aligned_buffer::BUFFER_ALIGNMENT, hash::sha256_hex, AlignedBufferPool},
    KeyEncryptionCipher, Result,
};

pub struct StripeArchiver {
    stripe_source: Box<dyn StripeSource>,
    io_channel: Box<dyn IoChannel>,
    stripe_count: usize,
    metadata: Box<UbiMetadata>,
    archive_store: Box<dyn ArchiveStore>,
    block_cipher: Option<XtsBlockCipher>,
    kek: KeyEncryptionCipher,
    buffer_pool: AlignedBufferPool,
    inflight_puts: usize,
    stripe_fetch_buffers: HashMap<usize, SharedBuffer>,
    seen_hashes: HashSet<String>,
    stripe_hashes: HashMap<usize, String>,
    compression: ArchiveCompressionAlgorithm,
}

impl StripeArchiver {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        stripe_source: Box<dyn StripeSource>,
        bdev: &dyn BlockDevice,
        metadata: Box<UbiMetadata>,
        archive_store: Box<dyn ArchiveStore>,
        encrypt: bool,
        compression: ArchiveCompressionAlgorithm,
        kek: KeyEncryptionCipher,
        concurrency: usize,
    ) -> Result<Self> {
        let block_cipher = if encrypt {
            Some(XtsBlockCipher::random()?)
        } else {
            None
        };
        let stripe_count = bdev.stripe_count(metadata.stripe_sector_count());
        let buffer_pool = AlignedBufferPool::new(
            BUFFER_ALIGNMENT,
            concurrency,
            metadata.stripe_sector_count() as usize * SECTOR_SIZE,
        );
        Ok(Self {
            stripe_source,
            io_channel: bdev.create_channel()?,
            metadata,
            archive_store,
            block_cipher,
            kek,
            stripe_count,
            buffer_pool,
            inflight_puts: 0,
            stripe_fetch_buffers: HashMap::new(),
            seen_hashes: HashSet::new(),
            stripe_hashes: HashMap::new(),
            compression,
        })
    }

    pub fn archive_all(&mut self) -> crate::Result<()> {
        let mut next_stripe_id = 0;
        while next_stripe_id < self.stripe_count {
            if !self.stripe_should_be_archived(next_stripe_id) {
                next_stripe_id += 1;
                continue;
            }

            if self.maybe_start_next_stripe(next_stripe_id)? {
                next_stripe_id += 1;
            }

            self.poll_fetches()?;
            self.poll_uploads()?;
        }

        // Drain all in-flight operations before putting metadata
        while !self.stripe_fetch_buffers.is_empty() || self.inflight_puts > 0 {
            self.poll_fetches()?;
            self.poll_uploads()?;
        }

        self.put_metadata()?;
        self.put_stripe_hashes()?;
        Ok(())
    }

    fn maybe_start_next_stripe(&mut self, stripe_id: usize) -> Result<bool> {
        if let Some(buffer) = self.buffer_pool.get_buffer() {
            info!("Archiving stripe {}", stripe_id);
            self.stripe_fetch_buffers.insert(stripe_id, buffer.clone());

            self.start_fetch_stripe(stripe_id, buffer)?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    fn start_fetch_stripe(&mut self, stripe_id: usize, buffer: SharedBuffer) -> Result<()> {
        if self.stripe_written(stripe_id) || self.stripe_fetched(stripe_id) {
            debug!("Fetching stripe {} from block device", stripe_id,);
            self.io_channel.add_read(
                self.stripe_offset(stripe_id),
                self.metadata.stripe_sector_count() as u32,
                buffer,
                stripe_id,
            );
            self.io_channel.submit()?;
        } else {
            debug!("Fetching stripe {} from image", stripe_id,);
            self.stripe_source.request(stripe_id, buffer.clone())?;
        }
        Ok(())
    }

    fn poll_fetches(&mut self) -> Result<()> {
        let mut completed = self.io_channel.poll();
        completed.extend(self.stripe_source.poll());

        for (stripe_id, success) in completed {
            if !success {
                return Err(crate::ubiblk_error!(ArchiveError {
                    description: format!("I/O error while fetching stripe {}", stripe_id),
                }));
            }

            debug!("Completed fetching stripe {}", stripe_id,);
            self.start_upload_stripe(stripe_id)?;
        }
        Ok(())
    }

    fn maybe_encrypt(&mut self, stripe_id: usize, buffer: &mut [u8]) {
        let sector_offset = self.stripe_offset(stripe_id);
        assert!(
            buffer.len().is_multiple_of(SECTOR_SIZE),
            "Buffer length must be a multiple of sector size"
        );
        let sector_count = buffer.len() as u64 / SECTOR_SIZE as u64;
        if let Some(block_cipher) = self.block_cipher.as_mut() {
            block_cipher.encrypt(buffer, sector_offset, sector_count);
        }
    }

    fn start_upload_stripe(&mut self, stripe_id: usize) -> Result<()> {
        let buffer = self
            .stripe_fetch_buffers
            .remove(&stripe_id)
            .ok_or(crate::ubiblk_error!(ArchiveError {
                description: format!("Stripe buffer for stripe {} not found", stripe_id),
            }))?;

        let buffer_ref = buffer.borrow();
        let mut object_data = self.compression.compress(buffer_ref.as_slice())?;
        self.buffer_pool.return_buffer(&buffer);

        self.maybe_encrypt(stripe_id, &mut object_data);

        let hash = sha256_hex(&object_data);
        self.stripe_hashes.insert(stripe_id, hash.clone());
        if self.seen_hashes.contains(&hash) {
            debug!(
                "Stripe {} has duplicate hash {}, skipping upload",
                stripe_id, hash
            );
            return Ok(());
        }

        self.seen_hashes.insert(hash.clone());
        let object_key = self.hash_to_object_key(&hash);

        self.archive_store
            .start_put_object(&object_key, object_data);
        self.inflight_puts += 1;

        Ok(())
    }

    fn poll_uploads(&mut self) -> Result<()> {
        let results = self.archive_store.poll_puts();
        for (obj_name, result) in results {
            result?;
            debug!("Completed uploading object {}", obj_name);
            self.inflight_puts = self.inflight_puts.checked_sub(1).ok_or_else(|| {
                crate::ubiblk_error!(ArchiveError {
                    description: format!(
                        "Unexpected upload completion for {} with no inflight puts",
                        obj_name
                    ),
                })
            })?;
        }
        Ok(())
    }

    fn hash_to_object_key(&self, hash: &str) -> String {
        format!("data/{}", hash)
    }

    fn stripe_should_be_archived(&self, stripe_id: usize) -> bool {
        self.stripe_written(stripe_id) || self.stripe_exists_in_source(stripe_id)
    }

    fn stripe_written(&self, stripe_id: usize) -> bool {
        let header = self.metadata.stripe_headers[stripe_id];
        header & metadata_flags::WRITTEN != 0
    }

    fn stripe_fetched(&self, stripe_id: usize) -> bool {
        let header = self.metadata.stripe_headers[stripe_id];
        header & metadata_flags::FETCHED != 0
    }

    fn stripe_exists_in_source(&self, stripe_id: usize) -> bool {
        let header = self.metadata.stripe_headers[stripe_id];
        header & metadata_flags::HAS_SOURCE != 0
    }

    fn stripe_offset(&self, stripe_id: usize) -> u64 {
        (stripe_id as u64) * self.metadata.stripe_sector_count()
    }

    fn put_metadata(&mut self) -> Result<()> {
        let archive_metadata = self.archive_metadata()?;
        let metadata_json = serde_json::to_string(&archive_metadata).map_err(|e| {
            crate::ubiblk_error!(ArchiveError {
                description: format!("Failed to serialize archive metadata: {}", e),
            })
        })?;
        self.archive_store.put_object(
            "metadata.json",
            metadata_json.as_bytes(),
            DEFAULT_ARCHIVE_TIMEOUT,
        )?;
        Ok(())
    }

    fn put_stripe_hashes(&mut self) -> Result<()> {
        let mapping_json = serde_json::to_string(&self.stripe_hashes).map_err(|e| {
            crate::ubiblk_error!(ArchiveError {
                description: format!("Failed to serialize stripes hashes: {}", e),
            })
        })?;
        self.archive_store.put_object(
            "stripe-hashes.json",
            mapping_json.as_bytes(),
            DEFAULT_ARCHIVE_TIMEOUT,
        )?;
        Ok(())
    }

    fn archive_metadata(&self) -> Result<ArchiveMetadata> {
        let encryption_key = if let Some(block_cipher) = self.block_cipher.as_ref() {
            Some(block_cipher.encrypted_keys(&self.kek)?)
        } else {
            None
        };
        let archive_metadata = ArchiveMetadata {
            format_version: ARCHIVE_FORMAT_VERSION,
            stripe_sector_count: self.metadata.stripe_sector_count(),
            encryption_key,
            compression: self.compression.clone(),
        };
        Ok(archive_metadata)
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use crate::{
        archive::mem_store::MemStore,
        block_device::{bdev_test::TestBlockDevice, BlockDevice},
        stripe_source::BlockDeviceStripeSource,
    };

    use super::*;

    const STRIPE_SECTOR_COUNT_SHIFT: u8 = 4;
    const STRIPE_SECTOR_COUNT: u64 = 1 << STRIPE_SECTOR_COUNT_SHIFT;

    fn prep(
        bdev_stripe_count: usize,
        image_stripe_count: usize,
        encrypted: bool,
        fail_stripe_fetches: Vec<usize>,
    ) -> (StripeArchiver, Box<MemStore>) {
        let bdev_size = STRIPE_SECTOR_COUNT * (bdev_stripe_count * SECTOR_SIZE) as u64;
        let metadata = UbiMetadata::new(
            STRIPE_SECTOR_COUNT_SHIFT,
            bdev_stripe_count,
            image_stripe_count,
        );
        let bdev: Box<TestBlockDevice> = Box::new(TestBlockDevice::new(bdev_size));
        for stripe_id in 0..bdev_stripe_count {
            // Use two disjoint byte ranges to distinguish image stripes from
            // stripes that exist only on the backing device: image stripes get
            // bytes in 3..5, and non-image stripes get bytes in 0..2. The
            // modulus 3 keeps the pattern short and predictable for tests.
            let byte = if stripe_id < image_stripe_count {
                (stripe_id % 3 + 3) as u8
            } else {
                (stripe_id % 3) as u8
            };
            let buf = [byte; STRIPE_SECTOR_COUNT as usize * SECTOR_SIZE];
            let len = STRIPE_SECTOR_COUNT as usize * SECTOR_SIZE;
            let offset = stripe_id * len;
            bdev.write(offset, buf.as_slice(), len);
        }
        let stripe_source =
            BlockDeviceStripeSource::new(bdev.clone(), STRIPE_SECTOR_COUNT).unwrap();
        let stripe_source = crate::stripe_source::FlakyStripeSource::new(
            Box::new(stripe_source),
            fail_stripe_fetches
                .into_iter()
                .map(|sid| (sid, 1))
                .collect(),
        );

        let store = Box::new(MemStore::default());

        let archiver = StripeArchiver::new(
            Box::new(stripe_source),
            bdev.as_ref(),
            metadata,
            Box::new(MemStore::new_with_objects(store.objects.clone())),
            encrypted,
            ArchiveCompressionAlgorithm::None,
            KeyEncryptionCipher::default(),
            1,
        )
        .unwrap();

        (archiver, store)
    }

    #[test]
    fn test_stripe_should_be_archived() {
        let (mut archiver, _store) = prep(16, 4, false, Vec::new());
        archiver.metadata.stripe_headers[8] |= metadata_flags::WRITTEN;

        for stripe_id in 0..16 {
            let should_archive = archiver.stripe_should_be_archived(stripe_id);
            if stripe_id == 8 || stripe_id < 4 {
                assert!(should_archive);
            } else {
                assert!(!should_archive);
            }
        }
    }

    #[test]
    fn test_archive_all_no_image_stripes() {
        let (mut archiver, mut store) = prep(16, 0, false, Vec::new());
        archiver.metadata.stripe_headers[2] |= metadata_flags::WRITTEN;
        archiver.metadata.stripe_headers[5] |= metadata_flags::WRITTEN;
        archiver.metadata.stripe_headers[7] |= metadata_flags::WRITTEN;

        archiver.archive_all().unwrap();

        let stored_objects = store.list_objects().unwrap();

        // stripes 2 and 5 have the same data, so they share the same data object
        let stored_objects: std::collections::HashSet<String> =
            stored_objects.into_iter().collect();
        let expected_objects: std::collections::HashSet<String> = [
            "metadata.json".to_string(),
            "stripe-hashes.json".to_string(),
            format!("data/{}", &archiver.stripe_hashes[&2]),
            format!("data/{}", &archiver.stripe_hashes[&7]),
        ]
        .into_iter()
        .collect();
        assert_eq!(stored_objects, expected_objects);

        // verify stripe hashes
        let stripe_hashes = store
            .get_object("stripe-hashes.json", Duration::from_secs(5))
            .unwrap();
        let stripe_hashes: HashMap<usize, String> = serde_json::from_slice(&stripe_hashes).unwrap();
        assert_eq!(stripe_hashes.len(), 3);
        assert_eq!(stripe_hashes[&2], archiver.stripe_hashes[&2]);
        assert_eq!(stripe_hashes[&5], archiver.stripe_hashes[&2]);
        assert_eq!(stripe_hashes[&7], archiver.stripe_hashes[&7]);
    }

    #[test]
    fn test_archive_all_with_image_stripes() {
        let (mut archiver, mut store) = prep(16, 4, false, Vec::new());
        archiver.metadata.stripe_headers[2] &= !metadata_flags::HAS_SOURCE;
        archiver.metadata.stripe_headers[10] |= metadata_flags::WRITTEN;
        archiver.metadata.stripe_headers[12] |= metadata_flags::WRITTEN;

        archiver.archive_all().unwrap();
        let stored_objects = store.list_objects().unwrap();

        // stripes 0 and 3 have the same data, so they share the same data object
        let stored_objects: std::collections::HashSet<String> =
            stored_objects.into_iter().collect();
        let expected_objects: std::collections::HashSet<String> = [
            "metadata.json".to_string(),
            "stripe-hashes.json".to_string(),
            format!("data/{}", &archiver.stripe_hashes[&0]),
            format!("data/{}", &archiver.stripe_hashes[&1]),
            format!("data/{}", &archiver.stripe_hashes[&10]),
            format!("data/{}", &archiver.stripe_hashes[&12]),
        ]
        .into_iter()
        .collect();
        assert_eq!(stored_objects, expected_objects);

        // verify stripe hashes
        let stripe_hashes = store
            .get_object("stripe-hashes.json", Duration::from_secs(5))
            .unwrap();
        let stripe_hashes: HashMap<usize, String> = serde_json::from_slice(&stripe_hashes).unwrap();
        assert_eq!(stripe_hashes.len(), 5);
        assert_eq!(stripe_hashes[&0], archiver.stripe_hashes[&0]);
        assert_eq!(stripe_hashes[&1], archiver.stripe_hashes[&1]);
        assert_eq!(stripe_hashes[&3], archiver.stripe_hashes[&0]);
        assert_eq!(stripe_hashes[&10], archiver.stripe_hashes[&10]);
        assert_eq!(stripe_hashes[&12], archiver.stripe_hashes[&12]);
    }

    #[test]
    fn test_archive_metadata_not_encrypted() {
        let (mut archiver, _store) = prep(4, 4, false, Vec::new());
        archiver.archive_all().unwrap();
        let metadata_bytes = archiver
            .archive_store
            .get_object("metadata.json", Duration::from_secs(5))
            .unwrap();
        let metadata: ArchiveMetadata = serde_json::from_slice(&metadata_bytes).unwrap();
        assert_eq!(metadata.format_version, ARCHIVE_FORMAT_VERSION);
        assert_eq!(metadata.stripe_sector_count, STRIPE_SECTOR_COUNT);
        assert!(metadata.encryption_key.is_none());
    }

    #[test]
    fn test_archive_metadata_encrypted() {
        let (mut archiver, _store) = prep(4, 4, true, Vec::new());
        archiver.archive_all().unwrap();
        let metadata_bytes = archiver
            .archive_store
            .get_object("metadata.json", Duration::from_secs(5))
            .unwrap();
        let metadata: ArchiveMetadata = serde_json::from_slice(&metadata_bytes).unwrap();
        assert_eq!(metadata.format_version, ARCHIVE_FORMAT_VERSION);
        assert_eq!(metadata.stripe_sector_count, STRIPE_SECTOR_COUNT);
        assert!(metadata.encryption_key.is_some());
    }

    #[test]
    fn stripe_fetch_failure() {
        let (mut archiver, _store) = prep(4, 4, false, vec![2]);
        let result = archiver.archive_all();
        assert!(result.is_err());
        let err = result.err().unwrap();
        assert!(err
            .to_string()
            .contains("I/O error while fetching stripe 2"));
    }
}
