use std::time::Duration;

use log::{debug, info};

use super::ArchiveStore;
use crate::{
    archive::ArchiveMetadata,
    block_device::{
        shared_buffer, BlockDevice, IoChannel, SharedBuffer, UbiMetadata, STRIPE_NO_SOURCE_MASK,
        STRIPE_WRITTEN_MASK,
    },
    crypt::XtsBlockCipher,
    stripe_source::StripeSource,
    utils::hash::sha256_hex,
    vhost_backend::SECTOR_SIZE,
    KeyEncryptionCipher, Result,
};

// Timeout used for both fetching stripes from the stripe source and
// reading/writing them on the underlying block device. 30 seconds is chosen as
// a conservative upper bound.
const STRIPE_ARCHIVER_TIMEOUT: Duration = Duration::from_secs(30);

pub struct StripeArchiver {
    stripe_source: Box<dyn StripeSource>,
    io_channel: Box<dyn IoChannel>,
    stripe_count: usize,
    metadata: Box<UbiMetadata>,
    archive_store: Box<dyn ArchiveStore>,
    block_cipher: Option<XtsBlockCipher>,
    kek: KeyEncryptionCipher,
}

impl StripeArchiver {
    pub fn new(
        stripe_source: Box<dyn StripeSource>,
        bdev: &dyn BlockDevice,
        metadata: Box<UbiMetadata>,
        archive_store: Box<dyn ArchiveStore>,
        encrypt: bool,
        kek: KeyEncryptionCipher,
    ) -> Result<Self> {
        let block_cipher = if encrypt {
            Some(XtsBlockCipher::random()?)
        } else {
            None
        };
        let stripe_count = bdev.stripe_count(metadata.stripe_sector_count());
        Ok(Self {
            stripe_source,
            io_channel: bdev.create_channel()?,
            metadata,
            archive_store,
            block_cipher,
            kek,
            stripe_count,
        })
    }

    pub fn archive_all(&mut self) -> crate::Result<()> {
        for stripe_id in 0..self.stripe_count {
            if self.stripe_should_be_archived(stripe_id) {
                self.archive_stripe(stripe_id)?;
            }
        }
        self.put_metadata()?;
        Ok(())
    }

    fn archive_stripe(&mut self, stripe_id: usize) -> crate::Result<()> {
        info!("Archiving stripe {}", stripe_id);

        let stripe_data_rc = self.fetch_stripe(stripe_id)?;
        let mut stripe_data = stripe_data_rc.borrow_mut();

        let sector_offset = self.stripe_offset(stripe_id);
        if let Some(block_cipher) = self.block_cipher.as_mut() {
            block_cipher.encrypt(
                stripe_data.as_mut_slice(),
                sector_offset,
                self.metadata.stripe_sector_count(),
            );
        }

        let object_key = self.stripe_object_key(stripe_id, stripe_data.as_mut_slice());
        self.archive_store
            .put_object(&object_key, stripe_data.as_mut_slice())?;

        Ok(())
    }

    fn stripe_object_key(&self, stripe_id: usize, stripe_data: &[u8]) -> String {
        let hash = sha256_hex(stripe_data);
        format!("stripe_{:010}_{}", stripe_id, hash)
    }

    fn stripe_should_be_archived(&self, stripe_id: usize) -> bool {
        self.stripe_written(stripe_id) || self.stripe_exists_in_source(stripe_id)
    }

    fn stripe_written(&self, stripe_id: usize) -> bool {
        let header = self.metadata.stripe_headers[stripe_id];
        header & STRIPE_WRITTEN_MASK != 0
    }

    fn stripe_exists_in_source(&self, stripe_id: usize) -> bool {
        let header = self.metadata.stripe_headers[stripe_id];
        header & STRIPE_NO_SOURCE_MASK == 0
    }

    fn fetch_stripe_from_source(&mut self, stripe_id: usize, buffer: SharedBuffer) -> Result<()> {
        self.stripe_source.request(stripe_id, buffer.clone())?;
        self.stripe_source
            .wait_for_stripe(stripe_id, STRIPE_ARCHIVER_TIMEOUT)?;
        Ok(())
    }

    fn fetch_stripe(&mut self, stripe_id: usize) -> Result<SharedBuffer> {
        let stripe_len_bytes = (self.metadata.stripe_sector_count() as usize) * SECTOR_SIZE;

        let buffer = shared_buffer(stripe_len_bytes);

        if self.stripe_written(stripe_id) {
            debug!("Fetching stripe {} from block device", stripe_id,);
            self.fetch_stripe_from_bdev(stripe_id, buffer.clone())?;
        } else {
            debug!("Fetching stripe {} from image", stripe_id,);
            self.fetch_stripe_from_source(stripe_id, buffer.clone())?;
        }

        Ok(buffer)
    }

    fn fetch_stripe_from_bdev(&mut self, stripe_id: usize, buffer: SharedBuffer) -> Result<()> {
        self.io_channel.add_read(
            self.stripe_offset(stripe_id),
            self.metadata.stripe_sector_count() as u32,
            buffer.clone(),
            stripe_id,
        );
        self.io_channel.submit()?;
        crate::block_device::wait_for_completion(
            self.io_channel.as_mut(),
            stripe_id,
            STRIPE_ARCHIVER_TIMEOUT,
        )?;
        Ok(())
    }

    fn stripe_offset(&self, stripe_id: usize) -> u64 {
        (stripe_id as u64) * self.metadata.stripe_sector_count()
    }

    fn put_metadata(&mut self) -> Result<()> {
        let archive_metadata = self.archive_metadata()?;
        let metadata_yaml = serde_yaml::to_string(&archive_metadata).map_err(|e| {
            crate::UbiblkError::ArchiveError {
                description: format!("Failed to serialize archive metadata: {}", e),
            }
        })?;
        self.archive_store
            .put_object("metadata.yaml", metadata_yaml.as_bytes())?;
        Ok(())
    }

    fn archive_metadata(&self) -> Result<ArchiveMetadata> {
        let encryption_key = if let Some(block_cipher) = self.block_cipher.as_ref() {
            Some(block_cipher.encrypted_keys(&self.kek)?)
        } else {
            None
        };
        let archive_metadata = ArchiveMetadata {
            stripe_sector_count: self.metadata.stripe_sector_count(),
            encryption_key,
        };
        Ok(archive_metadata)
    }
}

#[cfg(test)]
mod tests {
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
    ) -> StripeArchiver {
        let bdev_size = STRIPE_SECTOR_COUNT * (bdev_stripe_count * SECTOR_SIZE) as u64;
        let metadata = UbiMetadata::new(
            STRIPE_SECTOR_COUNT_SHIFT,
            bdev_stripe_count,
            image_stripe_count,
        );
        let bdev: Box<TestBlockDevice> = Box::new(TestBlockDevice::new(bdev_size));
        let stripe_source =
            BlockDeviceStripeSource::new(bdev.clone(), STRIPE_SECTOR_COUNT).unwrap();
        let store = Box::new(MemStore::new());

        StripeArchiver::new(
            Box::new(stripe_source),
            bdev.as_ref(),
            metadata,
            store,
            encrypted,
            KeyEncryptionCipher::default(),
        )
        .unwrap()
    }

    #[test]
    fn test_stripe_object_key() {
        let archiver = prep(4, 4, false);
        let stripe_id = 42;
        let stripe_data = vec![0u8; 4096];
        let key = archiver.stripe_object_key(stripe_id, &stripe_data);
        assert!(key.starts_with("stripe_0000000042_"));
    }

    #[test]
    fn test_stripe_should_be_archived() {
        let mut archiver = prep(16, 4, false);
        archiver.metadata.stripe_headers[8] |= STRIPE_WRITTEN_MASK;

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
        let mut archiver = prep(16, 0, false);
        archiver.metadata.stripe_headers[2] |= STRIPE_WRITTEN_MASK;
        archiver.metadata.stripe_headers[5] |= STRIPE_WRITTEN_MASK;

        archiver.archive_all().unwrap();

        let mut stored_objects = archiver.archive_store.list_objects().unwrap();
        stored_objects.sort();

        assert_eq!(stored_objects.len(), 3);
        assert_eq!(stored_objects[0], "metadata.yaml");
        assert!(stored_objects[1].starts_with("stripe_0000000002_"));
        assert!(stored_objects[2].starts_with("stripe_0000000005_"));
    }

    #[test]
    fn test_archive_all_with_image_stripes() {
        let mut archiver = prep(16, 4, false);
        archiver.metadata.stripe_headers[2] |= STRIPE_NO_SOURCE_MASK;
        archiver.metadata.stripe_headers[10] |= STRIPE_WRITTEN_MASK;
        archiver.metadata.stripe_headers[12] |= STRIPE_WRITTEN_MASK;

        archiver.archive_all().unwrap();
        let mut stored_objects = archiver.archive_store.list_objects().unwrap();
        stored_objects.sort();

        assert_eq!(stored_objects.len(), 6);
        assert_eq!(stored_objects[0], "metadata.yaml");
        assert!(stored_objects[1].starts_with("stripe_0000000000_"));
        assert!(stored_objects[2].starts_with("stripe_0000000001_"));
        assert!(stored_objects[3].starts_with("stripe_0000000003_"));
        assert!(stored_objects[4].starts_with("stripe_0000000010_"));
        assert!(stored_objects[5].starts_with("stripe_0000000012_"));
    }

    #[test]
    fn test_archive_metadata_not_encrypted() {
        let mut archiver = prep(4, 4, false);
        archiver.archive_all().unwrap();
        let metadata_bytes = archiver.archive_store.get_object("metadata.yaml").unwrap();
        let metadata: ArchiveMetadata = serde_yaml::from_slice(&metadata_bytes).unwrap();
        assert_eq!(metadata.stripe_sector_count, STRIPE_SECTOR_COUNT);
        assert!(metadata.encryption_key.is_none());
    }

    #[test]
    fn test_archive_metadata_encrypted() {
        let mut archiver = prep(4, 4, true);
        archiver.archive_all().unwrap();
        let metadata_bytes = archiver.archive_store.get_object("metadata.yaml").unwrap();
        let metadata: ArchiveMetadata = serde_yaml::from_slice(&metadata_bytes).unwrap();
        assert_eq!(metadata.stripe_sector_count, STRIPE_SECTOR_COUNT);
        assert!(metadata.encryption_key.is_some());
    }

    #[test]
    fn test_object_key_large_stripe_id() {
        let archiver = prep(10, 0, false);
        let stripe_id = 1_234_567_890_123usize;
        let stripe_data = vec![0u8; 4096];
        let key = archiver.stripe_object_key(stripe_id, &stripe_data);
        assert!(key.starts_with("stripe_1234567890123_"));
    }
}
