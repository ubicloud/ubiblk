use std::time::Duration;

use log::info;

use super::ArchiveStore;
use crate::{
    archive::ArchiveMetadata,
    block_device::{
        shared_buffer, IoChannel, SharedBuffer, UbiMetadata, STRIPE_NO_SOURCE_MASK,
        STRIPE_WRITTEN_MASK,
    },
    crypt::XtsBlockCipher,
    stripe_source::StripeSource,
    utils::hash::sha256_hex,
    vhost_backend::SECTOR_SIZE,
    KeyEncryptionCipher, Result,
};

const STRIPE_ARCHIVER_TIMEOUT: Duration = Duration::from_secs(30);

pub struct StripeArchiver {
    stripe_source: Box<dyn StripeSource>,
    io_channel: Box<dyn IoChannel>,
    metadata: Box<UbiMetadata>,
    archive_store: Box<dyn ArchiveStore>,
    stripe_sector_count: u32,
    block_cipher: XtsBlockCipher,
    kek: KeyEncryptionCipher,
}

impl StripeArchiver {
    pub fn new(
        stripe_source: Box<dyn StripeSource>,
        io_channel: Box<dyn IoChannel>,
        metadata: Box<UbiMetadata>,
        archive_store: Box<dyn ArchiveStore>,
        kek: KeyEncryptionCipher,
    ) -> Result<Self> {
        let stripe_sector_count = 1 << metadata.stripe_sector_count_shift;
        let block_cipher = XtsBlockCipher::random();
        Ok(Self {
            stripe_source,
            io_channel,
            metadata,
            archive_store,
            stripe_sector_count,
            block_cipher,
            kek,
        })
    }

    pub fn archive_all(&mut self) -> crate::Result<()> {
        let stripe_count = self.metadata.stripe_count() as usize;
        for stripe_id in 0..stripe_count {
            if self.stripe_should_be_archived(stripe_id) {
                self.archive_stripe(stripe_id)?;
            }
        }
        self.put_metadata()?;
        Ok(())
    }

    fn archive_stripe(&mut self, stripe_id: usize) -> crate::Result<()> {
        info!("Archiving stripe {}", stripe_id);

        let mut stripe_data = self.fetch_stripe(stripe_id)?;

        let sector_start: u64 = stripe_id as u64 * self.stripe_sector_count as u64;
        self.block_cipher.encrypt(
            &mut stripe_data,
            sector_start,
            self.stripe_sector_count as u64,
        );

        let object_key = self.stripe_object_key(stripe_id, &stripe_data);
        self.archive_store.put_object(&object_key, &stripe_data)?;

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

    fn fetch_stripe(&mut self, stripe_id: usize) -> Result<Vec<u8>> {
        let stripe_len_bytes = (self.stripe_sector_count as usize) * SECTOR_SIZE;

        let buffer = shared_buffer(stripe_len_bytes);

        if self.stripe_written(stripe_id) {
            self.fetch_stripe_from_bdev(stripe_id, buffer.clone())?;
        } else {
            self.fetch_stripe_from_source(stripe_id, buffer.clone())?;
        }

        let result = buffer.borrow().as_slice().to_vec();
        Ok(result)
    }

    fn fetch_stripe_from_bdev(&mut self, stripe_id: usize, buffer: SharedBuffer) -> Result<()> {
        self.io_channel.add_read(
            self.stripe_offset(stripe_id),
            self.stripe_sector_count,
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
        (stripe_id as u64) * (self.stripe_sector_count as u64)
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
        let archive_metadata = ArchiveMetadata {
            stripe_sector_count: self.stripe_sector_count,
            encryption_key: Some(self.block_cipher.keys(self.kek.clone())?),
        };
        Ok(archive_metadata)
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        archive::mem_store::MemStore,
        block_device::{BlockDevice, NullBlockDevice},
        stripe_source::BlockDeviceStripeSource,
    };

    use super::*;

    fn prep(image_stripe_count: usize) -> StripeArchiver {
        let stripe_sector_count_shift = 4;
        let stripe_sector_count = 1 << stripe_sector_count_shift;
        let metadata = UbiMetadata::new(stripe_sector_count_shift, 16, image_stripe_count);
        let bdev_null = NullBlockDevice::new();
        let stripe_source =
            BlockDeviceStripeSource::new(bdev_null.clone(), stripe_sector_count as u64).unwrap();

        let store = Box::new(MemStore::new());

        StripeArchiver::new(
            Box::new(stripe_source),
            bdev_null.create_channel().unwrap(),
            metadata,
            store,
            KeyEncryptionCipher::default(),
        )
        .unwrap()
    }

    #[test]
    fn test_stripe_object_key() {
        let archiver = prep(4);
        let stripe_id = 42;
        let stripe_data = vec![0u8; 4096];
        let key = archiver.stripe_object_key(stripe_id, &stripe_data);
        assert!(key.starts_with("stripe_0000000042_"));
    }

    #[test]
    fn test_stripe_should_be_archived() {
        let mut archiver = prep(4);
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
    fn test_archive_all() {
        let mut archiver = prep(0);
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
}
