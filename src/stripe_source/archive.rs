use std::collections::HashMap;

use crate::{
    archive::{ArchiveMetadata, ArchiveStore},
    block_device::SharedBuffer,
    crypt::XtsBlockCipher,
    utils::hash::sha256_hex,
    KeyEncryptionCipher, Result, UbiblkError,
};

use super::StripeSource;

pub struct ArchiveStripeSource {
    store: Box<dyn ArchiveStore>,
    xts_cipher: Option<XtsBlockCipher>,
    stripe_object_names: HashMap<usize, String>,
    max_stripe_id: usize,
    stripe_sector_count: u64,
    finished_requests: Vec<(usize, bool)>,
}

impl ArchiveStripeSource {
    pub fn new(store: Box<dyn ArchiveStore>, kek: KeyEncryptionCipher) -> Result<Self> {
        let metadata: ArchiveMetadata = Self::fetch_metadata(store.as_ref())?;
        let stripe_object_names = Self::fetch_stripe_info(store.as_ref())?;
        let max_stripe_id = stripe_object_names.keys().max().cloned().unwrap_or(0);
        let stripe_sector_count = metadata.stripe_sector_count;
        let finished_requests = Vec::new();
        let xts_cipher = match metadata.encryption_key {
            None => None,
            Some(key) => Some(XtsBlockCipher::new(key.0, key.1, kek)?),
        };
        Ok(Self {
            store,
            xts_cipher,
            stripe_object_names,
            max_stripe_id,
            stripe_sector_count,
            finished_requests,
        })
    }

    fn fetch_metadata(store: &dyn ArchiveStore) -> Result<ArchiveMetadata> {
        let bytes = store.get_object("metadata.yaml")?;
        let metadata: ArchiveMetadata =
            serde_yaml::from_slice(&bytes).map_err(|e| UbiblkError::MetadataError {
                description: format!("failed to parse archive metadata: {}", e),
            })?;
        Ok(metadata)
    }

    fn fetch_stripe_info(store: &dyn ArchiveStore) -> Result<HashMap<usize, String>> {
        let object_list = store.list_objects()?;
        let mut stripe_object_names = HashMap::new();
        for object_name in object_list {
            if object_name == "metadata.yaml" {
                continue;
            }
            let (stripe_id, _sha256) = Self::parse_stripe_object_name(&object_name)?;
            if stripe_object_names.contains_key(&stripe_id) {
                return Err(UbiblkError::ArchiveError {
                    description: format!(
                        "Duplicate stripe object for stripe ID {}: {}",
                        stripe_id, object_name
                    ),
                });
            }
            stripe_object_names.insert(stripe_id, object_name);
        }
        Ok(stripe_object_names)
    }

    fn parse_stripe_object_name(object_name: &str) -> Result<(usize, String)> {
        let parts: Vec<&str> = object_name.split('_').collect();
        if parts.len() != 3 || parts[0] != "stripe" {
            return Err(UbiblkError::ArchiveError {
                description: format!("Invalid stripe object name: {}", object_name),
            });
        }
        let stripe_id = parts[1]
            .parse::<usize>()
            .map_err(|_| UbiblkError::ArchiveError {
                description: format!("Invalid stripe object name: {}", object_name),
            })?;
        let sha256 = parts[2].to_string();
        Ok((stripe_id, sha256))
    }

    fn fetch_stripe(
        &mut self,
        stripe_id: usize,
        object_name: &str,
        buffer: SharedBuffer,
    ) -> Result<()> {
        let (stripe_id_in_name, sha256) = Self::parse_stripe_object_name(object_name)?;
        if stripe_id != stripe_id_in_name {
            return Err(UbiblkError::ArchiveError {
                description: format!(
                    "Stripe ID mismatch: expected {}, found {} in object name {}",
                    stripe_id, stripe_id_in_name, object_name
                ),
            });
        }

        let data = self.store.get_object(object_name)?;
        Self::verify_stripe_data(stripe_id, &data, &sha256)?;

        let mut buf_ref = buffer.borrow_mut();
        let buf = buf_ref.as_mut_slice();
        if data.len() > buf.len() {
            return Err(UbiblkError::ArchiveError {
                description: format!(
                    "Stripe {} data size {} exceeds buffer size {}",
                    stripe_id,
                    data.len(),
                    buf.len()
                ),
            });
        }
        buf[..data.len()].copy_from_slice(&data);

        if data.len() < buf.len() {
            buf[data.len()..].fill(0);
        }

        if let Some(cipher) = self.xts_cipher.as_mut() {
            let sector_start = (stripe_id as u64) * self.stripe_sector_count;
            cipher.decrypt(buf, sector_start, self.stripe_sector_count);
        }

        self.finished_requests.push((stripe_id, true));
        Ok(())
    }

    fn verify_stripe_data(stripe_id: usize, data: &[u8], expected_sha256: &str) -> Result<()> {
        let computed_hash = sha256_hex(data);
        if computed_hash != expected_sha256 {
            return Err(UbiblkError::ArchiveError {
                description: format!("sha256 hash mismatch for stripe {}", stripe_id),
            });
        }
        Ok(())
    }
}

impl StripeSource for ArchiveStripeSource {
    fn request(&mut self, stripe_id: usize, buffer: SharedBuffer) -> Result<()> {
        let maybe_filename = self.stripe_object_names.get(&stripe_id).cloned();
        match maybe_filename {
            Some(filename) => self.fetch_stripe(stripe_id, &filename, buffer),
            None => {
                buffer.borrow_mut().as_mut_slice().fill(0);
                self.finished_requests.push((stripe_id, true));
                Ok(())
            }
        }
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        self.finished_requests.drain(..).collect()
    }

    fn busy(&self) -> bool {
        !self.finished_requests.is_empty()
    }

    fn sector_count(&self) -> u64 {
        if self.stripe_object_names.is_empty() {
            0
        } else {
            (self.max_stripe_id + 1) as u64 * self.stripe_sector_count
        }
    }

    fn has_stripe(&self, stripe_id: usize) -> bool {
        self.stripe_object_names.contains_key(&stripe_id)
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        block_device::{
            bdev_test::TestBlockDevice, shared_buffer, BlockDevice, UbiMetadata,
            METADATA_STRIPE_WRITTEN_BITMASK,
        },
        stripe_source::BlockDeviceStripeSource,
        vhost_backend::SECTOR_SIZE,
    };

    use super::*;
    use crate::archive::{MemStore, StripeArchiver};

    const STRIPE_SECTOR_COUNT_SHIFT: u8 = 4;
    const STRIPE_SECTOR_COUNT: u64 = 1 << STRIPE_SECTOR_COUNT_SHIFT;

    struct Setup {
        store: Box<MemStore>,
        disk_bdev: Box<TestBlockDevice>,
        image_bdev: Box<TestBlockDevice>,
        archiver: StripeArchiver,
    }

    fn prep(
        bdev_stripe_count: usize,
        image_stripe_count: usize,
        encrypted: bool,
        written_stripes: &[usize],
        kek: KeyEncryptionCipher,
    ) -> Setup {
        let mut metadata = UbiMetadata::new(
            STRIPE_SECTOR_COUNT_SHIFT,
            bdev_stripe_count,
            image_stripe_count,
        );
        for &stripe_id in written_stripes {
            metadata.stripe_headers[stripe_id] |= METADATA_STRIPE_WRITTEN_BITMASK;
        }

        let bdev_size = STRIPE_SECTOR_COUNT * (bdev_stripe_count * SECTOR_SIZE) as u64;
        let disk_bdev: Box<TestBlockDevice> = Box::new(TestBlockDevice::new(bdev_size));

        let image_bdev_size = STRIPE_SECTOR_COUNT * (image_stripe_count * SECTOR_SIZE) as u64;
        let image_bdev: Box<TestBlockDevice> = Box::new(TestBlockDevice::new(image_bdev_size));
        let stripe_source =
            BlockDeviceStripeSource::new(image_bdev.clone(), STRIPE_SECTOR_COUNT).unwrap();

        let store = Box::new(MemStore::new());

        let archiver = StripeArchiver::new(
            Box::new(stripe_source),
            disk_bdev.as_ref(),
            metadata,
            store.clone(),
            encrypted,
            kek,
        )
        .unwrap();

        Setup {
            store,
            disk_bdev,
            image_bdev,
            archiver,
        }
    }

    fn do_test_archive_stripe_source(encrypted: bool, kek: KeyEncryptionCipher) {
        let bdev_stripe_count = 16;
        let image_stripe_count = 10;
        let written_stripes = vec![2, 7, 11, 14];
        let expected_sector_count = 15 * STRIPE_SECTOR_COUNT;
        let mut setup = prep(
            bdev_stripe_count,
            image_stripe_count,
            encrypted,
            &written_stripes,
            kek.clone(),
        );

        // populate image bdev before archiving
        for stripe_id in 0..image_stripe_count {
            for sector in 0..STRIPE_SECTOR_COUNT {
                let offset = (stripe_id as u64 * STRIPE_SECTOR_COUNT + sector) * SECTOR_SIZE as u64;
                let expected_byte = ((stripe_id + sector as usize) % 256) as u8;
                let buf = vec![expected_byte; SECTOR_SIZE];
                let mut mem = setup.image_bdev.mem.write().unwrap();
                mem[offset as usize..(offset as usize + SECTOR_SIZE)].copy_from_slice(&buf);
            }
        }

        // populate disk bdev before archiving
        for stripe_id in 0..bdev_stripe_count {
            for sector in 0..STRIPE_SECTOR_COUNT {
                let offset = (stripe_id as u64 * STRIPE_SECTOR_COUNT + sector) * SECTOR_SIZE as u64;
                let expected_byte = ((3 + stripe_id + sector as usize) % 256) as u8;
                let buf = vec![expected_byte; SECTOR_SIZE];
                let mut mem = setup.disk_bdev.mem.write().unwrap();
                mem[offset as usize..(offset as usize + SECTOR_SIZE)].copy_from_slice(&buf);
            }
        }

        setup.archiver.archive_all().unwrap();
        let mut source = ArchiveStripeSource::new(setup.store.clone(), kek).unwrap();

        assert_eq!(
            source.sector_count(),
            expected_sector_count,
            "sector count mismatch"
        );

        // read back stripes
        for stripe_id in 0..bdev_stripe_count {
            let buffer = shared_buffer((STRIPE_SECTOR_COUNT * SECTOR_SIZE as u64) as usize);
            source.request(stripe_id, buffer.clone()).unwrap();
            assert!(source.busy());
            let completions = source.poll();
            assert_eq!(completions.len(), 1);
            let (completed_stripe_id, success) = completions[0];
            assert_eq!(completed_stripe_id, stripe_id, "stripe id mismatch");
            assert!(success, "stripe read failed");

            let buf_ref = buffer.borrow();
            let buf = buf_ref.as_slice();
            for sector in 0..STRIPE_SECTOR_COUNT {
                let offset = (sector as usize) * SECTOR_SIZE;
                let expected_byte = if written_stripes.contains(&stripe_id) {
                    ((3 + stripe_id + sector as usize) % 256) as u8
                } else if stripe_id < image_stripe_count {
                    ((stripe_id + sector as usize) % 256) as u8
                } else {
                    0u8
                };
                for b in &buf[offset..offset + SECTOR_SIZE] {
                    assert_eq!(
                        *b, expected_byte,
                        "mismatch at stripe {}, sector {}",
                        stripe_id, sector
                    );
                }
            }
        }
    }

    #[test]
    fn test_archive_stripe_source_encrypted_no_key_encryption() {
        do_test_archive_stripe_source(true, KeyEncryptionCipher::default());
    }

    #[test]
    fn test_archive_stripe_source_encrypted_with_key_encryption() {
        let kek = KeyEncryptionCipher {
            method: crate::CipherMethod::Aes256Gcm,
            key: Some(vec![0xAB; 32]),
            init_vector: Some(vec![0xCD; 12]),
            auth_data: Some("ubiblk_test".as_bytes().to_vec()),
        };
        do_test_archive_stripe_source(true, kek);
    }

    #[test]
    fn test_archive_stripe_source_unencrypted() {
        do_test_archive_stripe_source(false, KeyEncryptionCipher::default());
    }

    #[test]
    fn test_errors_on_empty_source() {
        let store = Box::new(MemStore::new());
        let kek = KeyEncryptionCipher::default();
        let result = ArchiveStripeSource::new(store, kek);
        assert!(
            result.is_err()
                && result
                    .err()
                    .unwrap()
                    .to_string()
                    .contains("Object metadata.yaml not found")
        );
    }

    #[test]
    fn test_errors_on_unexpected_item() {
        let kek = KeyEncryptionCipher::default();
        let mut setup = prep(4, 2, false, &[0, 1], kek.clone());
        setup.archiver.archive_all().unwrap();
        setup.store.put_object("unexpected_item", b"data").unwrap();
        let result = ArchiveStripeSource::new(setup.store.clone(), kek);
        assert!(
            result.is_err()
                && result
                    .err()
                    .unwrap()
                    .to_string()
                    .contains("Invalid stripe object name: unexpected_item")
        );
    }

    #[test]
    fn test_errors_on_hash_mismatch() {
        let kek = KeyEncryptionCipher::default();
        let mut setup = prep(4, 2, false, &[0, 1], kek.clone());
        setup.archiver.archive_all().unwrap();

        // Corrupt one stripe object
        setup
            .store
            .put_object("stripe_0000000002_invalidhash", b"corrupted data")
            .unwrap();
        let result = ArchiveStripeSource::new(setup.store.clone(), kek);
        assert!(result.is_ok());

        let mut source = result.unwrap();

        let buf = shared_buffer((STRIPE_SECTOR_COUNT * SECTOR_SIZE as u64) as usize);

        // Stripe 0 & 1 should be fine
        assert!(source.request(0, buf.clone()).is_ok());
        assert!(source.request(1, buf.clone()).is_ok());

        // Stripe 2 should error out due to hash mismatch
        let result = source.request(2, buf.clone());
        assert!(result.is_err());
        assert!(result
            .err()
            .unwrap()
            .to_string()
            .contains("sha256 hash mismatch for stripe 2"));
    }

    #[test]
    fn test_errors_on_duplicate_stripe_object() {
        let kek = KeyEncryptionCipher::default();
        let mut setup = prep(4, 2, false, &[0, 1], kek.clone());
        setup.archiver.archive_all().unwrap();

        // Add duplicate stripe object
        setup
            .store
            .put_object("stripe_0000000001_somehash", b"some data")
            .unwrap();

        let result = ArchiveStripeSource::new(setup.store.clone(), kek);
        assert!(result.is_err());
        assert!(result
            .err()
            .unwrap()
            .to_string()
            .contains("Duplicate stripe object for stripe ID 1"));
    }
}
