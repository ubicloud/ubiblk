use std::collections::HashMap;

use crate::{
    archive::{ArchiveMetadata, ArchiveStore, DEFAULT_ARCHIVE_TIMEOUT},
    block_device::SharedBuffer,
    crypt::XtsBlockCipher,
    utils::hash::sha256_hex,
    KeyEncryptionCipher, Result,
};

use super::StripeSource;

struct PendingRequest {
    stripe_id: usize,
    buffer: SharedBuffer,
    expected_sha256: String,
}

pub struct ArchiveStripeSource {
    store: Box<dyn ArchiveStore>,
    xts_cipher: Option<XtsBlockCipher>,
    stripe_object_names: HashMap<usize, String>,
    max_stripe_id: usize,
    stripe_sector_count: u64,
    finished_requests: Vec<(usize, bool)>,
    pending_requests: HashMap<String, PendingRequest>,
}

impl ArchiveStripeSource {
    pub fn new(mut store: Box<dyn ArchiveStore>, kek: KeyEncryptionCipher) -> Result<Self> {
        let metadata: ArchiveMetadata = Self::fetch_metadata(store.as_mut())?;
        let stripe_object_names = Self::fetch_stripe_info(store.as_ref())?;
        let max_stripe_id = stripe_object_names.keys().max().cloned().unwrap_or(0);
        let stripe_sector_count = metadata.stripe_sector_count;
        let finished_requests = Vec::new();
        let pending_requests = HashMap::new();
        let xts_cipher = match metadata.encryption_key {
            None => None,
            Some(key) => Some(XtsBlockCipher::from_encrypted(key.0, key.1, &kek)?),
        };
        Ok(Self {
            store,
            xts_cipher,
            stripe_object_names,
            max_stripe_id,
            stripe_sector_count,
            finished_requests,
            pending_requests,
        })
    }

    fn fetch_metadata(store: &mut dyn ArchiveStore) -> Result<ArchiveMetadata> {
        let bytes = store.get_object("metadata.yaml", DEFAULT_ARCHIVE_TIMEOUT)?;
        let metadata: ArchiveMetadata = serde_yaml::from_slice(&bytes).map_err(|e| {
            crate::ubiblk_error!(MetadataError {
                description: format!("failed to parse archive metadata: {}", e),
            })
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
                return Err(crate::ubiblk_error!(ArchiveError {
                    description: format!(
                        "Duplicate stripe object for stripe ID {}: {}",
                        stripe_id, object_name
                    ),
                }));
            }
            stripe_object_names.insert(stripe_id, object_name);
        }
        Ok(stripe_object_names)
    }

    pub fn parse_stripe_object_name(object_name: &str) -> Result<(usize, String)> {
        let parts: Vec<&str> = object_name.split('_').collect();
        if parts.len() != 3 || parts[0] != "stripe" {
            return Err(crate::ubiblk_error!(ArchiveError {
                description: format!("Invalid stripe object name: {}", object_name),
            }));
        }
        let stripe_id = parts[1].parse::<usize>().map_err(|_| {
            crate::ubiblk_error!(ArchiveError {
                description: format!("Invalid stripe object name: {}", object_name),
            })
        })?;
        let sha256 = parts[2].to_string();
        Ok((stripe_id, sha256))
    }

    fn start_fetch_stripe(
        &mut self,
        stripe_id: usize,
        filename: String,
        buffer: SharedBuffer,
    ) -> Result<()> {
        let (stripe_id_parsed, expected_sha256) = Self::parse_stripe_object_name(&filename)?;
        if stripe_id_parsed != stripe_id {
            return Err(crate::ubiblk_error!(ArchiveError {
                description: format!(
                    "Stripe ID {} does not match parsed ID {} from filename {}",
                    stripe_id, stripe_id_parsed, &filename
                ),
            }));
        }
        if self.pending_requests.contains_key(&filename) {
            return Err(crate::ubiblk_error!(ArchiveError {
                description: format!("Stripe {} is already being fetched", stripe_id),
            }));
        }
        self.store.start_get_object(&filename);
        self.pending_requests.insert(
            filename,
            PendingRequest {
                stripe_id,
                buffer,
                expected_sha256,
            },
        );
        Ok(())
    }

    fn finish_stripe_request(
        &mut self,
        stripe_id: usize,
        data: &[u8],
        expected_sha256: &str,
        buffer: SharedBuffer,
    ) -> Result<()> {
        Self::verify_stripe_data(stripe_id, data, expected_sha256)?;

        let mut buf_ref = buffer.borrow_mut();
        let buf = buf_ref.as_mut_slice();
        if data.len() > buf.len() {
            return Err(crate::ubiblk_error!(ArchiveError {
                description: format!(
                    "Stripe {} data size {} exceeds buffer size {}",
                    stripe_id,
                    data.len(),
                    buf.len()
                ),
            }));
        }
        buf[..data.len()].copy_from_slice(data);

        if data.len() < buf.len() {
            buf[data.len()..].fill(0);
        }

        if let Some(cipher) = self.xts_cipher.as_mut() {
            let sector_start = (stripe_id as u64) * self.stripe_sector_count;
            cipher.decrypt(buf, sector_start, self.stripe_sector_count);
        }

        Ok(())
    }

    fn verify_stripe_data(stripe_id: usize, data: &[u8], expected_sha256: &str) -> Result<()> {
        let computed_hash = sha256_hex(data);
        if computed_hash != expected_sha256 {
            return Err(crate::ubiblk_error!(ArchiveError {
                description: format!("sha256 hash mismatch for stripe {}", stripe_id),
            }));
        }
        Ok(())
    }
}

impl StripeSource for ArchiveStripeSource {
    fn request(&mut self, stripe_id: usize, buffer: SharedBuffer) -> Result<()> {
        let maybe_filename = self.stripe_object_names.get(&stripe_id).cloned();
        match maybe_filename {
            Some(filename) => self.start_fetch_stripe(stripe_id, filename, buffer),
            None => {
                buffer.borrow_mut().as_mut_slice().fill(0);
                self.finished_requests.push((stripe_id, true));
                Ok(())
            }
        }
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        let completions = self.store.poll_gets();
        for (object_name, result) in completions {
            if let Some(pending) = self.pending_requests.remove(&object_name) {
                let success = match result {
                    Ok(data) => self
                        .finish_stripe_request(
                            pending.stripe_id,
                            &data,
                            &pending.expected_sha256,
                            pending.buffer,
                        )
                        .is_ok(),
                    Err(e) => {
                        log::error!("Failed to fetch stripe {}: {}", pending.stripe_id, e);
                        false
                    }
                };
                self.finished_requests.push((pending.stripe_id, success));
            } else {
                log::error!(
                    "Received unexpected completed get for object {}",
                    object_name
                );
            }
        }
        self.finished_requests.drain(..).collect()
    }

    fn busy(&self) -> bool {
        !self.pending_requests.is_empty() || !self.finished_requests.is_empty()
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
    use std::rc::Rc;
    use std::time::Duration;

    use crate::UbiblkError;
    use crate::{
        backends::SECTOR_SIZE,
        block_device::{
            bdev_test::TestBlockDevice, metadata_flags, shared_buffer, BlockDevice, UbiMetadata,
        },
        stripe_source::BlockDeviceStripeSource,
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

    fn clone_memstore(store: &MemStore) -> Box<MemStore> {
        Box::new(MemStore::new_with_objects(Rc::clone(&store.objects)))
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
            metadata.stripe_headers[stripe_id] |= metadata_flags::WRITTEN;
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
            clone_memstore(store.as_ref()),
            encrypted,
            kek,
            1,
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
        let mut source = ArchiveStripeSource::new(clone_memstore(&setup.store), kek).unwrap();

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
        setup
            .store
            .put_object("unexpected_item", b"data", Duration::from_secs(5))
            .unwrap();
        let result = ArchiveStripeSource::new(clone_memstore(&setup.store), kek);
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
            .put_object(
                "stripe_0000000002_invalidhash",
                b"corrupted data",
                Duration::from_secs(5),
            )
            .unwrap();
        let result = ArchiveStripeSource::new(clone_memstore(&setup.store), kek);
        assert!(result.is_ok());

        let mut source = result.unwrap();

        let buf = shared_buffer((STRIPE_SECTOR_COUNT * SECTOR_SIZE as u64) as usize);

        // Stripe 0 & 1 should be fine
        assert!(source.request(0, buf.clone()).is_ok());
        assert!(source.request(1, buf.clone()).is_ok());

        // Stripe 2 should error out due to hash mismatch
        assert!(source.request(2, buf.clone()).is_ok());

        let completions = source.poll();
        assert_eq!(completions.len(), 3);
        for (stripe_id, success) in completions {
            match stripe_id {
                0 | 1 => assert!(success, "stripe {} should succeed", stripe_id),
                2 => assert!(!success, "stripe 2 should fail"),
                _ => panic!("unexpected stripe id {}", stripe_id),
            }
        }
    }

    #[test]
    fn test_errors_on_duplicate_stripe_object() {
        let kek = KeyEncryptionCipher::default();
        let mut setup = prep(4, 2, false, &[0, 1], kek.clone());
        setup.archiver.archive_all().unwrap();

        // Add duplicate stripe object
        setup
            .store
            .put_object(
                "stripe_0000000001_somehash",
                b"some data",
                Duration::from_secs(5),
            )
            .unwrap();

        let result = ArchiveStripeSource::new(clone_memstore(&setup.store), kek);
        assert!(result.is_err());
        assert!(result
            .err()
            .unwrap()
            .to_string()
            .contains("Duplicate stripe object for stripe ID 1"));
    }

    #[test]
    fn test_errors_on_duplicate_request() {
        let kek = KeyEncryptionCipher::default();
        let mut setup = prep(4, 2, false, &[0], kek.clone());
        setup.archiver.archive_all().unwrap();

        let mut source = ArchiveStripeSource::new(clone_memstore(&setup.store), kek).unwrap();
        let buf = shared_buffer((STRIPE_SECTOR_COUNT * SECTOR_SIZE as u64) as usize);
        source.request(0, buf.clone()).unwrap();
        let err = source.request(0, buf).unwrap_err();
        assert!(matches!(err, UbiblkError::ArchiveError { .. }));
    }
}
