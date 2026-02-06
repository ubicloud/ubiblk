use std::collections::HashMap;

use ubiblk_macros::error_context;

use crate::{
    archive::{
        deserialize_stripe_mapping, validate_format_version, ArchiveCompressionAlgorithm,
        ArchiveMetadata, ArchiveStore, StripeContentMap, StripeContentSpecifier,
        DEFAULT_ARCHIVE_TIMEOUT,
    },
    backends::SECTOR_SIZE,
    block_device::SharedBuffer,
    crypt::XtsBlockCipher,
    utils::hash::sha256_bytes,
    KeyEncryptionCipher, Result,
};

use super::StripeSource;

struct PendingRequest {
    pending_stripes: Vec<(usize, SharedBuffer)>,
    expected_sha256: [u8; 32],
}

pub struct ArchiveStripeSource {
    store: Box<dyn ArchiveStore>,
    xts_cipher: Option<XtsBlockCipher>,
    stripe_hashes: StripeContentMap,
    max_stripe_id: usize,
    stripe_sector_count: u64,
    compression: ArchiveCompressionAlgorithm,
    finished_requests: Vec<(usize, bool)>,
    pending_requests: HashMap<String, PendingRequest>,
}

impl ArchiveStripeSource {
    #[error_context("Failed to create ArchiveStripeSource")]
    pub fn new(mut store: Box<dyn ArchiveStore>, kek: KeyEncryptionCipher) -> Result<Self> {
        let metadata: ArchiveMetadata = Self::fetch_metadata(store.as_mut())?;
        let hmac_key = Self::decrypt_hmac_key(&metadata, &kek)?;
        let xts_cipher = match metadata.encryption_key {
            None => None,
            Some(key) => Some(XtsBlockCipher::from_encrypted(key.0, key.1, &kek)?),
        };
        let stripe_hashes =
            Self::fetch_stripe_hashes(store.as_mut(), hmac_key.as_ref(), xts_cipher.clone())?;
        let max_stripe_id = stripe_hashes.keys().max().cloned().unwrap_or(0);
        let stripe_sector_count = metadata.stripe_sector_count;
        let finished_requests = Vec::new();
        let pending_requests = HashMap::new();
        Ok(Self {
            store,
            xts_cipher,
            stripe_hashes,
            max_stripe_id,
            stripe_sector_count,
            finished_requests,
            pending_requests,
            compression: metadata.compression,
        })
    }

    #[error_context("Failed to fetch archive metadata")]
    fn fetch_metadata(store: &mut dyn ArchiveStore) -> Result<ArchiveMetadata> {
        let bytes = store.get_object("metadata.json", DEFAULT_ARCHIVE_TIMEOUT)?;
        let metadata: ArchiveMetadata = serde_json::from_slice(&bytes).map_err(|e| {
            crate::ubiblk_error!(MetadataError {
                description: format!("failed to parse archive metadata: {}", e),
            })
        })?;
        validate_format_version(metadata.format_version)?;
        Ok(metadata)
    }

    #[error_context("Failed to fetch stripe hashes")]
    fn fetch_stripe_hashes(
        store: &mut dyn ArchiveStore,
        hmac_key: Option<&[u8; 32]>,
        xts_cipher: Option<XtsBlockCipher>,
    ) -> Result<StripeContentMap> {
        let manifest_name = "stripe-mapping";
        let stripe_hashes_bytes = store.get_object(manifest_name, DEFAULT_ARCHIVE_TIMEOUT)?;
        let hmac_key = hmac_key.ok_or_else(|| {
            crate::ubiblk_error!(MetadataError {
                description: format!("missing HMAC key for {manifest_name}"),
            })
        })?;
        let stripe_hashes = deserialize_stripe_mapping(&stripe_hashes_bytes, hmac_key, xts_cipher)
            .map_err(|e| {
                crate::ubiblk_error!(MetadataError {
                    description: e.to_string(),
                })
            })?;
        Ok(stripe_hashes)
    }

    fn decrypt_hmac_key(
        metadata: &ArchiveMetadata,
        kek: &KeyEncryptionCipher,
    ) -> Result<Option<[u8; 32]>> {
        let key = kek.decrypt_key_data(&metadata.hmac_key)?;
        let key_array: [u8; 32] = key.try_into().map_err(|_| {
            crate::ubiblk_error!(MetadataError {
                description: "invalid HMAC key length in metadata".to_string(),
            })
        })?;
        Ok(Some(key_array))
    }

    fn start_fetch_stripe(
        &mut self,
        stripe_id: usize,
        sha256: [u8; 32],
        buffer: SharedBuffer,
    ) -> Result<()> {
        let object_name = self.object_key(&sha256);

        if let Some(pending) = self.pending_requests.get_mut(&object_name) {
            pending.pending_stripes.push((stripe_id, buffer));
            return Ok(());
        }

        self.store.start_get_object(&object_name);
        self.pending_requests.insert(
            object_name,
            PendingRequest {
                pending_stripes: vec![(stripe_id, buffer)],
                expected_sha256: sha256,
            },
        );
        Ok(())
    }

    fn finish_pending_request(&mut self, request: &PendingRequest, data: &[u8]) {
        for (stripe_id, buffer) in &request.pending_stripes {
            if let Err(e) =
                self.finish_stripe_fetch(*stripe_id, buffer.clone(), data, &request.expected_sha256)
            {
                log::error!("Failed to finish stripe {} fetch: {}", stripe_id, e);
                self.finished_requests.push((*stripe_id, false));
            } else {
                self.finished_requests.push((*stripe_id, true));
            }
        }
    }

    fn maybe_decrypt(&mut self, data: &mut [u8], stripe_id: usize) -> Result<()> {
        if let Some(cipher) = self.xts_cipher.as_mut() {
            if !data.len().is_multiple_of(SECTOR_SIZE) {
                return Err(crate::ubiblk_error!(ArchiveError {
                    description: format!(
                        "Stripe {} data size {} is not a multiple of sector size {}",
                        stripe_id,
                        data.len(),
                        SECTOR_SIZE
                    ),
                }));
            }
            let sector_start = (stripe_id as u64) * self.stripe_sector_count;
            let sector_count = data.len() as u64 / SECTOR_SIZE as u64;
            cipher.decrypt(data, sector_start, sector_count);
        }
        Ok(())
    }

    fn finish_stripe_fetch(
        &mut self,
        stripe_id: usize,
        destination_buffer: SharedBuffer,
        fetched_data: &[u8],
        expected_sha256: &[u8; 32],
    ) -> Result<()> {
        Self::verify_stripe_data(stripe_id, fetched_data, expected_sha256)?;

        let mut decrypted_data = fetched_data.to_vec();
        self.maybe_decrypt(&mut decrypted_data, stripe_id)?;

        let decompressed_data = self.compression.decompress(&decrypted_data)?;

        let mut buf_ref = destination_buffer.borrow_mut();
        let buf = buf_ref.as_mut_slice();
        if decompressed_data.len() > buf.len() {
            return Err(crate::ubiblk_error!(ArchiveError {
                description: format!(
                    "Stripe {} data size {} exceeds buffer size {}",
                    stripe_id,
                    decompressed_data.len(),
                    buf.len()
                ),
            }));
        }
        buf[..decompressed_data.len()].copy_from_slice(&decompressed_data);

        if decompressed_data.len() < buf.len() {
            buf[decompressed_data.len()..].fill(0);
        }

        Ok(())
    }

    fn verify_stripe_data(stripe_id: usize, data: &[u8], expected_sha256: &[u8; 32]) -> Result<()> {
        let computed_hash = sha256_bytes(data);
        if &computed_hash != expected_sha256 {
            return Err(crate::ubiblk_error!(ArchiveError {
                description: format!("sha256 hash mismatch for stripe {}", stripe_id),
            }));
        }
        Ok(())
    }

    fn object_key(&self, hash: &[u8; 32]) -> String {
        format!("data/{}", hex::encode(hash))
    }
}

impl StripeSource for ArchiveStripeSource {
    fn request(&mut self, stripe_id: usize, buffer: SharedBuffer) -> Result<()> {
        let maybe_specifier = self.stripe_hashes.get(&stripe_id).cloned();
        match maybe_specifier {
            Some(StripeContentSpecifier::Zero) => {
                buffer.borrow_mut().as_mut_slice().fill(0);
                self.finished_requests.push((stripe_id, true));
                Ok(())
            }
            Some(StripeContentSpecifier::Some(sha256)) => {
                self.start_fetch_stripe(stripe_id, sha256, buffer)
            }
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
                match result {
                    Ok(data) => {
                        self.finish_pending_request(&pending, &data);
                    }
                    Err(e) => {
                        log::error!("Failed to fetch stripe object {}: {}", object_name, e);
                        for (stripe_id, _) in &pending.pending_stripes {
                            self.finished_requests.push((*stripe_id, false));
                        }
                    }
                }
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
        if self.stripe_hashes.is_empty() {
            0
        } else {
            (self.max_stripe_id + 1) as u64 * self.stripe_sector_count
        }
    }

    fn has_stripe(&self, stripe_id: usize) -> bool {
        self.stripe_hashes.contains_key(&stripe_id)
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;
    use std::time::Duration;

    use base64::engine::general_purpose::STANDARD;
    use base64::Engine;

    use crate::{
        archive::ArchiveCompressionAlgorithm,
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
        compression: ArchiveCompressionAlgorithm,
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

        for stripe_id in 0..bdev_stripe_count {
            let offset = stripe_id * STRIPE_SECTOR_COUNT as usize * SECTOR_SIZE;
            // Use a small offset (3) so disk contents differ from image
            // stripes, making it easier for tests to detect incorrect copying
            // or omission.
            let expected_byte = ((3 + stripe_id) % 256) as u8;
            let buf = vec![expected_byte; STRIPE_SECTOR_COUNT as usize * SECTOR_SIZE];
            disk_bdev.write(offset, &buf, buf.len());
        }

        let image_bdev_size = STRIPE_SECTOR_COUNT * (image_stripe_count * SECTOR_SIZE) as u64;
        let image_bdev: Box<TestBlockDevice> = Box::new(TestBlockDevice::new(image_bdev_size));

        for stripe_id in 0..image_stripe_count {
            let offset = stripe_id * STRIPE_SECTOR_COUNT as usize * SECTOR_SIZE;
            let expected_byte = (stripe_id % 256) as u8;
            let buf = vec![expected_byte; STRIPE_SECTOR_COUNT as usize * SECTOR_SIZE];
            image_bdev.write(offset, &buf, buf.len());
        }

        let stripe_source =
            BlockDeviceStripeSource::new(image_bdev.clone(), STRIPE_SECTOR_COUNT).unwrap();

        let store = Box::new(MemStore::new());

        let archiver = StripeArchiver::new(
            Box::new(stripe_source),
            disk_bdev.as_ref(),
            metadata,
            clone_memstore(store.as_ref()),
            encrypted,
            compression,
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

    fn do_test_archive_stripe_source(
        encrypted: bool,
        kek: KeyEncryptionCipher,
        compression: ArchiveCompressionAlgorithm,
    ) {
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
            compression,
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
        do_test_archive_stripe_source(
            true,
            KeyEncryptionCipher::default(),
            ArchiveCompressionAlgorithm::None,
        );
    }

    #[test]
    fn test_archive_stripe_source_encrypted_with_key_encryption() {
        let kek = KeyEncryptionCipher {
            method: crate::CipherMethod::Aes256Gcm,
            key: Some(vec![0xAB; 32]),
            auth_data: Some("ubiblk_test".as_bytes().to_vec()),
        };
        do_test_archive_stripe_source(true, kek, ArchiveCompressionAlgorithm::None);
    }

    #[test]
    fn test_archive_stripe_source_unencrypted() {
        do_test_archive_stripe_source(
            false,
            KeyEncryptionCipher::default(),
            ArchiveCompressionAlgorithm::None,
        );
    }

    #[test]
    fn test_archive_stripe_source_snappy_encrypted() {
        do_test_archive_stripe_source(
            true,
            KeyEncryptionCipher::default(),
            ArchiveCompressionAlgorithm::Snappy,
        );
    }

    #[test]
    fn test_archive_stripe_source_zstd_encrypted() {
        do_test_archive_stripe_source(
            true,
            KeyEncryptionCipher::default(),
            ArchiveCompressionAlgorithm::Zstd { level: 3 },
        );
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
                    .contains("Object metadata.json not found")
        );
    }

    #[test]
    fn test_errors_on_missing_format_version() {
        let mut store = MemStore::new();
        store
            .put_object(
                "metadata.json",
                br#"{"stripe_sector_count":16,"encryption_key":null}"#,
                Duration::from_secs(5),
            )
            .unwrap();

        let result = ArchiveStripeSource::new(Box::new(store), KeyEncryptionCipher::default());
        assert!(result.is_err());
        assert!(result
            .err()
            .unwrap()
            .to_string()
            .contains("missing field `format_version`"));
    }

    #[test]
    fn test_errors_on_future_format_version() {
        let mut store = MemStore::new();
        store
            .put_object(
                "metadata.json",
                br#"{"format_version":99,"stripe_sector_count":16,"encryption_key":null}"#,
                Duration::from_secs(5),
            )
            .unwrap();

        let result = ArchiveStripeSource::new(Box::new(store), KeyEncryptionCipher::default());
        assert!(result.is_err());
        assert!(result
            .err()
            .unwrap()
            .to_string()
            .contains("unsupported archive format version 99 (supported 1..=1)"));
    }

    #[test]
    fn test_accepts_supported_format_version() {
        let mut store = MemStore::new();
        let hmac_key = [0x11u8; 32];
        let stripe_mapping =
            crate::archive::serialize_stripe_mapping(&StripeContentMap::new(), &hmac_key, None)
                .unwrap();
        let hmac_key_b64 = STANDARD.encode(hmac_key);
        store
            .put_object(
                "metadata.json",
                format!(
                    r#"{{"format_version":1,"stripe_sector_count":16,"encryption_key":null,"hmac_key":"{}"}}"#,
                    hmac_key_b64
                )
                .as_bytes(),
                Duration::from_secs(5),
            )
            .unwrap();
        store
            .put_object("stripe-mapping", &stripe_mapping, Duration::from_secs(5))
            .unwrap();

        let result = ArchiveStripeSource::new(Box::new(store), KeyEncryptionCipher::default());
        assert!(result.is_ok());
    }

    #[test]
    fn test_errors_on_hash_mismatch() {
        let kek = KeyEncryptionCipher::default();
        let mut setup = prep(
            4,
            2,
            false,
            &[0, 2],
            kek.clone(),
            ArchiveCompressionAlgorithm::None,
        );
        setup.archiver.archive_all().unwrap();

        let result = ArchiveStripeSource::new(clone_memstore(&setup.store), kek);
        assert!(result.is_ok());

        let mut source = result.unwrap();

        let buf = shared_buffer((STRIPE_SECTOR_COUNT * SECTOR_SIZE as u64) as usize);
        buf.borrow_mut().as_mut_slice().fill(0xFF);
        let stripe_hash = match source
            .stripe_hashes
            .get(&2)
            .expect("stripe 2 hash should exist")
        {
            StripeContentSpecifier::Some(hash) => hash,
            StripeContentSpecifier::Zero => panic!("stripe 2 unexpectedly zero"),
        };
        let object_name = source.object_key(stripe_hash);
        // Corrupt the stripe data in the store to cause hash mismatch
        setup
            .store
            .put_object(
                &object_name,
                buf.borrow().as_slice(),
                Duration::from_secs(5),
            )
            .unwrap();

        // Stripe 0 & 1 should be fine
        assert!(source.request(0, buf.clone()).is_ok());
        assert!(source.request(1, buf.clone()).is_ok());

        // Stripe 2 should error out due to hash mismatch
        assert!(source.request(2, buf.clone()).is_ok());

        let mut completions = source.poll();
        completions.sort_by_key(|(stripe_id, _)| *stripe_id);
        assert_eq!(completions.len(), 3);
        assert_eq!(completions[0], (0, true));
        assert_eq!(completions[1], (1, true));
        assert_eq!(completions[2], (2, false));
    }

    #[test]
    fn test_fetch_stripe_hashes_bad_cbor() {
        let mut store = MemStore::new();
        let hmac_key = [0x22u8; 32];
        let stripe_mapping = b"not-cbor";
        let hmac_key_b64 = STANDARD.encode(hmac_key);
        store
            .put_object(
                "metadata.json",
                format!(
                    r#"{{"format_version":1,"stripe_sector_count":16,"encryption_key":null,"hmac_key":"{}"}}"#,
                    hmac_key_b64
                )
                .as_bytes(),
                Duration::from_secs(5),
            )
            .unwrap();
        store
            .put_object("stripe-mapping", stripe_mapping, Duration::from_secs(5))
            .unwrap();

        let result = ArchiveStripeSource::new(Box::new(store), KeyEncryptionCipher::default());
        assert!(result.is_err());
        assert!(result
            .err()
            .unwrap()
            .to_string()
            .contains("failed to parse stripe-mapping"));
    }

    #[test]
    fn test_errors_when_zstd_level_missing() {
        let mut store = MemStore::new();
        let hmac_key = [0x33u8; 32];
        let stripe_mapping =
            crate::archive::serialize_stripe_mapping(&StripeContentMap::new(), &hmac_key, None)
                .unwrap();
        let hmac_key_b64 = STANDARD.encode(hmac_key);
        store
            .put_object(
                "metadata.json",
                serde_json::to_string(&serde_json::json!({
                    "format_version": 1,
                    "stripe_sector_count": 16,
                    "encryption_key": null,
                    "compression": { "zstd": {} },
                    "hmac_key": hmac_key_b64
                }))
                .unwrap()
                .as_bytes(),
                Duration::from_secs(5),
            )
            .unwrap();
        store
            .put_object("stripe-mapping", &stripe_mapping, Duration::from_secs(5))
            .unwrap();

        let result = ArchiveStripeSource::new(Box::new(store), KeyEncryptionCipher::default());
        assert!(result.is_err());
        assert!(result
            .err()
            .unwrap()
            .to_string()
            .contains("missing field `level`"));
    }

    #[test]
    fn test_errors_when_zstd_level_invalid() {
        let mut store = MemStore::new();
        let hmac_key = [0x44u8; 32];
        let stripe_mapping =
            crate::archive::serialize_stripe_mapping(&StripeContentMap::new(), &hmac_key, None)
                .unwrap();
        let hmac_key_b64 = STANDARD.encode(hmac_key);
        store
            .put_object(
                "metadata.json",
                serde_json::to_string(&serde_json::json!({
                    "format_version": 1,
                    "stripe_sector_count": 16,
                    "encryption_key": null,
                    "compression": {
                        "zstd": {
                            "level": 2147483648i64
                        }
                    },
                    "hmac_key": hmac_key_b64,
                }))
                .unwrap()
                .as_bytes(),
                Duration::from_secs(5),
            )
            .unwrap();
        store
            .put_object("stripe-mapping", &stripe_mapping, Duration::from_secs(5))
            .unwrap();

        let result = ArchiveStripeSource::new(Box::new(store), KeyEncryptionCipher::default());
        assert!(result.is_err());
        let error = result.err().unwrap().to_string();
        assert!(
            error.contains("invalid value") && error.contains("i32"),
            "unexpected error: {error}"
        );
    }
}
