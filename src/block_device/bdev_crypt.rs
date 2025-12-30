use super::*;

use crate::{
    crypt::{KeyEncryptionCipher, XtsBlockCipher},
    Result,
};

struct Request {
    sector_offset: u64,
    sector_count: u32,
    buf: SharedBuffer,
}

struct CryptIoChannel {
    base: Box<dyn IoChannel>,
    xts_cipher: XtsBlockCipher,
    read_requests: Vec<Option<Request>>,
}

impl CryptIoChannel {
    pub fn new(base: Box<dyn IoChannel>, xts_cipher: XtsBlockCipher) -> Self {
        CryptIoChannel {
            base,
            xts_cipher,
            read_requests: Vec::new(),
        }
    }
}

impl IoChannel for CryptIoChannel {
    fn add_read(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        if id >= self.read_requests.len() {
            self.read_requests.resize_with(id + 1, || None);
        }
        self.read_requests[id] = Some(Request {
            sector_offset,
            buf: buf.clone(),
            sector_count,
        });
        self.base
            .add_read(sector_offset, sector_count, buf.clone(), id);
    }

    fn add_write(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        self.xts_cipher.encrypt(
            buf.borrow_mut().as_mut_slice(),
            sector_offset,
            sector_count as u64,
        );
        self.base
            .add_write(sector_offset, sector_count, buf.clone(), id);
    }

    fn add_flush(&mut self, id: usize) {
        self.base.add_flush(id);
    }

    fn submit(&mut self) -> Result<()> {
        self.base.submit()
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        let mut results = vec![];
        for (id, result) in self.base.poll() {
            if id < self.read_requests.len() {
                if let Some(req) = self.read_requests[id].take() {
                    if result {
                        self.xts_cipher.decrypt(
                            req.buf.borrow_mut().as_mut_slice(),
                            req.sector_offset,
                            req.sector_count as u64,
                        );
                    }
                    results.push((id, result));
                    continue;
                }
            }
            results.push((id, result));
        }
        results
    }

    fn busy(&self) -> bool {
        self.base.busy()
    }
}

pub struct CryptBlockDevice {
    base: Box<dyn BlockDevice>,
    xts_cipher: XtsBlockCipher,
}

impl BlockDevice for CryptBlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>> {
        let base_channel = self.base.create_channel()?;
        let crypt_channel = CryptIoChannel::new(base_channel, self.xts_cipher.clone());
        Ok(Box::new(crypt_channel))
    }

    fn sector_count(&self) -> u64 {
        self.base.sector_count()
    }

    fn clone(&self) -> Box<dyn BlockDevice> {
        Box::new(CryptBlockDevice {
            base: self.base.clone(),
            xts_cipher: self.xts_cipher.clone(),
        })
    }
}

impl CryptBlockDevice {
    pub fn new(
        base: Box<dyn BlockDevice>,
        key1: Vec<u8>,
        key2: Vec<u8>,
        kek: KeyEncryptionCipher,
    ) -> Result<Box<Self>> {
        let xts_cipher = XtsBlockCipher::new(key1, key2, kek)?;
        Ok(Box::new(CryptBlockDevice { base, xts_cipher }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::UbiblkError;

    use crate::{
        block_device::bdev_test::TestBlockDevice,
        crypt::{CipherMethod, KeyEncryptionCipher},
        vhost_backend::SECTOR_SIZE,
    };

    #[test]
    fn test_crypt_block_device() {
        let kek = KeyEncryptionCipher::default();
        let base = TestBlockDevice::new(1024 * 1024);
        let metrics = base.metrics.clone();
        let mem = base.mem.clone();
        let key1 = [
            1, 35, 69, 103, 137, 171, 205, 239, 1, 35, 69, 103, 137, 171, 205, 239, 1, 35, 69, 103,
            137, 171, 205, 239, 1, 35, 69, 103, 137, 171, 205, 239,
        ];
        let key2 = [
            254, 220, 186, 152, 118, 84, 50, 16, 254, 220, 186, 152, 118, 84, 50, 16, 254, 220,
            186, 152, 118, 84, 50, 16, 254, 220, 186, 152, 118, 84, 50, 16,
        ];
        let crypt_bdev = CryptBlockDevice::new(Box::new(base), key1.to_vec(), key2.to_vec(), kek)
            .expect("Failed to create CryptBlockDevice");
        let mut channel = crypt_bdev
            .create_channel()
            .expect("Failed to create channel");

        // initially, first 2 sectors of mem should be the same
        assert_eq!(
            &mem.read().unwrap()[0..SECTOR_SIZE],
            &mem.read().unwrap()[SECTOR_SIZE..SECTOR_SIZE * 2]
        );

        let sample_data = "Hello, world!".as_bytes();
        let buf = shared_buffer(SECTOR_SIZE);

        for i in 0..2 {
            buf.borrow_mut().as_mut_slice()[0..sample_data.len()].copy_from_slice(sample_data);
            channel.add_write(i, 1, buf.clone(), 12);
            channel.submit().expect("Failed to submit write request");
            while channel.busy() {
                std::thread::sleep(std::time::Duration::from_millis(10));
            }
            let poll_results = channel.poll();
            assert_eq!(poll_results, vec![(12, true)]);
        }

        assert_eq!(metrics.read().unwrap().reads, 0);
        assert_eq!(metrics.read().unwrap().writes, 2);
        assert_eq!(metrics.read().unwrap().flushes, 0);

        for i in 0..2 {
            let read_id = 34;
            buf.borrow_mut().as_mut_slice().fill(0);
            channel.add_read(i, 1, buf.clone(), read_id);
            channel.submit().expect("Failed to submit read request");

            while channel.busy() {
                std::thread::sleep(std::time::Duration::from_millis(10));
            }

            let poll_results = channel.poll();
            assert_eq!(poll_results, vec![(read_id, true)]);
            assert_eq!(&buf.borrow().as_slice()[0..sample_data.len()], sample_data);
        }

        assert_eq!(metrics.read().unwrap().reads, 2);
        assert_eq!(metrics.read().unwrap().writes, 2);
        assert_eq!(metrics.read().unwrap().flushes, 0);

        let flush_id = 56;
        channel.add_flush(flush_id);
        channel.submit().expect("Failed to submit flush request");
        while channel.busy() {
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
        let poll_results = channel.poll();
        assert_eq!(poll_results, vec![(flush_id, true)]);

        assert_eq!(metrics.read().unwrap().reads, 2);
        assert_eq!(metrics.read().unwrap().writes, 2);
        assert_eq!(metrics.read().unwrap().flushes, 1);

        // Although we wrote the same data to both sectors, the encrypted data
        // should be different due to the different tweaks.
        assert_ne!(
            &mem.read().unwrap()[0..SECTOR_SIZE],
            &mem.read().unwrap()[SECTOR_SIZE..SECTOR_SIZE * 2]
        );
    }

    #[test]
    fn test_invalid_key_length() {
        let kek = KeyEncryptionCipher::default();
        let base = TestBlockDevice::new(1024 * 1024);
        let key1 = [
            1, 35, 69, 103, 137, 171, 205, 239, 1, 35, 69, 103, 137, 171, 205, 239, 1, 35, 69, 103,
            137, 171, 205, 239, 1, 35, 69, 103, 137, 171, 205, 239, 1, 35, 69, 103, 137, 171, 205,
            239,
        ];
        let key2 = [
            254, 220, 186, 152, 118, 84, 50, 16, 254, 220, 186, 152, 118, 84, 50, 16, 254, 220,
            186, 152, 118, 84, 50, 16, 254, 220, 186, 152, 118, 84, 50, 16, 254, 220, 186, 152,
            118, 84, 50, 16,
        ];
        let result = CryptBlockDevice::new(Box::new(base), key1.to_vec(), key2.to_vec(), kek);
        assert!(result.is_err());
    }

    #[test]
    fn test_sector_count() {
        let base = TestBlockDevice::new(1024 * 1024);
        let bdev = CryptBlockDevice::new(
            Box::new(base),
            vec![0u8; 32],
            vec![0u8; 32],
            KeyEncryptionCipher::default(),
        )
        .unwrap();

        assert_eq!(bdev.sector_count(), 2048);
    }

    #[test]
    fn test_invalid_iv_length() {
        let kek = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(vec![0u8; 32]),
            init_vector: Some(vec![0u8; 8]),
            auth_data: Some(vec![]),
        };
        let base = TestBlockDevice::new(1024 * 1024);
        let key1 = vec![0u8; 48];
        let key2 = vec![0u8; 48];

        let result = CryptBlockDevice::new(Box::new(base), key1, key2, kek);
        assert!(matches!(result, Err(UbiblkError::InvalidParameter { .. })));
    }

    #[test]
    fn test_encrypted_key_decryption() {
        let kek = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(vec![
                0xb8, 0x2b, 0xc6, 0x88, 0x9f, 0xad, 0x94, 0x02, 0xf4, 0xeb, 0x7e, 0x64, 0x1a, 0x15,
                0x1a, 0x3a, 0x19, 0xa0, 0xb1, 0xe4, 0xa4, 0xa0, 0x22, 0xb5, 0x1c, 0x38, 0x71, 0x24,
                0x68, 0x2e, 0x8d, 0x22,
            ]),
            init_vector: Some(vec![
                0x50, 0x4b, 0x7e, 0xc0, 0x8f, 0x8b, 0x76, 0xad, 0x54, 0x81, 0x0f, 0xcf,
            ]),
            auth_data: Some(vec![]),
        };
        let key1 = vec![
            0x68, 0x84, 0xaa, 0xee, 0x36, 0xde, 0x35, 0x63, 0xbc, 0x53, 0xe5, 0x47, 0x39, 0xbd,
            0x3d, 0x2b, 0x82, 0xb9, 0x4a, 0x3d, 0x43, 0xb0, 0xc1, 0x8b, 0x7f, 0x6f, 0x3d, 0xa0,
            0xee, 0x2f, 0x38, 0x6f, 0x52, 0x23, 0x55, 0xa9, 0x19, 0xd5, 0x0c, 0xed, 0x69, 0xae,
            0x59, 0x00, 0x6d, 0x1a, 0x19, 0x32,
        ];
        let key2 = vec![
            0xe4, 0xe4, 0xda, 0xba, 0x49, 0xd2, 0xc7, 0x05, 0x85, 0xa9, 0x11, 0xaf, 0x13, 0x61,
            0x1f, 0xdd, 0x9b, 0xf6, 0xb3, 0x5b, 0x32, 0x3d, 0xd6, 0xd8, 0x15, 0x7c, 0xaa, 0xdc,
            0x51, 0xe4, 0x2b, 0xaf, 0x7f, 0x06, 0x12, 0x3e, 0xee, 0x31, 0x7e, 0x54, 0x54, 0x06,
            0x15, 0xbd, 0x7e, 0x8f, 0x7b, 0x23,
        ];

        let base = TestBlockDevice::new(1024 * 1024);
        let bdev_crypt = CryptBlockDevice::new(Box::new(base), key1.clone(), key2.clone(), kek)
            .expect("Failed to create CryptBlockDevice");

        let expected_key1_hex = "13a13755601ef674dab4ba8f8c33762082270f9d1aad33ae1bec63919501d176";
        let expected_key2_hex = "9fc147011f120412e34e4e67a6ef54d69b68f6fb6b2024fd71fff4ed2acac2b6";
        let expected_block_cipher = XtsBlockCipher::new(
            hex::decode(expected_key1_hex).unwrap(),
            hex::decode(expected_key2_hex).unwrap(),
            KeyEncryptionCipher::default(),
        )
        .unwrap();
        assert_eq!(bdev_crypt.xts_cipher, expected_block_cipher);
    }

    #[test]
    fn test_invalid_encrypted_key_length() {
        let kek = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(vec![
                0xb8, 0x2b, 0xc6, 0x88, 0x9f, 0xad, 0x94, 0x02, 0xf4, 0xeb, 0x7e, 0x64, 0x1a, 0x15,
                0x1a, 0x3a, 0x19, 0xa0, 0xb1, 0xe4, 0xa4, 0xa0, 0x22, 0xb5, 0x1c, 0x38, 0x71, 0x24,
                0x68, 0x2e, 0x8d, 0x22,
            ]),
            init_vector: Some(vec![
                0x50, 0x4b, 0x7e, 0xc0, 0x8f, 0x8b, 0x76, 0xad, 0x54, 0x81, 0x0f, 0xcf,
            ]),
            auth_data: Some(vec![]),
        };
        let key1 = vec![0u8; 31];
        let key2 = vec![0u8; 31];

        let base = TestBlockDevice::new(1024 * 1024);
        let result = CryptBlockDevice::new(Box::new(base), key1.clone(), key2.clone(), kek);
        assert!(matches!(result, Err(UbiblkError::InvalidParameter { .. })));
    }

    #[test]
    fn test_missing_kek_parameters() {
        let kek = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            ..Default::default()
        };
        let base = TestBlockDevice::new(1024 * 1024);
        let key1 = vec![0u8; 32];
        let key2 = vec![0u8; 32];

        let result = CryptBlockDevice::new(Box::new(base), key1, key2, kek);
        assert!(matches!(result, Err(UbiblkError::InvalidParameter { .. })));
    }

    #[test]
    fn test_invalid_kek_key_length() {
        let kek = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(vec![0u8; 31]),
            init_vector: Some(vec![0u8; 12]),
            auth_data: Some(vec![]),
        };
        let base = TestBlockDevice::new(1024 * 1024);
        let res = CryptBlockDevice::new(Box::new(base), vec![0u8; 32], vec![0u8; 32], kek);
        assert!(matches!(res, Err(UbiblkError::InvalidParameter { .. })));
    }
}
