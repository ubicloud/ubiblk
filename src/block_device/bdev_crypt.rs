use super::*;
#[cfg(test)]
use crate::utils::aligned_buffer::AlignedBuf;
use crate::vhost_backend::{CipherMethod, KeyEncryptionCipher, SECTOR_SIZE};
use crate::{Result, VhostUserBlockError};
#[cfg(not(feature = "disable-isal-crypto"))]
use crate::{XTS_AES_256_dec, XTS_AES_256_enc};
#[cfg(feature = "disable-isal-crypto")]
use aes::cipher::generic_array::GenericArray;
#[cfg(feature = "disable-isal-crypto")]
use aes::Aes256;
use aes_gcm::aead::Payload;
use aes_gcm::{
    aead::{consts::U12, generic_array::GenericArray as AeadArray, Aead, KeyInit as AeadKeyInit},
    Aes256Gcm,
};
use log::error;
#[cfg(feature = "disable-isal-crypto")]
use xts_mode::{get_tweak_default, Xts128};

struct Request {
    sector_offset: u64,
    sector_count: u32,
    buf: SharedBuffer,
}

struct CryptIoChannel {
    base: Box<dyn IoChannel>,
    #[cfg_attr(feature = "disable-isal-crypto", allow(dead_code))]
    key1: [u8; 32],
    #[cfg_attr(feature = "disable-isal-crypto", allow(dead_code))]
    key2: [u8; 32],
    #[cfg(feature = "disable-isal-crypto")]
    xts: Xts128<Aes256>,
    read_requests: Vec<Option<Request>>,
}

impl CryptIoChannel {
    pub fn new(base: Box<dyn IoChannel>, key1: [u8; 32], key2: [u8; 32]) -> Self {
        #[cfg(feature = "disable-isal-crypto")]
        let xts = {
            let cipher1 = Aes256::new(GenericArray::from_slice(&key1));
            let cipher2 = Aes256::new(GenericArray::from_slice(&key2));
            Xts128::new(cipher1, cipher2)
        };

        CryptIoChannel {
            base,
            key1,
            key2,
            #[cfg(feature = "disable-isal-crypto")]
            xts,
            read_requests: Vec::new(),
        }
    }
}

impl CryptIoChannel {
    #[cfg_attr(feature = "disable-isal-crypto", allow(dead_code))]
    fn get_initial_tweak(&self, sector: u64) -> [u8; 16] {
        /*
         * Based on SPDK's _sw_accel_crypto_operation() in spdk/lib/accel/accel_sw.c:
         *   uint64_t iv[2];
         *   iv[0] = 0;
         *   iv[1] = accel_task->iv;
         */
        let mut tweak = [0u8; 16];
        // First 8 bytes are already zero.
        // Encode the sector number as little-endian into the second 8 bytes.
        tweak[8..].copy_from_slice(&sector.to_le_bytes());
        tweak
    }

    /*
     * From isa-l_crypto/include/aes_xts.h:
     *
     * The input and output buffers can be overlapping as long as the output buffer
     * pointer is not less than the input buffer pointer. If the two pointers are the
     * same, then encryption/decryption will occur in-place.
     *
     * The input and output buffers, keys, pre-expanded keys and initial tweak value
     * are not required to be aligned to 16 bytes, any alignment works.
     */

    #[cfg(not(feature = "disable-isal-crypto"))]
    fn decrypt(&mut self, buf: &mut [u8], sector_start: u64, sector_count: u64) {
        for i in 0..sector_count as usize {
            let sector = sector_start + i as u64;
            let mut tweak = self.get_initial_tweak(sector);
            let sector_data = &mut buf[i * SECTOR_SIZE..(i + 1) * SECTOR_SIZE];
            unsafe {
                XTS_AES_256_dec(
                    self.key2.as_mut_ptr(),
                    self.key1.as_mut_ptr(),
                    tweak.as_mut_ptr(),
                    SECTOR_SIZE as u64,
                    sector_data.as_ptr(),
                    sector_data.as_mut_ptr(),
                );
            }
        }
    }

    #[cfg(feature = "disable-isal-crypto")]
    fn decrypt(&mut self, buf: &mut [u8], sector_start: u64, sector_count: u64) {
        for i in 0..sector_count as usize {
            let sector = sector_start + i as u64;
            let sector_data = &mut buf[i * SECTOR_SIZE..(i + 1) * SECTOR_SIZE];
            self.xts
                .decrypt_sector(sector_data, get_tweak_default(sector as u128));
        }
    }

    #[cfg(not(feature = "disable-isal-crypto"))]
    fn encrypt(&mut self, buf: &mut [u8], sector_start: u64, sector_count: u64) {
        for i in 0..sector_count as usize {
            let sector = sector_start + i as u64;
            let mut tweak = self.get_initial_tweak(sector);
            let sector_data = &mut buf[i * SECTOR_SIZE..(i + 1) * SECTOR_SIZE];
            unsafe {
                XTS_AES_256_enc(
                    self.key2.as_mut_ptr(),
                    self.key1.as_mut_ptr(),
                    tweak.as_mut_ptr(),
                    SECTOR_SIZE as u64,
                    sector_data.as_ptr(),
                    sector_data.as_mut_ptr(),
                );
            }
        }
    }

    #[cfg(feature = "disable-isal-crypto")]
    fn encrypt(&mut self, buf: &mut [u8], sector_start: u64, sector_count: u64) {
        for i in 0..sector_count as usize {
            let sector = sector_start + i as u64;
            let sector_data = &mut buf[i * SECTOR_SIZE..(i + 1) * SECTOR_SIZE];
            self.xts
                .encrypt_sector(sector_data, get_tweak_default(sector as u128));
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
        self.encrypt(
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
                        self.decrypt(
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
    key1: [u8; 32],
    key2: [u8; 32],
}

impl BlockDevice for CryptBlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>> {
        let base_channel = self.base.create_channel()?;
        let crypt_channel = CryptIoChannel::new(base_channel, self.key1, self.key2);
        Ok(Box::new(crypt_channel))
    }

    fn sector_count(&self) -> u64 {
        self.base.sector_count()
    }
}

impl CryptBlockDevice {
    pub fn new(
        base: Box<dyn BlockDevice>,
        key1: Vec<u8>,
        key2: Vec<u8>,
        kek: KeyEncryptionCipher,
    ) -> Result<Box<Self>> {
        let (key1, key2) = decrypt_keys(key1, key2, kek)?;
        Ok(Box::new(CryptBlockDevice { base, key1, key2 }))
    }
}

fn decrypt_keys(
    key1: Vec<u8>,
    key2: Vec<u8>,
    kek: KeyEncryptionCipher,
) -> Result<([u8; 32], [u8; 32])> {
    match kek.method {
        CipherMethod::None => {
            if key1.len() != 32 || key2.len() != 32 {
                error!("Key length must be 32 bytes");
                return Err(VhostUserBlockError::InvalidParameter {
                    description: "Key length must be 32 bytes".to_string(),
                });
            }
            let key1 = key1.try_into().map_err(|_| {
                error!("Failed to convert key1 to array");
                VhostUserBlockError::InvalidParameter {
                    description: "Failed to convert key1 to array".to_string(),
                }
            })?;
            let key2 = key2.try_into().map_err(|_| {
                error!("Failed to convert key2 to array");
                VhostUserBlockError::InvalidParameter {
                    description: "Failed to convert key2 to array".to_string(),
                }
            })?;
            Ok((key1, key2))
        }

        CipherMethod::Aes256Gcm => {
            let kek_key = kek.key.ok_or(VhostUserBlockError::InvalidParameter {
                description: "Key is required".to_string(),
            })?;
            let kek_iv = kek
                .init_vector
                .ok_or(VhostUserBlockError::InvalidParameter {
                    description: "Initialization vector is required".to_string(),
                })?;
            let kek_auth_data = kek.auth_data.ok_or(VhostUserBlockError::InvalidParameter {
                description: "Authentication data is required".to_string(),
            })?;

            let cipher = Aes256Gcm::new_from_slice(&kek_key).map_err(|e| {
                error!("Failed to initialize cipher: {e}");
                VhostUserBlockError::InvalidParameter {
                    description: format!("Failed to initialize cipher: {e}"),
                }
            })?;

            if kek_iv.len() != 12 {
                error!("Initial vector must be exactly 12 bytes");
                return Err(VhostUserBlockError::InvalidParameter {
                    description: "Initial vector must be exactly 12 bytes".to_string(),
                });
            }
            let nonce = Nonce::from_slice(&kek_iv);

            let clear1 = decrypt_block(&cipher, nonce, &kek_auth_data, &key1)?;
            let clear2 = decrypt_block(&cipher, nonce, &kek_auth_data, &key2)?;
            Ok((clear1, clear2))
        }
    }
}

type Nonce = AeadArray<u8, U12>;

fn decrypt_block(
    cipher: &Aes256Gcm,
    nonce: &Nonce,
    auth_data: &[u8],
    enc: &[u8],
) -> Result<[u8; 32]> {
    let plain = cipher
        .decrypt(
            nonce,
            Payload {
                msg: enc,
                aad: auth_data,
            },
        )
        .map_err(|e| {
            error!("Failed to decrypt key: {e}");
            VhostUserBlockError::InvalidParameter {
                description: format!("Failed to decrypt key: {e}"),
            }
        })?;

    if plain.len() != 32 {
        error!("Decrypted key must be exactly 32 bytes");
        return Err(VhostUserBlockError::InvalidParameter {
            description: "Decrypted key must be exactly 32 bytes".to_string(),
        });
    }
    let mut out = [0u8; 32];
    out.copy_from_slice(&plain);
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        block_device::bdev_test::TestBlockDevice,
        vhost_backend::{CipherMethod, SECTOR_SIZE},
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
        let buf = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));

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
        let key1 = hex::encode(bdev_crypt.key1);
        let key2 = hex::encode(bdev_crypt.key2);
        assert_eq!(key1, expected_key1_hex);
        assert_eq!(key2, expected_key2_hex);
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
        assert!(matches!(
            result,
            Err(VhostUserBlockError::InvalidParameter { .. })
        ));
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
        assert!(matches!(
            result,
            Err(VhostUserBlockError::InvalidParameter { .. })
        ));
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
        assert!(matches!(
            result,
            Err(VhostUserBlockError::InvalidParameter { .. })
        ));
    }

    #[test]
    fn test_get_initial_tweak() {
        let base = TestBlockDevice::new(1024 * 1024);
        let base_chan = base.create_channel().unwrap();
        let chan = CryptIoChannel::new(base_chan, [1u8; 32], [2u8; 32]);

        let sector = 0x1122_3344_5566_7788u64;
        let tweak = chan.get_initial_tweak(sector);

        assert_eq!(&tweak[0..8], &[0u8; 8]);
        assert_eq!(&tweak[8..16], &sector.to_le_bytes());
    }

    #[test]
    fn test_decrypt_block_failure() {
        use aes_gcm::Aes256Gcm;

        let cipher = Aes256Gcm::new_from_slice(&[0u8; 32]).unwrap();
        let nonce = AeadArray::from_slice(&[0u8; 12]);
        let enc = vec![0u8; 48];

        let res = decrypt_block(&cipher, nonce, &[], &enc);
        assert!(matches!(
            res,
            Err(VhostUserBlockError::InvalidParameter { .. })
        ));
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
    fn test_invalid_kek_key_length() {
        let kek = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(vec![0u8; 31]),
            init_vector: Some(vec![0u8; 12]),
            auth_data: Some(vec![]),
        };
        let base = TestBlockDevice::new(1024 * 1024);
        let res = CryptBlockDevice::new(Box::new(base), vec![0u8; 32], vec![0u8; 32], kek);
        assert!(matches!(
            res,
            Err(VhostUserBlockError::InvalidParameter { .. })
        ));
    }

    #[test]
    fn test_decrypt_block_bad_plain_length() {
        use aes_gcm::{aead::KeyInit as AeadKeyInit, Aes256Gcm};
        let cipher = Aes256Gcm::new_from_slice(&[0u8; 32]).unwrap();
        let nonce = AeadArray::from_slice(&[0u8; 12]);
        let data = [1u8; 8];
        let enc = cipher
            .encrypt(
                nonce,
                Payload {
                    msg: &data,
                    aad: b"",
                },
            )
            .unwrap();

        let res = decrypt_block(&cipher, nonce, b"", &enc);
        assert!(matches!(
            res,
            Err(VhostUserBlockError::InvalidParameter { .. })
        ));
    }
}
