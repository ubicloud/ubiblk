use crate::{
    crypt::KeyEncryptionCipher, vhost_backend::SECTOR_SIZE, Result, XTS_AES_256_dec,
    XTS_AES_256_enc,
};

use openssl::rand::rand_bytes;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct XtsBlockCipher {
    key1: [u8; 32],
    key2: [u8; 32],
}

impl XtsBlockCipher {
    pub fn new(
        encrypted_key1: Vec<u8>,
        encrypted_key2: Vec<u8>,
        kek: KeyEncryptionCipher,
    ) -> Result<Self> {
        let (dec_key1, dec_key2) = kek.decrypt_xts_keys(encrypted_key1, encrypted_key2)?;

        Ok(XtsBlockCipher {
            key1: dec_key1,
            key2: dec_key2,
        })
    }

    fn rand_bytes(buf: &mut [u8]) -> Result<()> {
        rand_bytes(buf).map_err(|e| crate::UbiblkError::CryptoError {
            description: format!("Failed to generate random bytes: {}", e),
        })
    }

    pub fn random() -> Result<Self> {
        let mut key1 = [0u8; 32];
        let mut key2 = [0u8; 32];
        Self::rand_bytes(&mut key1)?;
        Self::rand_bytes(&mut key2)?;
        Ok(XtsBlockCipher { key1, key2 })
    }

    pub fn encrypted_keys(&self, kek: &KeyEncryptionCipher) -> Result<(Vec<u8>, Vec<u8>)> {
        kek.encrypt_xts_keys(&self.key1, &self.key2)
    }

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

    pub fn decrypt(&mut self, buf: &mut [u8], sector_start: u64, sector_count: u64) {
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

    pub fn encrypt(&mut self, buf: &mut [u8], sector_start: u64, sector_count: u64) {
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
}

#[cfg(test)]
mod tests {
    use crate::CipherMethod;

    use super::*;

    #[test]
    fn test_get_initial_tweak() {
        let kek = KeyEncryptionCipher::default();
        let xts_cipher = XtsBlockCipher::new(vec![1u8; 32], vec![2u8; 32], kek).unwrap();

        let sector = 0x1122_3344_5566_7788u64;
        let tweak = xts_cipher.get_initial_tweak(sector);

        assert_eq!(&tweak[0..8], &[0u8; 8]);
        assert_eq!(&tweak[8..16], &sector.to_le_bytes());
    }

    #[test]
    fn test_generate_random_keys() {
        let xts_cipher1 = XtsBlockCipher::random().unwrap();
        let xts_cipher2 = XtsBlockCipher::random().unwrap();

        // We should have an extremely low chance of generating the same keys
        // twice in row
        assert_ne!(xts_cipher1.key1, xts_cipher2.key1);
        assert_ne!(xts_cipher1.key2, xts_cipher2.key2);
    }

    #[test]
    fn test_keys_no_key_encryption() {
        let kek = KeyEncryptionCipher::default();
        let key1 = vec![3u8; 32];
        let key2 = vec![4u8; 32];

        let xts_cipher = XtsBlockCipher::new(key1.clone(), key2.clone(), kek.clone()).unwrap();
        let (enc_key1, enc_key2) = xts_cipher.encrypted_keys(&kek).unwrap();

        assert_eq!(enc_key1, key1.as_slice());
        assert_eq!(enc_key2, key2.as_slice());
    }

    #[test]
    fn test_keys_with_key_encryption() {
        let kek_key = [0x11u8; 32];
        let iv = [0x22u8; 12];
        let aad = b"test-aad";

        let kek = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(kek_key.to_vec()),
            init_vector: Some(iv.to_vec()),
            auth_data: Some(aad.to_vec()),
        };
        let key1 = vec![5u8; 32];
        let key2 = vec![6u8; 32];

        let (enc1, enc2) = kek.encrypt_xts_keys(&key1, &key2).unwrap();
        assert_ne!(enc1, key1);
        assert_ne!(enc2, key2);

        let xts_cipher = XtsBlockCipher::new(enc1.clone(), enc2.clone(), kek.clone()).unwrap();
        let (enc3, enc4) = xts_cipher.encrypted_keys(&kek).unwrap();

        assert_eq!(enc1, enc3);
        assert_eq!(enc2, enc4);
    }
}
