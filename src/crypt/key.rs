use std::{fs::File, path::PathBuf};

use crate::{Result, UbiblkError};
use aes_gcm::{
    aead::{Aead, AeadCore, KeyInit, Payload},
    Aes256Gcm, Nonce,
};
use log::error;
use serde::{Deserialize, Serialize};
use serde_with::{base64::Base64, serde_as};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Default)]
#[serde(rename_all = "kebab-case")]
pub enum CipherMethod {
    #[default]
    None,
    Aes256Gcm,
}

#[serde_as]
#[derive(Debug, Clone, Deserialize, Default)]
pub struct KeyEncryptionCipher {
    pub method: CipherMethod,

    #[serde_as(as = "Option<Base64>")]
    pub key: Option<Vec<u8>>,

    #[serde_as(as = "Option<Base64>")]
    pub init_vector: Option<Vec<u8>>,

    #[serde_as(as = "Option<Base64>")]
    pub auth_data: Option<Vec<u8>>,
}

type KekNonce = Nonce<<Aes256Gcm as AeadCore>::NonceSize>;

impl KeyEncryptionCipher {
    fn init_cipher_context(&self) -> Result<(Aes256Gcm, KekNonce, &[u8])> {
        let key = self
            .key
            .as_ref()
            .ok_or_else(|| param_err("Key is required"))?;

        let iv = self
            .init_vector
            .as_ref()
            .ok_or_else(|| param_err("Initialization vector is required"))?;

        let auth_data = self
            .auth_data
            .as_ref()
            .ok_or_else(|| param_err("Authentication data is required"))?;

        let cipher = Aes256Gcm::new_from_slice(key).map_err(|e| {
            let msg = format!("Failed to initialize cipher: {e}");
            error!("{}", msg);
            param_err(msg)
        })?;

        if iv.len() != 12 {
            let msg = "Initialization vector must be exactly 12 bytes";
            error!("{}", msg);
            return Err(param_err(msg));
        }
        let nonce = KekNonce::from_slice(iv);

        Ok((cipher, *nonce, auth_data))
    }

    pub fn load(path: Option<&PathBuf>, unlink: bool) -> Result<Self> {
        let Some(path) = path else {
            return Ok(KeyEncryptionCipher::default());
        };

        let file = File::open(path)?;
        let kek: KeyEncryptionCipher =
            serde_yaml::from_reader(file).map_err(|e| UbiblkError::InvalidParameter {
                description: format!("Error parsing KEK file {}: {e}", path.display()),
            })?;

        if unlink {
            std::fs::remove_file(path)?;
        }

        Ok(kek)
    }
}

pub fn decrypt_keys(
    key1: Vec<u8>,
    key2: Vec<u8>,
    kek: KeyEncryptionCipher,
) -> Result<([u8; 32], [u8; 32])> {
    match kek.method {
        CipherMethod::None => {
            // "None" implies inputs are already plain text; just validate length.
            Ok((ensure_32_bytes(key1)?, ensure_32_bytes(key2)?))
        }
        CipherMethod::Aes256Gcm => {
            let (cipher, nonce, auth) = kek.init_cipher_context()?;

            let k1 = decrypt_bytes(&cipher, &nonce, auth, &key1)?;
            let k2 = decrypt_bytes(&cipher, &nonce, auth, &key2)?;

            Ok((ensure_32_bytes(k1)?, ensure_32_bytes(k2)?))
        }
    }
}

pub fn decrypt_psk_secret(secret: Vec<u8>, kek: &KeyEncryptionCipher) -> Result<Vec<u8>> {
    match kek.method {
        CipherMethod::None => Ok(secret),
        CipherMethod::Aes256Gcm => {
            let (cipher, nonce, auth) = kek.init_cipher_context()?;
            decrypt_bytes(&cipher, &nonce, auth, &secret)
        }
    }
}

fn decrypt_bytes(
    cipher: &Aes256Gcm,
    nonce: &KekNonce,
    aad: &[u8],
    ciphertext: &[u8],
) -> Result<Vec<u8>> {
    cipher
        .decrypt(
            nonce,
            Payload {
                msg: ciphertext,
                aad,
            },
        )
        .map_err(|e| {
            let msg = format!("Failed to decrypt data: {e}");
            error!("{}", msg);
            param_err(msg)
        })
}

fn ensure_32_bytes(data: Vec<u8>) -> Result<[u8; 32]> {
    data.try_into().map_err(|_| {
        let msg = "Key length must be exactly 32 bytes";
        error!("{}", msg);
        param_err(msg)
    })
}

fn param_err(description: impl Into<String>) -> UbiblkError {
    UbiblkError::InvalidParameter {
        description: description.into(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use aes_gcm::KeyInit;

    fn encrypt_helper(kek_key: &[u8], iv: &[u8], aad: &[u8], plaintext: &[u8]) -> Vec<u8> {
        let cipher = Aes256Gcm::new_from_slice(kek_key).unwrap();
        let nonce = KekNonce::from_slice(iv);
        cipher
            .encrypt(
                nonce,
                Payload {
                    msg: plaintext,
                    aad,
                },
            )
            .unwrap()
    }

    #[test]
    fn test_decrypt_keys_aes_gcm_success() {
        let kek_key = [0x11u8; 32];
        let iv = [0x22u8; 12];
        let aad = b"test-aad";

        // The actual secret keys we want to protect
        let target_key1 = [0xAAu8; 32];
        let target_key2 = [0xBBu8; 32];

        let enc1 = encrypt_helper(&kek_key, &iv, aad, &target_key1);
        let enc2 = encrypt_helper(&kek_key, &iv, aad, &target_key2);

        let config = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(kek_key.to_vec()),
            init_vector: Some(iv.to_vec()),
            auth_data: Some(aad.to_vec()),
        };

        let (res1, res2) = decrypt_keys(enc1, enc2, config).expect("Decryption should succeed");
        assert_eq!(res1, target_key1);
        assert_eq!(res2, target_key2);
    }

    #[test]
    fn test_decrypt_psk_secret_aes_gcm_success() {
        let kek_key = [0x33u8; 32];
        let iv = [0x44u8; 12];
        let aad = b"psk-aad";
        let secret_msg = b"super secret psk string";

        let enc_secret = encrypt_helper(&kek_key, &iv, aad, secret_msg);

        let config = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(kek_key.to_vec()),
            init_vector: Some(iv.to_vec()),
            auth_data: Some(aad.to_vec()),
        };

        let res = decrypt_psk_secret(enc_secret, &config).expect("Decryption should succeed");
        assert_eq!(res, secret_msg);
    }

    #[test]
    fn test_decrypt_keys_none_method() {
        // When method is None, input is treated as raw plaintext
        let raw_key1 = vec![1u8; 32];
        let raw_key2 = vec![2u8; 32];
        let config = KeyEncryptionCipher {
            method: CipherMethod::None,
            ..Default::default()
        };

        let (k1, k2) = decrypt_keys(raw_key1.clone(), raw_key2.clone(), config).unwrap();
        assert_eq!(k1.to_vec(), raw_key1);
        assert_eq!(k2.to_vec(), raw_key2);
    }

    #[test]
    fn test_aes_gcm_decrypt_failure_tampered_ciphertext() {
        let kek_key = [0x11u8; 32];
        let iv = [0x22u8; 12];
        let aad = b"aad";
        let target = [0xAAu8; 32];

        let mut enc = encrypt_helper(&kek_key, &iv, aad, &target);
        // Tamper with the last byte (part of the authentication tag)
        let last_idx = enc.len() - 1;
        enc[last_idx] ^= 0xFF;

        let config = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(kek_key.to_vec()),
            init_vector: Some(iv.to_vec()),
            auth_data: Some(aad.to_vec()),
        };

        let res = decrypt_keys(enc.clone(), enc, config);
        assert!(matches!(res, Err(UbiblkError::InvalidParameter { .. })));
    }

    #[test]
    fn test_aes_gcm_missing_parameters() {
        let config = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: None, // Missing key
            init_vector: Some(vec![0u8; 12]),
            auth_data: Some(vec![]),
        };
        let res = decrypt_psk_secret(vec![], &config);
        assert!(
            matches!(res, Err(UbiblkError::InvalidParameter { ref description }) if description == "Key is required")
        );
    }

    #[test]
    fn test_aes_gcm_invalid_iv_length() {
        let config = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(vec![0u8; 32]),
            init_vector: Some(vec![0u8; 11]), // 11 bytes (too short)
            auth_data: Some(vec![]),
        };
        let res = decrypt_psk_secret(vec![], &config);
        assert!(
            matches!(res, Err(UbiblkError::InvalidParameter { ref description }) if description.contains("12 bytes"))
        );
    }

    #[test]
    fn test_decrypt_keys_invalid_output_length() {
        let kek_key = [0x11u8; 32];
        let iv = [0x22u8; 12];
        let aad = b"aad";

        // Encrypting 31 bytes instead of 32
        let short_key = [0xAAu8; 31];
        let enc = encrypt_helper(&kek_key, &iv, aad, &short_key);

        let config = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(kek_key.to_vec()),
            init_vector: Some(iv.to_vec()),
            auth_data: Some(aad.to_vec()),
        };

        // Decryption succeeds, but length validation should fail
        let res = decrypt_keys(enc.clone(), enc, config);
        assert!(
            matches!(res, Err(UbiblkError::InvalidParameter { ref description }) if description.contains("exactly 32 bytes"))
        );
    }
}
