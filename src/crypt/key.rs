use crate::{Result, UbiblkError};
use aes_gcm::{
    aead::{Aead, AeadCore, KeyInit, OsRng, Payload},
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
#[derive(Clone, Serialize, Deserialize, Default, PartialEq)]
pub struct KeyEncryptionCipher {
    pub method: CipherMethod,

    #[serde_as(as = "Option<Base64>")]
    pub key: Option<Vec<u8>>,

    #[serde_as(as = "Option<Base64>")]
    pub auth_data: Option<Vec<u8>>,
}

impl std::fmt::Debug for KeyEncryptionCipher {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("KeyEncryptionCipher")
            .field("method", &self.method)
            .field("key", &self.key.as_ref().map(|_| "[REDACTED]"))
            .field("auth_data", &self.auth_data.as_ref().map(|_| "[REDACTED]"))
            .finish()
    }
}

type KekNonce = Nonce<<Aes256Gcm as AeadCore>::NonceSize>;

/// GCM tag size in bytes.
const GCM_TAG_SIZE: usize = 16;
/// GCM nonce size in bytes.
const GCM_NONCE_SIZE: usize = 12;

impl KeyEncryptionCipher {
    /// Validate and return references to the key and authentication data.
    fn init_context(&self) -> Result<(&[u8], &[u8])> {
        let key = self
            .key
            .as_ref()
            .ok_or_else(|| param_err("Key is required"))?;

        let auth_data = self
            .auth_data
            .as_ref()
            .ok_or_else(|| param_err("Authentication data is required"))?;

        Ok((key, auth_data))
    }

    pub fn encrypt_xts_keys(&self, key1: &[u8], key2: &[u8]) -> Result<(Vec<u8>, Vec<u8>)> {
        match self.method {
            CipherMethod::None => Ok((key1.to_vec(), key2.to_vec())),
            CipherMethod::Aes256Gcm => {
                let (key, auth) = self.init_context()?;

                let k1 = aes256gcm_encrypt(key, auth, key1)?;
                let k2 = aes256gcm_encrypt(key, auth, key2)?;

                Ok((k1, k2))
            }
        }
    }

    pub fn decrypt_xts_keys(&self, key1: Vec<u8>, key2: Vec<u8>) -> Result<([u8; 32], [u8; 32])> {
        match self.method {
            CipherMethod::None => {
                // "None" implies inputs are already plain text; just validate length.
                Ok((ensure_32_bytes(key1)?, ensure_32_bytes(key2)?))
            }
            CipherMethod::Aes256Gcm => {
                let (key, auth) = self.init_context()?;

                let k1 = aes256gcm_decrypt(key, auth, &key1)?;
                let k2 = aes256gcm_decrypt(key, auth, &key2)?;

                Ok((ensure_32_bytes(k1)?, ensure_32_bytes(k2)?))
            }
        }
    }

    pub fn decrypt_psk_secret(&self, secret: Vec<u8>) -> Result<Vec<u8>> {
        match self.method {
            CipherMethod::None => Ok(secret),
            CipherMethod::Aes256Gcm => {
                let (key, auth) = self.init_context()?;
                aes256gcm_decrypt(key, auth, &secret)
            }
        }
    }

    pub fn decrypt_aws_credential(&self, cred: Vec<u8>) -> Result<String> {
        let decrypted_bytes = match self.method {
            CipherMethod::None => cred,
            CipherMethod::Aes256Gcm => {
                let (key, auth) = self.init_context()?;
                aes256gcm_decrypt(key, auth, &cred)?
            }
        };

        String::from_utf8(decrypted_bytes).map_err(|e| {
            let msg = format!("Decrypted AWS credential is not valid UTF-8: {e}");
            error!("{}", msg);
            param_err(msg)
        })
    }

    pub fn encrypt_key_data(&self, plaintext: &[u8]) -> Result<Vec<u8>> {
        match self.method {
            CipherMethod::None => Ok(plaintext.to_vec()),
            CipherMethod::Aes256Gcm => {
                let (key, auth) = self.init_context()?;
                aes256gcm_encrypt(key, auth, plaintext)
            }
        }
    }

    pub fn decrypt_key_data(&self, ciphertext: &[u8]) -> Result<Vec<u8>> {
        match self.method {
            CipherMethod::None => Ok(ciphertext.to_vec()),
            CipherMethod::Aes256Gcm => {
                let (key, auth) = self.init_context()?;
                aes256gcm_decrypt(key, auth, ciphertext)
            }
        }
    }
}

fn new_cipher(key: &[u8]) -> Result<Aes256Gcm> {
    Aes256Gcm::new_from_slice(key).map_err(|e| {
        let msg = format!("Failed to initialize cipher: {e}");
        error!("{}", msg);
        param_err(msg)
    })
}

/// Decrypt data in the format [12-byte nonce || ciphertext || 16-byte tag].
pub fn aes256gcm_decrypt(key: &[u8], aad: &[u8], ciphertext: &[u8]) -> Result<Vec<u8>> {
    let cipher = new_cipher(key)?;

    // Minimum new-format length: nonce (12) + tag (16) + at least 0 bytes of ciphertext = 28
    if ciphertext.len() < GCM_NONCE_SIZE + GCM_TAG_SIZE {
        let msg = "Failed to decrypt data: ciphertext is too short to include nonce and tag";
        error!("{}", msg);
        return Err(param_err(msg));
    }

    let nonce = KekNonce::from_slice(&ciphertext[..GCM_NONCE_SIZE]);
    let encrypted_data = &ciphertext[GCM_NONCE_SIZE..];
    let plaintext = cipher
        .decrypt(
            nonce,
            Payload {
                msg: encrypted_data,
                aad,
            },
        )
        .map_err(|e| {
            let msg = format!("Failed to decrypt data: {e}");
            error!("{}", msg);
            param_err(msg)
        })?;

    Ok(plaintext)
}

/// Encrypt data with a per-call random nonce. Output format:
/// [12-byte random nonce || ciphertext || 16-byte GCM tag]
pub fn aes256gcm_encrypt(key: &[u8], aad: &[u8], plaintext: &[u8]) -> Result<Vec<u8>> {
    let cipher = new_cipher(key)?;

    let nonce = Aes256Gcm::generate_nonce(&mut OsRng);
    let ciphertext = cipher
        .encrypt(
            &nonce,
            Payload {
                msg: plaintext,
                aad,
            },
        )
        .map_err(|e| {
            let msg = format!("Failed to encrypt data: {e}");
            error!("{}", msg);
            param_err(msg)
        })?;

    // Prepend nonce to ciphertext
    let mut output = Vec::with_capacity(GCM_NONCE_SIZE + ciphertext.len());
    output.extend_from_slice(&nonce);
    output.extend_from_slice(&ciphertext);
    Ok(output)
}

fn ensure_32_bytes(data: Vec<u8>) -> Result<[u8; 32]> {
    data.try_into().map_err(|_| {
        let msg = "Key length must be exactly 32 bytes";
        error!("{}", msg);
        param_err(msg)
    })
}

#[track_caller]
fn param_err(description: impl Into<String>) -> UbiblkError {
    let location = std::panic::Location::caller();
    UbiblkError::InvalidParameter {
        description: description.into(),
        meta: crate::ErrorMeta::new(crate::ErrorLocation::new(location.file(), location.line())),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use aes_gcm::KeyInit;

    fn encrypt_helper(kek_key: &[u8], nonce: &[u8], aad: &[u8], plaintext: &[u8]) -> Vec<u8> {
        let cipher = Aes256Gcm::new_from_slice(kek_key).unwrap();
        let nonce = KekNonce::from_slice(nonce);
        let ciphertext = cipher
            .encrypt(
                nonce,
                Payload {
                    msg: plaintext,
                    aad,
                },
            )
            .unwrap();
        let mut output = Vec::with_capacity(GCM_NONCE_SIZE + ciphertext.len());
        output.extend_from_slice(nonce);
        output.extend_from_slice(&ciphertext);
        output
    }

    #[test]
    fn test_debug_redacts_sensitive_fields() {
        let cipher = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(vec![0xAA; 32]),
            auth_data: Some(vec![0xCC; 8]),
        };
        let debug_output = format!("{:?}", cipher);
        assert!(
            debug_output.contains("Aes256Gcm"),
            "method should be visible"
        );
        assert!(
            debug_output.contains("[REDACTED]"),
            "should contain [REDACTED]"
        );
        assert!(!debug_output.contains("170"), "key bytes leaked in Debug");
        assert!(
            !debug_output.contains("204"),
            "auth_data bytes leaked in Debug"
        );
    }

    #[test]
    fn test_decrypt_keys_aes_gcm_success() {
        let kek_key = [0x11u8; 32];
        let nonce = [0x22u8; 12];
        let aad = b"test-aad";

        // The actual secret keys we want to protect
        let target_key1 = [0xAAu8; 32];
        let target_key2 = [0xBBu8; 32];

        let enc1 = encrypt_helper(&kek_key, &nonce, aad, &target_key1);
        let enc2 = encrypt_helper(&kek_key, &nonce, aad, &target_key2);

        let cipher = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(kek_key.to_vec()),
            auth_data: Some(aad.to_vec()),
        };

        let (res1, res2) = cipher
            .decrypt_xts_keys(enc1, enc2)
            .expect("Decryption should succeed");
        assert_eq!(res1, target_key1);
        assert_eq!(res2, target_key2);
    }

    #[test]
    fn test_decrypt_psk_secret_aes_gcm_success() {
        let kek_key = [0x33u8; 32];
        let nonce = [0x44u8; 12];
        let aad = b"psk-aad";
        let secret_msg = b"super secret psk string";

        let enc_secret = encrypt_helper(&kek_key, &nonce, aad, secret_msg);

        let cipher = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(kek_key.to_vec()),
            auth_data: Some(aad.to_vec()),
        };

        let res = cipher
            .decrypt_psk_secret(enc_secret)
            .expect("Decryption should succeed");
        assert_eq!(res, secret_msg);
    }

    #[test]
    fn test_decrypt_keys_none_method() {
        // When method is None, input is treated as raw plaintext
        let raw_key1 = vec![1u8; 32];
        let raw_key2 = vec![2u8; 32];
        let cipher = KeyEncryptionCipher {
            method: CipherMethod::None,
            ..Default::default()
        };

        let (k1, k2) = cipher
            .decrypt_xts_keys(raw_key1.clone(), raw_key2.clone())
            .unwrap();
        assert_eq!(k1.to_vec(), raw_key1);
        assert_eq!(k2.to_vec(), raw_key2);
    }

    #[test]
    fn test_aes_gcm_decrypt_failure_tampered_ciphertext() {
        let kek_key = [0x11u8; 32];
        let nonce = [0x22u8; 12];
        let aad = b"aad";
        let target = [0xAAu8; 32];

        let mut enc = encrypt_helper(&kek_key, &nonce, aad, &target);
        // Tamper with the last byte (part of the authentication tag)
        let last_idx = enc.len() - 1;
        enc[last_idx] ^= 0xFF;

        let cipher = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(kek_key.to_vec()),
            auth_data: Some(aad.to_vec()),
        };

        let res = cipher.decrypt_xts_keys(enc.clone(), enc);
        assert!(matches!(res, Err(UbiblkError::InvalidParameter { .. })));
    }

    #[test]
    fn test_decrypt_rejects_short_ciphertext() {
        let cipher = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(vec![0x11u8; 32]),
            auth_data: Some(b"short-aad".to_vec()),
        };

        let short_ciphertext = vec![0x00u8; 10];
        let res = cipher.decrypt_key_data(&short_ciphertext);
        assert!(
            matches!(res, Err(UbiblkError::InvalidParameter { ref description, .. }) if description.contains("too short"))
        );
    }

    #[test]
    fn test_aes_gcm_missing_parameters() {
        let cipher = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: None, // Missing key
            auth_data: Some(vec![]),
        };
        let res = cipher.decrypt_psk_secret(vec![]);
        assert!(
            matches!(res, Err(UbiblkError::InvalidParameter { ref description, .. }) if description == "Key is required")
        );
    }

    #[test]
    fn test_decrypt_keys_invalid_output_length() {
        let kek_key = [0x11u8; 32];
        let nonce = [0x22u8; 12];
        let aad = b"aad";

        // Encrypting 31 bytes instead of 32
        let short_key = [0xAAu8; 31];
        let enc = encrypt_helper(&kek_key, &nonce, aad, &short_key);

        let cipher = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(kek_key.to_vec()),
            auth_data: Some(aad.to_vec()),
        };

        // Decryption succeeds, but length validation should fail
        let res = cipher.decrypt_xts_keys(enc.clone(), enc);
        assert!(
            matches!(res, Err(UbiblkError::InvalidParameter { ref description, .. }) if description.contains("exactly 32 bytes"))
        );
    }

    #[test]
    fn test_encrypt_xts_keys_none_method() {
        let key1 = [0xAAu8; 32];
        let key2 = [0xBBu8; 32];

        let cipher = KeyEncryptionCipher {
            method: CipherMethod::None,
            ..Default::default()
        };

        let (enc1, enc2) = cipher.encrypt_xts_keys(&key1, &key2).unwrap();
        assert_eq!(enc1, key1);
        assert_eq!(enc2, key2);
    }

    #[test]
    fn test_encrypt_xts_keys_aes_gcm_success() {
        let kek_key = [0x11u8; 32];
        let aad = b"test-aad";

        let key1 = [0xAAu8; 32];
        let key2 = [0xBBu8; 32];

        let cipher = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(kek_key.to_vec()),
            auth_data: Some(aad.to_vec()),
        };

        let (enc1, enc2) = cipher.encrypt_xts_keys(&key1, &key2).unwrap();
        assert_ne!(enc1, key1);
        assert_ne!(enc2, key2);

        // Decrypt to verify correctness
        let (dec1, dec2) = cipher.decrypt_xts_keys(enc1, enc2).unwrap();
        assert_eq!(dec1, key1);
        assert_eq!(dec2, key2);
    }

    #[test]
    fn test_decrypt_aws_credential_aes_gcm_success() {
        let kek_key = [0x33u8; 32];
        let nonce = [0x44u8; 12];
        let aad = b"aws-cred-aad";
        let credential_str = "AKIAEXAMPLEACCESSKEY";
        let credential_bytes = credential_str.as_bytes();
        let enc_cred = encrypt_helper(&kek_key, &nonce, aad, credential_bytes);
        let cipher = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(kek_key.to_vec()),
            auth_data: Some(aad.to_vec()),
        };
        let dec_cred = cipher
            .decrypt_aws_credential(enc_cred)
            .expect("Decryption should succeed");
        assert_eq!(dec_cred, credential_str);
    }

    #[test]
    fn test_decrypt_aws_credential_none_method() {
        let credential_str = "AKIAEXAMPLEACCESSKEY";
        let credential_bytes = credential_str.as_bytes().to_vec();
        let cipher = KeyEncryptionCipher {
            method: CipherMethod::None,
            ..Default::default()
        };
        let dec_cred = cipher
            .decrypt_aws_credential(credential_bytes.clone())
            .expect("Decryption should succeed");
        assert_eq!(dec_cred, credential_str);
    }

    #[test]
    fn test_decrypt_aws_credential_invalid_utf8() {
        let kek_key = [0x33u8; 32];
        let nonce = [0x44u8; 12];
        let aad = b"aws-cred-aad";
        let invalid_utf8 = vec![0xFF, 0xFE, 0xFD]; // Invalid UTF-8 bytes
        let enc_cred = encrypt_helper(&kek_key, &nonce, aad, &invalid_utf8);
        let cipher = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(kek_key.to_vec()),
            auth_data: Some(aad.to_vec()),
        };
        let res = cipher.decrypt_aws_credential(enc_cred);
        assert!(
            matches!(res, Err(UbiblkError::InvalidParameter { ref description, .. }) if description.contains("valid UTF-8"))
        );
    }

    #[test]
    fn test_encrypt_decrypt_roundtrip_random_nonce() {
        let kek_key = [0x55u8; 32];
        let aad = b"roundtrip-aad";
        let plaintext = b"the quick brown fox jumps over the lazy dog";

        let cipher = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(kek_key.to_vec()),
            auth_data: Some(aad.to_vec()),
        };

        let encrypted = cipher.encrypt_key_data(plaintext).unwrap();
        // New format: 12 nonce + plaintext_len + 16 tag
        assert_eq!(
            encrypted.len(),
            GCM_NONCE_SIZE + plaintext.len() + GCM_TAG_SIZE
        );

        let decrypted = cipher.decrypt_key_data(&encrypted).unwrap();
        assert_eq!(decrypted, plaintext);
    }

    #[test]
    fn test_encrypt_produces_different_ciphertexts() {
        let kek_key = [0x66u8; 32];
        let aad = b"nonce-test-aad";
        let plaintext = [0xCCu8; 32];

        let cipher = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(kek_key.to_vec()),
            auth_data: Some(aad.to_vec()),
        };

        let enc1 = cipher.encrypt_key_data(&plaintext).unwrap();
        let enc2 = cipher.encrypt_key_data(&plaintext).unwrap();

        // The two encryptions of the same plaintext must differ (random nonces)
        assert_ne!(
            enc1, enc2,
            "Two encryptions of identical plaintext must produce different ciphertexts"
        );

        // Both must decrypt to the same plaintext
        let dec1 = cipher.decrypt_key_data(&enc1).unwrap();
        let dec2 = cipher.decrypt_key_data(&enc2).unwrap();
        assert_eq!(dec1, plaintext);
        assert_eq!(dec2, plaintext);
    }
}
