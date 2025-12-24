use crate::{Result, VhostUserBlockError};
use aes_gcm::{
    aead::{Aead, AeadCore, Payload},
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

pub fn decrypt_keys(
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
            use aes_gcm::KeyInit;
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
                error!("Initialization vector must be exactly 12 bytes");
                return Err(VhostUserBlockError::InvalidParameter {
                    description: "Initialization vector must be exactly 12 bytes".to_string(),
                });
            }
            let nonce_bytes: [u8; 12] = kek_iv.as_slice().try_into().map_err(|_| {
                error!("Initialization vector must be exactly 12 bytes");
                VhostUserBlockError::InvalidParameter {
                    description: "Initialization vector must be exactly 12 bytes".to_string(),
                }
            })?;
            let nonce = KekNonce::from(nonce_bytes);

            let clear1 = decrypt_block(&cipher, &nonce, &kek_auth_data, &key1)?;
            let clear2 = decrypt_block(&cipher, &nonce, &kek_auth_data, &key2)?;
            Ok((clear1, clear2))
        }
    }
}

type KekNonce = Nonce<<Aes256Gcm as AeadCore>::NonceSize>;

fn decrypt_block(
    cipher: &Aes256Gcm,
    nonce: &KekNonce,
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

    #[test]
    fn test_decrypt_block_failure() {
        use aes_gcm::{Aes256Gcm, KeyInit};

        let cipher = Aes256Gcm::new_from_slice(&[0u8; 32]).unwrap();
        let nonce = KekNonce::from([0u8; 12]);
        let enc = vec![0u8; 48];

        let res = decrypt_block(&cipher, &nonce, &[], &enc);
        assert!(matches!(
            res,
            Err(VhostUserBlockError::InvalidParameter { .. })
        ));
    }

    #[test]
    fn test_decrypt_block_bad_plain_length() {
        use aes_gcm::{aead::KeyInit as AeadKeyInit, Aes256Gcm};
        let cipher = Aes256Gcm::new_from_slice(&[0u8; 32]).unwrap();
        let nonce = KekNonce::from([0u8; 12]);
        let data = [1u8; 8];
        let enc = cipher
            .encrypt(
                &nonce,
                Payload {
                    msg: &data,
                    aad: b"",
                },
            )
            .unwrap();

        let res = decrypt_block(&cipher, &nonce, b"", &enc);
        assert!(matches!(
            res,
            Err(VhostUserBlockError::InvalidParameter { .. })
        ));
    }
}
