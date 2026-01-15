use std::path::Path;

use serde::Deserialize;

use crate::crypt::{decode_optional_key, KeyEncryptionCipher};

#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case")]
pub struct RemoteStripeSourceConfig {
    pub address: String,
    #[serde(default)]
    pub psk_identity: Option<String>,
    #[serde(default, deserialize_with = "decode_optional_key")]
    pub psk_secret: Option<Vec<u8>>,
}

impl RemoteStripeSourceConfig {
    pub fn load_from_file_with_kek(path: &Path, kek: &KeyEncryptionCipher) -> crate::Result<Self> {
        let contents =
            std::fs::read_to_string(path).map_err(|e| crate::UbiblkError::InvalidParameter {
                description: format!(
                    "Failed to read remote config file {}: {}",
                    path.display(),
                    e
                ),
            })?;
        Self::load_from_str_with_kek(&contents, kek)
    }

    fn load_from_str_with_kek(yaml_str: &str, kek: &KeyEncryptionCipher) -> crate::Result<Self> {
        let mut config: RemoteStripeSourceConfig =
            serde_yaml::from_str(yaml_str).map_err(|e| crate::UbiblkError::InvalidParameter {
                description: format!("Failed to parse remote config YAML: {}", e),
            })?;
        config.decrypt_with_kek(kek)?;
        config.validate()?;
        Ok(config)
    }

    pub(crate) fn decrypt_with_kek(&mut self, kek: &KeyEncryptionCipher) -> crate::Result<()> {
        if let Some(secret) = self.psk_secret.take() {
            self.psk_secret = Some(kek.decrypt_psk_secret(secret)?);
        }
        Ok(())
    }

    pub(crate) fn validate(&self) -> crate::Result<()> {
        if self.psk_identity.is_some() ^ self.psk_secret.is_some() {
            return Err(crate::UbiblkError::InvalidParameter {
                description: "Both psk_identity and psk_secret must be specified together."
                    .to_string(),
            });
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use aes_gcm::aead::{Aead, KeyInit, Payload};
    use base64::{engine::general_purpose::STANDARD, Engine};
    use serde_yaml::from_str;
    use std::io::Write;
    use tempfile::NamedTempFile;

    fn encrypt_with_kek(kek_key: &[u8], iv: &[u8], aad: &[u8], plaintext: &[u8]) -> Vec<u8> {
        let cipher = aes_gcm::Aes256Gcm::new_from_slice(kek_key).unwrap();
        let nonce = aes_gcm::Nonce::from_slice(iv);
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
    fn test_remote_stripe_source_parsing() {
        let yaml = r#"
        source: remote
        address: "1.2.3.4:4567"
        psk_identity: client1
        psk_secret: "MDEyMzQ1Njc4OUFCQ0RFRg=="
        "#;

        let config: super::super::StripeSourceConfig = from_str(yaml).unwrap();
        match config {
            super::super::StripeSourceConfig::Remote { config } => {
                assert_eq!(config.psk_identity.as_deref(), Some("client1"));
                assert_eq!(
                    config.psk_secret.as_deref(),
                    Some(b"0123456789ABCDEF".as_ref())
                );
            }
            other => panic!("Unexpected stripe source: {other:?}"),
        }
    }

    #[test]
    fn test_missing_psk_pair() {
        let yaml_secret_only = r#"
        address: "1.2.3.4:4567"
        psk_secret: "MDEyMzQ1Njc4OUFCQ0RFRg=="
        "#;
        let result = RemoteStripeSourceConfig::load_from_str_with_kek(
            yaml_secret_only,
            &KeyEncryptionCipher::default(),
        );
        assert!(result.is_err());

        let yaml_identity_only = r#"
        address: "1.2.3.4:4567"
        psk_identity: client1
        "#;
        let result = RemoteStripeSourceConfig::load_from_str_with_kek(
            yaml_identity_only,
            &KeyEncryptionCipher::default(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn test_load_from_file_with_kek_decrypts_secret() {
        let kek_key = [0x42u8; 32];
        let iv = [0x99u8; 12];
        let aad = b"remote-aad";
        let kek = KeyEncryptionCipher {
            method: crate::crypt::CipherMethod::Aes256Gcm,
            key: Some(kek_key.to_vec()),
            init_vector: Some(iv.to_vec()),
            auth_data: Some(aad.to_vec()),
        };

        let secret_plain = b"super-secret";
        let encrypted_secret = encrypt_with_kek(&kek_key, &iv, aad, secret_plain);
        let encoded_secret = STANDARD.encode(encrypted_secret);

        let yaml = format!(
            r#"
        address: "1.2.3.4:4567"
        psk_identity: client1
        psk_secret: "{encoded_secret}"
        "#
        );

        let mut file = NamedTempFile::new().unwrap();
        file.write_all(yaml.as_bytes()).unwrap();

        let config = RemoteStripeSourceConfig::load_from_file_with_kek(file.path(), &kek).unwrap();
        assert_eq!(config.psk_identity.as_deref(), Some("client1"));
        assert_eq!(config.psk_secret.as_deref(), Some(secret_plain.as_ref()));
    }

    // Decryption behavior is covered by crypt module tests; here we focus on parsing/validation.
}
