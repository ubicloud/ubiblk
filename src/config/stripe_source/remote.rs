use std::path::Path;

use serde::Deserialize;

use crate::crypt::{decode_optional_key, KeyEncryptionCipher};

#[derive(Clone, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case")]
pub struct RemoteStripeSourceConfig {
    pub address: String,
    #[serde(default)]
    pub psk_identity: Option<String>,
    #[serde(default, deserialize_with = "decode_optional_key")]
    pub psk_secret: Option<Vec<u8>>,
    #[serde(default)]
    pub allow_insecure: bool,
}

impl std::fmt::Debug for RemoteStripeSourceConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RemoteStripeSourceConfig")
            .field("address", &self.address)
            .field("psk_identity", &self.psk_identity)
            .field(
                "psk_secret",
                &self.psk_secret.as_ref().map(|_| "[REDACTED]"),
            )
            .field("allow_insecure", &self.allow_insecure)
            .finish()
    }
}

impl RemoteStripeSourceConfig {
    pub fn load_from_file_with_kek(path: &Path, kek: &KeyEncryptionCipher) -> crate::Result<Self> {
        let contents = std::fs::read_to_string(path).map_err(|e| {
            crate::ubiblk_error!(InvalidParameter {
                description: format!(
                    "Failed to read remote config file {}: {}",
                    path.display(),
                    e
                ),
            })
        })?;
        Self::load_from_str_with_kek(&contents, kek)
    }

    fn load_from_str_with_kek(yaml_str: &str, kek: &KeyEncryptionCipher) -> crate::Result<Self> {
        let mut config: RemoteStripeSourceConfig = serde_yaml::from_str(yaml_str).map_err(|e| {
            crate::ubiblk_error!(InvalidParameter {
                description: format!("Failed to parse remote config YAML: {}", e),
            })
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
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: "Both psk_identity and psk_secret must be specified together."
                    .to_string(),
            }));
        }
        if !self.allow_insecure && (self.psk_identity.is_none() || self.psk_secret.is_none()) {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: "PSK credentials must be provided unless allow_insecure is true."
                    .to_string(),
            }));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::config::StripeSourceConfig;

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

        let config: StripeSourceConfig = from_str(yaml).unwrap();

        assert_eq!(
            config,
            StripeSourceConfig::Remote {
                config: RemoteStripeSourceConfig {
                    address: "1.2.3.4:4567".to_string(),
                    psk_identity: Some("client1".to_string()),
                    psk_secret: Some(b"0123456789ABCDEF".to_vec()),
                    allow_insecure: false,
                },
            }
        );
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
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Both psk_identity and psk_secret must be specified together."));

        let yaml_identity_only = r#"
        address: "1.2.3.4:4567"
        psk_identity: client1
        "#;
        let result = RemoteStripeSourceConfig::load_from_str_with_kek(
            yaml_identity_only,
            &KeyEncryptionCipher::default(),
        );
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Both psk_identity and psk_secret must be specified together."));
    }

    #[test]
    fn test_remote_without_psk_pair_is_valid() {
        let yaml = r#"
        address: "1.2.3.4:4567"
        allow_insecure: true
        "#;
        let config =
            RemoteStripeSourceConfig::load_from_str_with_kek(yaml, &KeyEncryptionCipher::default())
                .unwrap();

        assert_eq!(config.address, "1.2.3.4:4567");
        assert!(config.psk_identity.is_none());
        assert!(config.psk_secret.is_none());
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

    #[test]
    fn test_load_from_file_with_kek_missing_path() {
        let result = RemoteStripeSourceConfig::load_from_file_with_kek(
            Path::new("/nonexistent/remote.yaml"),
            &KeyEncryptionCipher::default(),
        );
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Failed to read remote config file"));
    }

    #[test]
    fn test_load_from_str_with_kek_invalid_yaml() {
        let invalid_yaml = "xyz: [unclosed_list";
        let result = RemoteStripeSourceConfig::load_from_str_with_kek(
            invalid_yaml,
            &KeyEncryptionCipher::default(),
        );
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Failed to parse remote config YAML"));
    }

    #[test]
    fn test_default_allow_insecure() {
        let yaml = r#"
        address: "1.2.3.4:4567"
        psk_identity: client1
        psk_secret: "MDEyMzQ1Njc4OUFCQ0RFRg=="
        "#;
        let config =
            RemoteStripeSourceConfig::load_from_str_with_kek(yaml, &KeyEncryptionCipher::default())
                .unwrap();
        assert_eq!(config.address, "1.2.3.4:4567");
        assert!(!config.allow_insecure);
    }

    #[test]
    fn test_validation_fails_with_missing_psk_pair() {
        let yaml = r#"
        address: "1.2.3.4:4567"
        allow_insecure: false
        "#;
        let result =
            RemoteStripeSourceConfig::load_from_str_with_kek(yaml, &KeyEncryptionCipher::default());
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("PSK credentials must be provided unless allow_insecure is true."));
    }

    #[test]
    fn test_credential_redaction_in_debug() {
        let config = RemoteStripeSourceConfig {
            address: "1.2.3.4:4567".to_string(),
            psk_identity: Some("client1".to_string()),
            psk_secret: Some(vec![0xAA; 16]),
            allow_insecure: false,
        };
        let debug_str = format!("{:?}", config);
        assert!(debug_str.contains("address: \"1.2.3.4:4567\""));
        assert!(debug_str.contains("psk_identity: Some(\"client1\")"));
        assert!(debug_str.contains("psk_secret: Some(\"[REDACTED]\")"));
        assert!(debug_str.contains("allow_insecure: false"));
        assert!(!debug_str.contains("170")); // 0xAA = 170
    }
}
