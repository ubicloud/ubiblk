use std::path::{Component, Path};

use serde::Deserialize;

use crate::crypt::{decode_key, KeyEncryptionCipher};

fn default_archive_connections() -> usize {
    16
}

#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case")]
pub struct AwsCredentials {
    #[serde(deserialize_with = "decode_key")]
    pub access_key_id: Vec<u8>,
    #[serde(deserialize_with = "decode_key")]
    pub secret_access_key: Vec<u8>,
}

#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case", tag = "type")]
pub enum ArchiveStripeSourceConfig {
    Filesystem {
        path: String,
        #[serde(default)]
        archive_kek: KeyEncryptionCipher,
    },
    S3 {
        bucket: String,
        #[serde(default)]
        prefix: Option<String>,
        #[serde(default)]
        endpoint: Option<String>,
        #[serde(default)]
        region: Option<String>,
        #[serde(default)]
        profile: Option<String>,
        #[serde(default)]
        credentials: Option<AwsCredentials>,
        #[serde(default = "default_archive_connections")]
        connections: usize,
        #[serde(default)]
        archive_kek: KeyEncryptionCipher,
    },
}

impl ArchiveStripeSourceConfig {
    pub fn load_from_file_with_kek(path: &Path, kek: &KeyEncryptionCipher) -> crate::Result<Self> {
        let contents = std::fs::read_to_string(path).map_err(|e| {
            crate::ubiblk_error!(InvalidParameter {
                description: format!(
                    "Failed to read archive target config {}: {}",
                    path.display(),
                    e
                ),
            })
        })?;
        Self::load_from_str_with_kek(&contents, kek)
    }

    fn load_from_str_with_kek(yaml_str: &str, kek: &KeyEncryptionCipher) -> crate::Result<Self> {
        let mut config: ArchiveStripeSourceConfig =
            serde_yaml::from_str(yaml_str).map_err(|e| {
                crate::ubiblk_error!(InvalidParameter {
                    description: format!("Failed to parse archive target config YAML: {}", e),
                })
            })?;
        config.decrypt_with_kek(kek)?;
        config.validate()?;
        Ok(config)
    }

    pub fn archive_kek(&self) -> &KeyEncryptionCipher {
        match self {
            ArchiveStripeSourceConfig::Filesystem { archive_kek, .. } => archive_kek,
            ArchiveStripeSourceConfig::S3 { archive_kek, .. } => archive_kek,
        }
    }

    pub fn archive_kek_mut(&mut self) -> &mut KeyEncryptionCipher {
        match self {
            ArchiveStripeSourceConfig::Filesystem { archive_kek, .. } => archive_kek,
            ArchiveStripeSourceConfig::S3 { archive_kek, .. } => archive_kek,
        }
    }

    pub fn connections(&self) -> usize {
        match self {
            ArchiveStripeSourceConfig::Filesystem { .. } => default_archive_connections(),
            ArchiveStripeSourceConfig::S3 { connections, .. } => *connections,
        }
    }

    pub fn decrypt_with_kek(&mut self, kek: &KeyEncryptionCipher) -> crate::Result<()> {
        Self::decrypt_archive_kek(kek, self.archive_kek_mut())?;

        if let ArchiveStripeSourceConfig::S3 { credentials, .. } = self {
            if let Some(creds) = credentials.as_mut() {
                let access_key_id =
                    kek.decrypt_aws_credential(std::mem::take(&mut creds.access_key_id))?;
                let secret_access_key =
                    kek.decrypt_aws_credential(std::mem::take(&mut creds.secret_access_key))?;
                creds.access_key_id = access_key_id.into_bytes();
                creds.secret_access_key = secret_access_key.into_bytes();
            }
        }

        Ok(())
    }

    fn decrypt_archive_kek(
        kek: &KeyEncryptionCipher,
        archive_kek: &mut KeyEncryptionCipher,
    ) -> crate::Result<()> {
        Self::decrypt_optional_secret(kek, &mut archive_kek.key)?;
        Self::decrypt_optional_secret(kek, &mut archive_kek.init_vector)?;
        Self::decrypt_optional_secret(kek, &mut archive_kek.auth_data)?;
        Ok(())
    }

    fn decrypt_optional_secret(
        kek: &KeyEncryptionCipher,
        secret: &mut Option<Vec<u8>>,
    ) -> crate::Result<()> {
        if let Some(value) = secret.take() {
            *secret = Some(kek.decrypt_psk_secret(value)?);
        }
        Ok(())
    }

    fn validate(&self) -> crate::Result<()> {
        if let ArchiveStripeSourceConfig::S3 { prefix, .. } = self {
            Self::validate_prefix(prefix)?;
        }
        Ok(())
    }

    fn validate_prefix(prefix: &Option<String>) -> crate::Result<()> {
        if let Some(p) = prefix {
            if Path::new(p)
                .components()
                .any(|c| matches!(c, Component::CurDir | Component::ParentDir))
            {
                return Err(crate::ubiblk_error!(InvalidParameter {
                    description: format!("Invalid S3 prefix (contains . or .. components): {}", p),
                }));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::crypt::CipherMethod;
    use aes_gcm::{
        aead::{Aead, KeyInit, Payload},
        Aes256Gcm, Nonce,
    };
    use base64::{engine::general_purpose::STANDARD, Engine};
    use serde_yaml::from_str;
    use std::io::Write;
    use tempfile::NamedTempFile;

    fn encrypt_with_kek(kek_key: &[u8], iv: &[u8], aad: &[u8], plaintext: &[u8]) -> Vec<u8> {
        let cipher = Aes256Gcm::new_from_slice(kek_key).unwrap();
        let nonce = Nonce::from_slice(iv);
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
    fn test_filesystem_archive_source_parsing() {
        let yaml = r#"
        source: archive
        type: filesystem
        path: "/path/to/archive"
        "#;

        let config: super::super::StripeSourceConfig = from_str(yaml).unwrap();

        assert_eq!(
            config,
            super::super::StripeSourceConfig::Archive {
                config: ArchiveStripeSourceConfig::Filesystem {
                    path: "/path/to/archive".to_string(),
                    archive_kek: KeyEncryptionCipher::default(),
                }
            }
        );
    }

    #[test]
    fn test_s3_archive_source_parsing() {
        let yaml = r#"
        source: archive
        type: s3
        bucket: backups
        prefix: images
        endpoint: https://account.r2.cloudflarestorage.com
        region: auto
        profile: r2
        credentials:
          access_key_id: "QUtJQUlBQUFBQUFBQQ=="
          secret_access_key: "c2VjcmV0S2V5MTIzNDU2"
        "#;

        let config: super::super::StripeSourceConfig = from_str(yaml).unwrap();

        assert_eq!(
            config,
            super::super::StripeSourceConfig::Archive {
                config: ArchiveStripeSourceConfig::S3 {
                    bucket: "backups".to_string(),
                    prefix: Some("images".to_string()),
                    endpoint: Some("https://account.r2.cloudflarestorage.com".to_string()),
                    profile: Some("r2".to_string()),
                    region: Some("auto".to_string()),
                    credentials: Some(AwsCredentials {
                        access_key_id: b"AKIAIAAAAAAAA".to_vec(),
                        secret_access_key: b"secretKey123456".to_vec(),
                    }),
                    connections: 16,
                    archive_kek: KeyEncryptionCipher::default(),
                }
            }
        );
    }

    #[test]
    fn test_archive_kek_decryption() {
        let kek_key = [0x11u8; 32];
        let iv = [0x22u8; 12];
        let aad = b"test-aad";
        let kek = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(kek_key.to_vec()),
            init_vector: Some(iv.to_vec()),
            auth_data: Some(aad.to_vec()),
        };

        let archive_key = [0x33u8; 32];
        let archive_iv = [0x44u8; 12];
        let archive_aad = b"archive-aad";

        let cipher = Aes256Gcm::new_from_slice(&kek_key).unwrap();
        let nonce = Nonce::from_slice(&iv);
        let enc_key = cipher
            .encrypt(
                nonce,
                Payload {
                    msg: &archive_key,
                    aad,
                },
            )
            .unwrap();
        let enc_iv = cipher
            .encrypt(
                nonce,
                Payload {
                    msg: &archive_iv,
                    aad,
                },
            )
            .unwrap();
        let enc_aad = cipher
            .encrypt(
                nonce,
                Payload {
                    msg: archive_aad,
                    aad,
                },
            )
            .unwrap();

        let yaml = format!(
            r#"
        type: filesystem
        path: "/path/to/archive"
        archive_kek:
          method: aes256-gcm
          key: "{}"
          init_vector: "{}"
          auth_data: "{}"
        "#,
            STANDARD.encode(enc_key),
            STANDARD.encode(enc_iv),
            STANDARD.encode(enc_aad),
        );

        let config = ArchiveStripeSourceConfig::load_from_str_with_kek(&yaml, &kek).unwrap();
        let archive_kek = config.archive_kek();
        assert_eq!(archive_kek.method, CipherMethod::Aes256Gcm);
        assert_eq!(archive_kek.key, Some(archive_key.to_vec()));
        assert_eq!(archive_kek.init_vector, Some(archive_iv.to_vec()));
        assert_eq!(archive_kek.auth_data, Some(archive_aad.to_vec()));
    }

    #[test]
    fn test_connections_and_archive_kek_mutation() {
        let mut config = ArchiveStripeSourceConfig::Filesystem {
            path: "/tmp/archive".to_string(),
            archive_kek: KeyEncryptionCipher::default(),
        };

        assert_eq!(config.connections(), 16);

        let archive_kek = config.archive_kek_mut();
        archive_kek.method = CipherMethod::Aes256Gcm;
        archive_kek.key = Some(vec![0xAA; 32]);
        archive_kek.init_vector = Some(vec![0xBB; 12]);
        archive_kek.auth_data = Some(b"kek-aad".to_vec());

        assert_eq!(config.archive_kek().method, CipherMethod::Aes256Gcm);

        let s3_config = ArchiveStripeSourceConfig::S3 {
            bucket: "bucket".to_string(),
            prefix: None,
            endpoint: None,
            region: None,
            profile: None,
            credentials: None,
            connections: 32,
            archive_kek: KeyEncryptionCipher::default(),
        };
        assert_eq!(s3_config.connections(), 32);
    }

    #[test]
    fn test_archive_kek_for_s3() {
        let kek = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(vec![0xCC; 32]),
            init_vector: Some(vec![0xDD; 12]),
            auth_data: Some(b"s3-aad".to_vec()),
        };
        let config = ArchiveStripeSourceConfig::S3 {
            bucket: "bucket".to_string(),
            archive_kek: kek.clone(),
            prefix: None,
            endpoint: None,
            region: None,
            profile: None,
            credentials: None,
            connections: 16,
        };
        assert_eq!(config.archive_kek(), &kek);
    }

    #[test]
    fn test_load_from_file_with_kek_decrypts_credentials() {
        let kek_key = [0x10u8; 32];
        let iv = [0x20u8; 12];
        let aad = b"cred-aad";
        let kek = KeyEncryptionCipher {
            method: CipherMethod::Aes256Gcm,
            key: Some(kek_key.to_vec()),
            init_vector: Some(iv.to_vec()),
            auth_data: Some(aad.to_vec()),
        };

        let access_key_plain = b"ACCESSKEY";
        let secret_key_plain = b"SECRETKEY123";
        let enc_access_key = encrypt_with_kek(&kek_key, &iv, aad, access_key_plain);
        let enc_secret_key = encrypt_with_kek(&kek_key, &iv, aad, secret_key_plain);

        let yaml = format!(
            r#"
        type: s3
        bucket: backups
        credentials:
          access_key_id: "{}"
          secret_access_key: "{}"
        "#,
            STANDARD.encode(enc_access_key),
            STANDARD.encode(enc_secret_key),
        );

        let mut file = NamedTempFile::new().unwrap();
        file.write_all(yaml.as_bytes()).unwrap();

        let config = ArchiveStripeSourceConfig::load_from_file_with_kek(file.path(), &kek).unwrap();
        assert_eq!(
            config,
            ArchiveStripeSourceConfig::S3 {
                bucket: "backups".to_string(),
                prefix: None,
                endpoint: None,
                region: None,
                profile: None,
                credentials: Some(AwsCredentials {
                    access_key_id: access_key_plain.to_vec(),
                    secret_access_key: secret_key_plain.to_vec(),
                }),
                connections: 16,
                archive_kek: KeyEncryptionCipher::default(),
            }
        );
    }

    #[test]
    fn test_load_from_str_with_kek_defaults_and_no_credentials() {
        let yaml = r#"
        type: s3
        bucket: backups
        "#;

        let config = ArchiveStripeSourceConfig::load_from_str_with_kek(
            yaml,
            &KeyEncryptionCipher::default(),
        )
        .unwrap();

        assert_eq!(
            config,
            ArchiveStripeSourceConfig::S3 {
                bucket: "backups".to_string(),
                prefix: None,
                endpoint: None,
                region: None,
                profile: None,
                credentials: None,
                connections: 16,
                archive_kek: KeyEncryptionCipher::default(),
            }
        );
    }

    #[test]
    fn test_load_from_file_with_kek_missing_path() {
        let result = ArchiveStripeSourceConfig::load_from_file_with_kek(
            Path::new("/nonexistent/archive.yaml"),
            &KeyEncryptionCipher::default(),
        );
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Failed to read archive target config"));
    }

    #[test]
    fn test_load_from_str_with_kek_invalid_yaml() {
        let invalid_yaml = "xyz: [unclosed_list";
        let result = ArchiveStripeSourceConfig::load_from_str_with_kek(
            invalid_yaml,
            &KeyEncryptionCipher::default(),
        );
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Failed to parse archive target config YAML"));
    }

    #[test]
    fn test_validate_prefix_with_invalid_components() {
        let invalid_prefix = Some("valid/../invalid".to_string());
        let result = ArchiveStripeSourceConfig::validate_prefix(&invalid_prefix);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Invalid S3 prefix (contains . or .. components)"));
    }
}
