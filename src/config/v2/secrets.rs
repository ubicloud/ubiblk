use std::{
    collections::HashMap,
    fs::File,
    io::Read,
    path::{Path, PathBuf},
};

use base64::Engine;
use serde::Deserialize;

use super::DangerZone;
use crate::{crypt::aes256gcm_decrypt, ubiblk_error, Result, ResultExt};

use base64::engine::general_purpose::STANDARD as b64_engine;

const MAX_SECRET_BYTES: usize = 8192;

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SecretSource {
    File(PathBuf),
    Base64(String),
    Env(String),
}

#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case")]
pub enum SecretRef {
    Ref(String),
}

impl SecretRef {
    pub fn id(&self) -> &str {
        match self {
            SecretRef::Ref(id) => id,
        }
    }
}

/// A secret definition as parsed from a `[secrets.<name>]` TOML sub-table.
#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct SecretDef {
    /// Source descriptor from TOML, using one of `source.file`, `source.base64`, or `source.env`.
    pub source: SecretSource,
    /// Optional KEK reference from the `kek.ref` TOML field.
    pub kek: Option<SecretRef>,
}

/// Resolved secret bytes ready for use by the rest of the config system.
#[derive(Clone)]
pub struct ResolvedSecret {
    bytes: Vec<u8>,
}

impl std::fmt::Debug for ResolvedSecret {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ResolvedSecret")
            .field("bytes", &"[REDACTED]")
            .finish()
    }
}

impl ResolvedSecret {
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }
}

impl Drop for ResolvedSecret {
    fn drop(&mut self) {
        zeroize::Zeroize::zeroize(&mut self.bytes);
    }
}

/// Parse the `[secrets]` table from a TOML value.
///
/// Expects a TOML table where each key maps to a sub-table with `source` and
/// optional `kek` fields.
pub fn parse_secrets(table: &toml::Value) -> Result<HashMap<String, SecretDef>> {
    let Some(value) = table.get("secrets") else {
        return Ok(HashMap::new());
    };

    if !value.is_table() {
        return Err(ubiblk_error!(InvalidParameter {
            description: "[secrets] must be a table".to_string()
        }));
    }

    value.clone().try_into().map_err(|e| {
        ubiblk_error!(InvalidParameter {
            description: format!("secrets: {e}")
        })
    })
}

/// Resolve all secret definitions into their final byte values.
pub fn resolve_secrets(
    defs: &HashMap<String, SecretDef>,
    danger_zone: &DangerZone,
) -> Result<HashMap<String, ResolvedSecret>> {
    let secret_count = defs.len();
    let mut resolved: HashMap<String, ResolvedSecret> = HashMap::new();

    let mut remaining_defs: Vec<(&String, &SecretDef)> = defs.iter().collect();

    for (name, def) in defs {
        if let Some(SecretRef::Ref(kek_ref)) = &def.kek {
            if !defs.contains_key(kek_ref) {
                return Err(ubiblk_error!(InvalidParameter {
                    description: format!("secrets.{name}: missing KEK reference '{kek_ref}'")
                }));
            }
        }
    }

    while resolved.len() < secret_count {
        let mut updated_remaining_defs = Vec::new();

        for (name, def) in remaining_defs.iter() {
            let maybe_resolved = maybe_resolve_secret(name, def, &resolved, danger_zone)?;
            if let Some(resolved_secret) = maybe_resolved {
                resolved.insert((*name).clone(), resolved_secret);
            } else {
                updated_remaining_defs.push((*name, *def));
            }
        }

        if updated_remaining_defs.len() == remaining_defs.len() {
            return Err(ubiblk_error!(InvalidParameter {
                description: "circular secret references detected".to_string()
            }));
        }

        remaining_defs = updated_remaining_defs;
    }

    Ok(resolved)
}

pub fn maybe_resolve_secret(
    name: &str,
    def: &SecretDef,
    resolved: &HashMap<String, ResolvedSecret>,
    danger_zone: &DangerZone,
) -> Result<Option<ResolvedSecret>> {
    if let Some(SecretRef::Ref(kek_ref)) = &def.kek {
        let Some(kek_secret) = resolved.get(kek_ref) else {
            return Ok(None);
        };
        let kek_bytes = kek_secret.as_bytes();
        let ciphertext = load_source(name, &def.source, true, danger_zone)?;
        // Secret name is used as AAD to bind ciphertext to its config slot.
        let decrypted = aes256gcm_decrypt(kek_bytes, name.as_bytes(), &ciphertext).context(
            format!("secrets.{name}: failed to decrypt using KEK '{kek_ref}'"),
        )?;
        Ok(Some(ResolvedSecret { bytes: decrypted }))
    } else {
        // No KEK; just load the source directly.
        let bytes = load_source(name, &def.source, false, danger_zone)?;
        Ok(Some(ResolvedSecret { bytes }))
    }
}

fn load_source(
    name: &str,
    source: &SecretSource,
    encrypted: bool,
    danger_zone: &DangerZone,
) -> Result<Vec<u8>> {
    match source {
        SecretSource::File(path) => load_file_source(name, path, danger_zone),
        SecretSource::Base64(data) => load_base64_source(name, data, encrypted, danger_zone),
        SecretSource::Env(var) => load_env_source(name, var),
    }
}

fn validate_secret_bytes(name: &str, bytes: &[u8]) -> Result<()> {
    if bytes.len() > MAX_SECRET_BYTES {
        return Err(ubiblk_error!(InvalidParameter {
            description: format!(
                "secrets.{name}: secret data exceeds maximum allowed size of {MAX_SECRET_BYTES} bytes"
            )
        }));
    }
    Ok(())
}

fn load_file_source(name: &str, path: &Path, danger_zone: &DangerZone) -> Result<Vec<u8>> {
    let file = File::open(path).map_err(|e| {
        ubiblk_error!(InvalidParameter {
            description: format!("secrets.{name}: failed to open '{path:?}': {e}")
        })
    })?;

    // Reject regular files unless danger_zone allows it.
    let metadata = file.metadata().map_err(|e| {
        ubiblk_error!(InvalidParameter {
            description: format!("secrets.{name}: failed to stat '{path:?}': {e}")
        })
    })?;

    if metadata.is_file() && !(danger_zone.enabled && danger_zone.allow_secret_over_regular_file) {
        return Err(ubiblk_error!(InvalidParameter {
            description: format!(
                "secrets.{name}: regular file cannot be used as source unless danger_zone.allow_secret_over_regular_file is enabled."
            )
        }));
    }

    let mut buf = Vec::new();
    file.take((MAX_SECRET_BYTES + 1) as u64)
        .read_to_end(&mut buf)
        .context(format!("secrets.{name}: failed to read '{path:?}'"))?;

    validate_secret_bytes(name, &buf)?;

    Ok(buf)
}

fn load_base64_source(
    name: &str,
    data: &str,
    encrypted: bool,
    danger_zone: &DangerZone,
) -> Result<Vec<u8>> {
    if !(encrypted || danger_zone.enabled && danger_zone.allow_inline_plaintext_secret) {
        return Err(ubiblk_error!(InvalidParameter {
            description: format!(
                "secrets.{name}: base64 secret source requires a KEK unless danger_zone.allow_inline_plaintext_secret is enabled"
            )
        }));
    }
    let bytes = b64_engine.decode(data).map_err(|e| {
        ubiblk_error!(InvalidParameter {
            description: format!("secrets.{name}: invalid base64: {e}")
        })
    })?;
    validate_secret_bytes(name, &bytes)?;
    Ok(bytes)
}

fn load_env_source(name: &str, var: &str) -> Result<Vec<u8>> {
    let value = std::env::var(var).map_err(|e| {
        ubiblk_error!(InvalidParameter {
            description: format!(
                "secrets.{name}: failed to read environment variable '{var}': {e}"
            )
        })
    })?;
    validate_secret_bytes(name, value.as_bytes())?;
    Ok(value.into_bytes())
}

#[cfg(test)]
mod tests {
    use std::io::Write;

    use super::*;
    use crate::crypt::aes256gcm_encrypt;
    use tempfile::{NamedTempFile, TempDir};

    fn default_danger_zone() -> DangerZone {
        DangerZone::default()
    }

    #[test]
    fn parse_secrets_returns_empty_when_missing() {
        let value = toml::from_str::<toml::Value>(
            r#"
           [disk]
           name = 'disk0'
           "#,
        )
        .unwrap();

        let parsed = parse_secrets(&value).unwrap();

        assert!(parsed.is_empty());
    }

    #[test]
    fn parse_secrets_from_toml_table() {
        let value = toml::from_str::<toml::Value>(
            r#"
            [secrets.kek]
            source.base64 = 'MDEyMzQ1Njc4OWFiY2RlZjAxMjM0NTY3ODlhYmNkZWY='
            [secrets.api]
            source.env = 'API_TOKEN'
            kek.ref = 'kek'
        "#,
        )
        .unwrap();

        let parsed = parse_secrets(&value).unwrap();

        assert_eq!(parsed.len(), 2);
        assert_eq!(
            parsed["kek"],
            SecretDef {
                source: SecretSource::Base64(
                    "MDEyMzQ1Njc4OWFiY2RlZjAxMjM0NTY3ODlhYmNkZWY=".to_string()
                ),
                kek: None,
            }
        );
        assert_eq!(
            parsed["api"],
            SecretDef {
                source: SecretSource::Env("API_TOKEN".to_string()),
                kek: Some(SecretRef::Ref("kek".to_string())),
            }
        );
    }

    #[test]
    fn parse_secrets_rejects_non_table() {
        let value = toml::from_str::<toml::Value>(
            r#"
            secrets = 'bad'
        "#,
        )
        .unwrap();

        let error = parse_secrets(&value).unwrap_err();
        let error_message = format!("{error}");
        assert!(error_message.contains("[secrets] must be a table"));
    }

    #[test]
    fn parse_secrets_rejects_unknown_fields() {
        let value = toml::from_str::<toml::Value>(
            r#"
            [secrets.db]
            source = { env = 'DB_PASSWORD' }
            extra = true
        "#,
        )
        .unwrap();

        let error = parse_secrets(&value).unwrap_err();
        let error_message = format!("{error}");

        assert!(error_message.contains("unknown field"));
    }

    #[test]
    fn resolve_secrets_rejects_base64_without_kek_by_default() {
        let defs = HashMap::from([(
            "plain".to_string(),
            SecretDef {
                source: SecretSource::Base64("aGVsbG8=".to_string()),
                kek: None,
            },
        )]);

        let result = resolve_secrets(&defs, &default_danger_zone());
        assert!(result.is_err());
        let error_message = format!("{}", result.unwrap_err());
        assert!(error_message.contains("base64 secret source requires a KEK"));
    }

    #[test]
    fn resolve_secrets_rejects_regular_file_without_danger_zone() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "top-secret").unwrap();

        let defs = HashMap::from([(
            "secret_file".to_string(),
            SecretDef {
                source: SecretSource::File(file.path().to_path_buf()),
                kek: None,
            },
        )]);

        let error = resolve_secrets(&defs, &default_danger_zone()).unwrap_err();
        let error_message = format!("{error}");

        assert!(error_message.contains("regular file cannot be used as source"));
    }

    #[test]
    fn resolve_secrets_reads_regular_file_when_explicitly_allowed() {
        let mut file = NamedTempFile::new().unwrap();
        write!(file, "top-secret").unwrap();

        let defs = HashMap::from([(
            "secret_file".to_string(),
            SecretDef {
                source: SecretSource::File(file.path().to_path_buf()),
                kek: None,
            },
        )]);

        let danger_zone = DangerZone {
            enabled: true,
            allow_secret_over_regular_file: true,
            ..DangerZone::default()
        };

        let resolved = resolve_secrets(&defs, &danger_zone).unwrap();

        assert_eq!(resolved["secret_file"].as_bytes(), b"top-secret");
    }

    #[test]
    fn resolve_secrets_handles_kek_decryption() {
        let kek = *b"0123456789abcdef0123456789abcdef";
        let secret_name = "db";
        let plaintext = b"very-secret-value";
        let encrypted = aes256gcm_encrypt(&kek, secret_name.as_bytes(), plaintext).unwrap();

        let dir = TempDir::new().unwrap();
        let fifo_path = dir.path().join("kek.pipe");
        let fifo_path_for_config = fifo_path.to_path_buf();
        nix::unistd::mkfifo(
            &fifo_path,
            nix::sys::stat::Mode::S_IRUSR | nix::sys::stat::Mode::S_IWUSR,
        )
        .unwrap();
        std::thread::spawn(move || {
            let mut fifo = File::create(&fifo_path).unwrap();
            fifo.write_all(&kek).unwrap();
        });

        let defs = HashMap::from([
            (
                "kek".to_string(),
                SecretDef {
                    source: SecretSource::File(fifo_path_for_config),
                    kek: None,
                },
            ),
            (
                secret_name.to_string(),
                SecretDef {
                    source: SecretSource::Base64(b64_engine.encode(encrypted)),
                    kek: Some(SecretRef::Ref("kek".to_string())),
                },
            ),
        ]);

        let result = resolve_secrets(&defs, &default_danger_zone());
        assert!(result.is_ok());

        let resolved = result.unwrap();
        assert_eq!(resolved[secret_name].as_bytes(), plaintext);
    }

    #[test]
    fn resolve_secrets_detects_circular_reference() {
        let defs = HashMap::from([
            (
                "a".to_string(),
                SecretDef {
                    source: SecretSource::Base64("YQ==".to_string()),
                    kek: Some(SecretRef::Ref("b".to_string())),
                },
            ),
            (
                "b".to_string(),
                SecretDef {
                    source: SecretSource::Base64("Yg==".to_string()),
                    kek: Some(SecretRef::Ref("a".to_string())),
                },
            ),
        ]);

        let error = resolve_secrets(&defs, &default_danger_zone()).unwrap_err();
        let error_message = format!("{error}");

        assert!(error_message.contains("circular secret references detected"));
    }

    #[test]
    fn resolve_secrets_rejects_missing_kek_reference() {
        let defs = HashMap::from([(
            "api".to_string(),
            SecretDef {
                source: SecretSource::Base64("aGVsbG8=".to_string()),
                kek: Some(SecretRef::Ref("missing".to_string())),
            },
        )]);

        let error = resolve_secrets(&defs, &default_danger_zone()).unwrap_err();
        let error_message = format!("{error}");

        assert!(error_message.contains("secrets.api: missing KEK reference 'missing'"));
    }

    #[test]
    fn resolve_secrets_rejects_oversize_secret() {
        let large_data = vec![b'a'; MAX_SECRET_BYTES + 1];
        let large_data_b64 = b64_engine.encode(&large_data);
        let defs = HashMap::from([(
            "big".to_string(),
            SecretDef {
                source: SecretSource::Base64(large_data_b64),
                kek: None,
            },
        )]);
        let danger_zone = DangerZone {
            enabled: true,
            allow_inline_plaintext_secret: true,
            ..DangerZone::default()
        };
        let error = resolve_secrets(&defs, &danger_zone).unwrap_err();
        let error_message = format!("{error}");
        assert!(error_message.contains("secret data exceeds maximum allowed size"));
    }

    #[test]
    fn resolve_secrets_rejects_self_kek_reference() {
        let defs = HashMap::from([(
            "self".to_string(),
            SecretDef {
                source: SecretSource::Base64("aGVsbG8=".to_string()),
                kek: Some(SecretRef::Ref("self".to_string())),
            },
        )]);
        let error = resolve_secrets(&defs, &default_danger_zone()).unwrap_err();
        let error_message = format!("{error}");
        assert!(error_message.contains("circular secret references detected"));
    }
}
