use std::fs::{self, File, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};

use base64::{engine::general_purpose::STANDARD, Engine};
use log::info;

use crate::crypt::KeyEncryptionCipher;
use crate::Result;

/// Atomically updates rekey-related fields in a YAML config file.
///
/// Uses the write-temp -> fsync -> rename -> fsync-parent pattern to ensure
/// crash safety. Only modifies rekey-specific fields (`encryption_key`,
/// `pending_encryption_key`, `rekey_state`, `rekey_progress`), preserving
/// all other fields exactly as they appear in the original file.
pub struct ConfigUpdater {
    config_path: PathBuf,
    kek: KeyEncryptionCipher,
}

impl ConfigUpdater {
    pub fn new(config_path: PathBuf, kek: KeyEncryptionCipher) -> Self {
        Self { config_path, kek }
    }

    /// Write the initial rekey state: store both old and new keys, set state to in_progress.
    pub fn start_rekey(
        &self,
        old_key: (&[u8; 32], &[u8; 32]),
        new_key: (&[u8; 32], &[u8; 32]),
    ) -> Result<()> {
        let mut doc = self.load_yaml()?;

        let (enc_new1, enc_new2) = self.kek.encrypt_xts_keys(new_key.0, new_key.1)?;
        self.set_key_pair(&mut doc, "pending_encryption_key", &enc_new1, &enc_new2);
        self.set_scalar(&mut doc, "rekey_state", "in_progress");
        self.set_number(&mut doc, "rekey_progress", 0);

        // Ensure encryption_key still has the old key (re-encrypt it in case KEK changed)
        let (enc_old1, enc_old2) = self.kek.encrypt_xts_keys(old_key.0, old_key.1)?;
        self.set_key_pair(&mut doc, "encryption_key", &enc_old1, &enc_old2);

        self.atomic_write(&doc)
    }

    /// Update progress after completing a stripe.
    pub fn update_progress(&self, stripe_index: u64) -> Result<()> {
        let mut doc = self.load_yaml()?;
        self.set_number(&mut doc, "rekey_progress", stripe_index);
        self.atomic_write(&doc)
    }

    /// Finalize rekey: move pending key to encryption_key, remove rekey fields.
    pub fn complete_rekey(&self, new_key: (&[u8; 32], &[u8; 32])) -> Result<()> {
        let mut doc = self.load_yaml()?;

        let (enc1, enc2) = self.kek.encrypt_xts_keys(new_key.0, new_key.1)?;
        self.set_key_pair(&mut doc, "encryption_key", &enc1, &enc2);

        // Remove rekey-specific fields
        self.remove_key(&mut doc, "pending_encryption_key");
        self.remove_key(&mut doc, "rekey_state");
        self.remove_key(&mut doc, "rekey_progress");

        self.atomic_write(&doc)
    }

    fn load_yaml(&self) -> Result<serde_yaml::Value> {
        let contents = fs::read_to_string(&self.config_path).map_err(|e| {
            crate::ubiblk_error!(InvalidParameter {
                description: format!(
                    "Failed to read config file {}: {}",
                    self.config_path.display(),
                    e
                ),
            })
        })?;
        serde_yaml::from_str(&contents).map_err(|e| {
            crate::ubiblk_error!(InvalidParameter {
                description: format!("Failed to parse config YAML: {}", e),
            })
        })
    }

    fn set_key_pair(
        &self,
        doc: &mut serde_yaml::Value,
        field: &str,
        enc_key1: &[u8],
        enc_key2: &[u8],
    ) {
        let map = doc.as_mapping_mut().expect("config must be a YAML mapping");
        let key = serde_yaml::Value::String(field.to_string());
        let val = serde_yaml::Value::Sequence(vec![
            serde_yaml::Value::String(STANDARD.encode(enc_key1)),
            serde_yaml::Value::String(STANDARD.encode(enc_key2)),
        ]);
        // Insert or replace
        if let Some(existing) = map.get_mut(&key) {
            *existing = val;
        } else {
            map.insert(key, val);
        }
    }

    fn set_scalar(&self, doc: &mut serde_yaml::Value, field: &str, value: &str) {
        let map = doc.as_mapping_mut().expect("config must be a YAML mapping");
        let key = serde_yaml::Value::String(field.to_string());
        let val = serde_yaml::Value::String(value.to_string());
        if let Some(existing) = map.get_mut(&key) {
            *existing = val;
        } else {
            map.insert(key, val);
        }
    }

    fn set_number(&self, doc: &mut serde_yaml::Value, field: &str, value: u64) {
        let map = doc.as_mapping_mut().expect("config must be a YAML mapping");
        let key = serde_yaml::Value::String(field.to_string());
        let val = serde_yaml::Value::Number(serde_yaml::Number::from(value));
        if let Some(existing) = map.get_mut(&key) {
            *existing = val;
        } else {
            map.insert(key, val);
        }
    }

    fn remove_key(&self, doc: &mut serde_yaml::Value, field: &str) {
        let map = doc.as_mapping_mut().expect("config must be a YAML mapping");
        let key = serde_yaml::Value::String(field.to_string());
        map.remove(&key);
    }

    /// Atomic write: write to temp file, fsync, rename over original, fsync parent dir.
    fn atomic_write(&self, doc: &serde_yaml::Value) -> Result<()> {
        let yaml_str = serde_yaml::to_string(doc).map_err(|e| {
            crate::ubiblk_error!(InvalidParameter {
                description: format!("Failed to serialize config YAML: {}", e),
            })
        })?;

        let parent = self.config_path.parent().unwrap_or(Path::new("."));
        let temp_path = self.config_path.with_extension("tmp");

        // Write to temp file
        let mut temp_file = OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .open(&temp_path)?;
        temp_file.write_all(yaml_str.as_bytes())?;
        temp_file.sync_all()?;
        drop(temp_file);

        // Rename over original (atomic on POSIX)
        fs::rename(&temp_path, &self.config_path)?;

        // Fsync parent directory to ensure the rename is durable
        let dir = File::open(parent)?;
        dir.sync_all()?;

        info!("Config updated atomically: {}", self.config_path.display());
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::crypt::CipherMethod;
    use tempfile::TempDir;

    fn write_config(dir: &Path, content: &str) -> PathBuf {
        let path = dir.join("config.yaml");
        fs::write(&path, content).unwrap();
        path
    }

    fn default_kek() -> KeyEncryptionCipher {
        KeyEncryptionCipher {
            method: CipherMethod::None,
            key: None,
            auth_data: None,
        }
    }

    #[test]
    fn test_start_rekey_adds_pending_key() {
        let dir = TempDir::new().unwrap();
        let path = write_config(
            dir.path(),
            r#"
path: /dev/sda
encryption_key:
  - "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA="
  - "AQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQE="
"#,
        );
        let updater = ConfigUpdater::new(path.clone(), default_kek());
        let old_key1 = [0u8; 32];
        let old_key2 = [1u8; 32];
        let new_key1 = [2u8; 32];
        let new_key2 = [3u8; 32];

        updater
            .start_rekey((&old_key1, &old_key2), (&new_key1, &new_key2))
            .unwrap();

        let contents = fs::read_to_string(&path).unwrap();
        assert!(contents.contains("pending_encryption_key"));
        assert!(contents.contains("rekey_state"));
        assert!(contents.contains("in_progress"));
        assert!(contents.contains("rekey_progress"));

        // Verify the pending key can be decoded
        let doc: serde_yaml::Value = serde_yaml::from_str(&contents).unwrap();
        let pending = doc.get("pending_encryption_key").unwrap();
        let seq = pending.as_sequence().unwrap();
        let decoded1 = STANDARD.decode(seq[0].as_str().unwrap()).unwrap();
        assert_eq!(decoded1, new_key1.to_vec());
    }

    #[test]
    fn test_update_progress() {
        let dir = TempDir::new().unwrap();
        let path = write_config(
            dir.path(),
            r#"
path: /dev/sda
rekey_state: in_progress
rekey_progress: 0
"#,
        );
        let updater = ConfigUpdater::new(path.clone(), default_kek());
        updater.update_progress(42).unwrap();

        let contents = fs::read_to_string(&path).unwrap();
        assert!(contents.contains("42"));
    }

    #[test]
    fn test_complete_rekey_removes_pending_fields() {
        let dir = TempDir::new().unwrap();
        let path = write_config(
            dir.path(),
            r#"
path: /dev/sda
encryption_key:
  - "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA="
  - "AQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQE="
pending_encryption_key:
  - "AgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgI="
  - "AwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwM="
rekey_state: in_progress
rekey_progress: "100"
"#,
        );
        let updater = ConfigUpdater::new(path.clone(), default_kek());
        let new_key1 = [2u8; 32];
        let new_key2 = [3u8; 32];

        updater.complete_rekey((&new_key1, &new_key2)).unwrap();

        let contents = fs::read_to_string(&path).unwrap();
        assert!(!contents.contains("pending_encryption_key"));
        assert!(!contents.contains("rekey_state"));
        assert!(!contents.contains("rekey_progress"));
        assert!(contents.contains("encryption_key"));
        // Verify encryption_key is now the new key
        let doc: serde_yaml::Value = serde_yaml::from_str(&contents).unwrap();
        let enc = doc.get("encryption_key").unwrap();
        let seq = enc.as_sequence().unwrap();
        let decoded1 = STANDARD.decode(seq[0].as_str().unwrap()).unwrap();
        assert_eq!(decoded1, new_key1.to_vec());
    }

    #[test]
    fn test_preserves_unrelated_fields() {
        let dir = TempDir::new().unwrap();
        let path = write_config(
            dir.path(),
            r#"
path: /dev/sda
socket: /tmp/test.sock
num_queues: 4
device_id: mydev
encryption_key:
  - "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA="
  - "AQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQE="
"#,
        );
        let updater = ConfigUpdater::new(path.clone(), default_kek());
        let old_key1 = [0u8; 32];
        let old_key2 = [1u8; 32];
        let new_key1 = [2u8; 32];
        let new_key2 = [3u8; 32];

        updater
            .start_rekey((&old_key1, &old_key2), (&new_key1, &new_key2))
            .unwrap();

        let contents = fs::read_to_string(&path).unwrap();
        assert!(contents.contains("path: /dev/sda"));
        assert!(contents.contains("socket: /tmp/test.sock"));
        assert!(contents.contains("num_queues: 4") || contents.contains("num_queues: '4'"));
        assert!(contents.contains("device_id: mydev"));
    }
}
