use serde::de::DeserializeOwned;
use std::{collections::HashMap, path::Path};

use super::{tuning::TuningSection, Config, DeviceSection, EncryptionSection};
use crate::{
    config::v2::{
        includes::resolve_includes,
        secrets::{parse_secrets, resolve_secrets, ResolvedSecret},
        stripe_source::{ArchiveStorageConfig, RemoteStripeConfig, StripeSourceConfig},
        ArchiveTargetConfig, DangerZone, RemoteStripeServerConfig,
    },
    ubiblk_error, Result, ResultExt,
};

impl Config {
    pub fn load(path: &Path) -> Result<Self> {
        let root = load_root_toml(path, "Loading config failed")?;
        let config_dir = path.parent().unwrap_or_else(|| Path::new("."));
        Self::load_from_value(root, config_dir)
    }

    fn load_from_value(root: toml::Value, config_dir: &Path) -> Result<Self> {
        let merged = load_merged(root, config_dir, &Self::allowed_top_level_keys())?;
        let common = load_common(&merged)?;

        let device: DeviceSection = parse_required_section(&merged, "device")?;

        let tuning: TuningSection = parse_optional_section(&merged, "tuning")?.unwrap_or_default();
        tuning.validate()?;

        let encryption: Option<EncryptionSection> = parse_optional_section(&merged, "encryption")?;
        let stripe_source: Option<StripeSourceConfig> =
            parse_optional_section(&merged, "stripe_source")?;

        if let Some(stripe_source) = &stripe_source {
            stripe_source.validate(&common.danger_zone, &common.secrets)?;
        }

        if let Some(encryption) = &encryption {
            encryption.validate_secrets(&common.secrets)?;
        } else if !(common.danger_zone.enabled && common.danger_zone.allow_unencrypted_disk) {
            return Err(ubiblk_error!(InvalidParameter {
                description: "Disk encryption is required unless danger_zone.allow_unencrypted_disk is enabled".to_string(),
            }));
        }

        Ok(Config {
            device,
            tuning,
            encryption,
            danger_zone: common.danger_zone,
            stripe_source,
            secrets: common.secrets,
        })
    }

    fn allowed_top_level_keys() -> [&'static str; 6] {
        [
            "device",
            "tuning",
            "encryption",
            "danger_zone",
            "stripe_source",
            "secrets",
        ]
    }
}

impl ArchiveTargetConfig {
    pub fn load(path: &Path) -> Result<Self> {
        let root = load_root_toml(path, "Loading target config failed")?;
        let config_dir = path.parent().unwrap_or_else(|| Path::new("."));
        Self::load_from_value(root, config_dir)
    }

    fn load_from_value(value: toml::Value, config_dir: &Path) -> Result<Self> {
        let merged = load_merged(value, config_dir, &Self::allowed_top_level_keys())?;
        let common = load_common(&merged)?;

        let target: ArchiveStorageConfig = parse_required_section(&merged, "target")?;
        target.validate(&common.secrets)?;

        Ok(ArchiveTargetConfig {
            target,
            danger_zone: common.danger_zone,
            secrets: common.secrets,
        })
    }

    fn allowed_top_level_keys() -> [&'static str; 3] {
        ["target", "danger_zone", "secrets"]
    }
}

impl RemoteStripeServerConfig {
    pub fn load(path: &Path) -> Result<Self> {
        let root = load_root_toml(path, "Loading listen config failed")?;
        let config_dir = path.parent().unwrap_or_else(|| Path::new("."));
        Self::load_from_value(root, config_dir)
    }

    fn load_from_value(value: toml::Value, config_dir: &Path) -> Result<Self> {
        let merged = load_merged(value, config_dir, &Self::allowed_top_level_keys())?;
        let common = load_common(&merged)?;

        let server: RemoteStripeConfig = parse_required_section(&merged, "server")?;
        server.validate(&common.danger_zone, &common.secrets)?;

        Ok(RemoteStripeServerConfig {
            server,
            danger_zone: common.danger_zone,
            secrets: common.secrets,
        })
    }

    fn allowed_top_level_keys() -> [&'static str; 3] {
        ["server", "danger_zone", "secrets"]
    }
}

impl EncryptionSection {
    fn validate_secrets(&self, secret_defs: &HashMap<String, ResolvedSecret>) -> Result<()> {
        let xts_key_id = self.xts_key.id();
        let xts_key = secret_defs.get(xts_key_id).ok_or_else(|| {
            ubiblk_error!(InvalidParameter {
                description: format!(
                    "Encryption xts_key reference '{}' not found in configuration",
                    xts_key_id
                ),
            })
        })?;
        if xts_key.as_bytes().len() != 64 {
            return Err(ubiblk_error!(InvalidParameter {
                description: format!(
                    "Encryption xts_key '{}' must be exactly 64 bytes (got {} bytes)",
                    xts_key_id,
                    xts_key.as_bytes().len()
                ),
            }));
        }
        Ok(())
    }
}

struct CommonResolvedConfig {
    danger_zone: DangerZone,
    secrets: HashMap<String, ResolvedSecret>,
}

fn load_root_toml(path: &Path, error_context: &str) -> Result<toml::Value> {
    let content = std::fs::read_to_string(path).context(error_context.to_string())?;
    warn_if_loose_permissions(path);
    toml::from_str(&content).map_err(|e| {
        ubiblk_error!(InvalidParameter {
            description: format!("Failed to parse TOML config: {}", e),
        })
    })
}

#[cfg(unix)]
fn warn_if_loose_permissions(path: &Path) {
    if let Some(mode) = get_file_mode(path) {
        if mode & 0o077 != 0 {
            log::warn!(
                "config file '{}' is accessible to other users (mode {:04o}); consider restricting to 0600",
                path.display(),
                mode & 0o7777
            );
        }
    }
}

#[cfg(unix)]
fn get_file_mode(path: &Path) -> Option<u32> {
    use std::os::unix::fs::PermissionsExt;
    std::fs::metadata(path).ok().map(|m| m.permissions().mode())
}

#[cfg(not(unix))]
fn warn_if_loose_permissions(_path: &Path) {}

fn load_merged(root: toml::Value, config_dir: &Path, allowed_keys: &[&str]) -> Result<toml::Value> {
    let merged = resolve_includes(root, config_dir)?;
    validate_top_level_keys(&merged, allowed_keys)?;
    Ok(merged)
}

fn load_common(merged: &toml::Value) -> Result<CommonResolvedConfig> {
    let danger_zone: DangerZone =
        parse_optional_section(merged, "danger_zone")?.unwrap_or_default();
    danger_zone.warn_ignored_flags();
    let secret_defs = parse_secrets(merged)?;
    let secrets = resolve_secrets(&secret_defs, &danger_zone)?;
    Ok(CommonResolvedConfig {
        danger_zone,
        secrets,
    })
}

fn parse_required_section<T: DeserializeOwned>(merged: &toml::Value, key: &str) -> Result<T> {
    let value = merged.get(key).ok_or_else(|| {
        ubiblk_error!(InvalidParameter {
            description: format!("Missing required [{}] section", key),
        })
    })?;
    value.clone().try_into().map_err(|e| {
        ubiblk_error!(InvalidParameter {
            description: format!("Failed to parse {} section: {}", key, e),
        })
    })
}

fn parse_optional_section<T: DeserializeOwned>(
    merged: &toml::Value,
    key: &str,
) -> Result<Option<T>> {
    merged
        .get(key)
        .map(|value| {
            value.clone().try_into().map_err(|e| {
                ubiblk_error!(InvalidParameter {
                    description: format!("Failed to parse {} section: {}", key, e),
                })
            })
        })
        .transpose()
}

fn validate_top_level_keys(root: &toml::Value, allowed_keys: &[&str]) -> Result<()> {
    let table = root.as_table().ok_or_else(|| {
        ubiblk_error!(InvalidParameter {
            description: "Top-level config must be a table".to_string(),
        })
    })?;
    for key in table.keys() {
        if !allowed_keys.contains(&key.as_str()) {
            return Err(ubiblk_error!(InvalidParameter {
                description: format!("Unknown top-level config key '{}'", key),
            }));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_config(toml: &str) -> Result<Config> {
        let value: toml::Value = toml::from_str(toml).unwrap();
        Config::load_from_value(value, Path::new("."))
    }

    #[test]
    fn loads_valid_config() {
        std::env::set_var(
            "XTS_KEY",
            "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
        );
        let toml = r#"
            [device]
            data_path = "/dev/ubiblk0"
            [tuning]
            num_queues = 2
            cpus = [0, 1]
            poll_timeout_us = 5000
            [encryption]
            xts_key.ref = "my_xts_key"
            [secrets.my_xts_key]
            source.env = "XTS_KEY"
            [danger_zone]
            enabled = true
            allow_env_secrets = true
        "#;
        let config = parse_config(toml).expect("Failed to load config");
        assert_eq!(config.device.data_path, Path::new("/dev/ubiblk0"));
        assert_eq!(config.tuning.num_queues, 2);
        assert_eq!(config.tuning.cpus, Some(vec![0, 1]));
        assert_eq!(config.tuning.poll_timeout_us, 5000);
        assert!(config.encryption.is_some());
        assert_eq!(config.secrets.len(), 1);
        assert!(config.secrets.contains_key("my_xts_key"));
    }

    #[test]
    fn rejects_missing_device_section() {
        let toml = r#"
            [tuning]
            num_queues = 2
        "#;
        let result = parse_config(toml);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("Missing required [device] section"));
    }

    #[test]
    fn rejects_invalid_secret_reference() {
        let toml = r#"
            [device]
            data_path = "/dev/ubiblk0"
            [encryption]
            xts_key.ref = "nonexistent_key"
        "#;
        let result = parse_config(toml);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg
            .contains("Encryption xts_key reference 'nonexistent_key' not found in configuration"));
    }

    #[test]
    fn rejects_invalid_xts_key_length() {
        std::env::set_var("SHORT_KEY", "short");
        let toml = r#"
            [device]
            data_path = "/dev/ubiblk0"
            [encryption]
            xts_key.ref = "short_key"
            [secrets.short_key]
            source.env = "SHORT_KEY"
            [danger_zone]
            enabled = true
            allow_env_secrets = true
        "#;
        let result = parse_config(toml);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("Encryption xts_key 'short_key' must be exactly 64 bytes"));
    }

    #[test]
    fn rejects_unencrypted_disk_without_danger_zone() {
        let toml = r#"
            [device]
            data_path = "/dev/ubiblk0"
        "#;
        let result = parse_config(toml);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains(
            "Disk encryption is required unless danger_zone.allow_unencrypted_disk is enabled"
        ));
    }

    #[test]
    fn allows_unencrypted_disk_with_danger_zone() {
        let toml = r#"
            [device]
            data_path = "/dev/ubiblk0"
            [danger_zone]
            enabled = true
            allow_unencrypted_disk = true
        "#;
        let config = parse_config(toml).expect("Failed to load config");
        assert_eq!(config.device.data_path, Path::new("/dev/ubiblk0"));
        assert!(config.encryption.is_none());
    }

    #[test]
    fn rejects_unencrypted_connection_without_danger_zone() {
        let toml = r#"
            [device]
            data_path = "/dev/ubiblk0"
            [stripe_source]
            type = "remote"
            address = "127.0.0.1:1234"
        "#;
        let result = parse_config(toml);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("Remote stripe source requires PSK unless danger_zone.allow_unencrypted_connection is enabled"));
    }

    #[test]
    fn rejects_invalid_stripe_source_config() {
        let toml = r#"
            [device]
            data_path = "/dev/ubiblk0"
            [stripe_source]
            type = "invalid_type"
            address = "127.0.0.1:1234"
        "#;
        let result = parse_config(toml);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg
            .contains("Failed to parse stripe_source section: unknown variant `invalid_type`"));
    }

    #[test]
    fn rejects_unknown_fields_in_device_section() {
        let toml = r#"
            [device]
            data_path = "/dev/ubiblk0"
            unknown_field = "value"
        "#;
        let result = parse_config(toml);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("Failed to parse device section: unknown field `unknown_field`"));
    }

    #[test]
    fn rejects_unknown_sections() {
        let toml = r#"
            [device]
            data_path = "/dev/ubiblk0"
            [unknown_section]
            key = "value"
            [danger_zone]
            enabled = true
            allow_unencrypted_disk = true
        "#;
        let result = parse_config(toml);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("Unknown top-level config key 'unknown_section'"));
    }

    #[test]
    fn rejects_invalid_tuning_config() {
        let toml = r#"
            [device]
            data_path = "/dev/ubiblk0"
            [tuning]
            num_queues = 0
            [danger_zone]
            enabled = true
            allow_unencrypted_disk = true
        "#;
        let result = parse_config(toml);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("num_queues 0 is out of range (must be 1..=63)"));
    }

    #[test]
    fn loads_valid_target_config() {
        std::env::set_var(
            "LOADS_VALID_TARGET_CONFIG_ARCHIVE_KEK",
            "0123456789abcdef0123456789abcdef",
        );
        let toml = r#"
[target]
storage = "filesystem"
path = "/backups/archive1"
archive_kek.ref = "my_archive_kek"
[secrets.my_archive_kek]
source.env = "LOADS_VALID_TARGET_CONFIG_ARCHIVE_KEK"
[danger_zone]
enabled = true
allow_env_secrets = true
        "#;
        let value: toml::Value = toml::from_str(toml).unwrap();
        let result = ArchiveTargetConfig::load_from_value(value, Path::new("."));
        assert!(result.is_ok());
        let config = result.unwrap();
        assert!(matches!(config.target, ArchiveStorageConfig::Filesystem {
            path, archive_kek, ..
        } if path == Path::new("/backups/archive1") && archive_kek.id() == "my_archive_kek"));
        assert_eq!(config.secrets.len(), 1);
    }

    #[test]
    fn loads_valid_remote_stripe_server_config() {
        std::env::set_var(
            "LOADS_VALID_REMOTE_SERVER_CONFIG_PSK",
            "0123456789abcdef0123456789abcdef",
        );

        let toml = r#"
[server]
address = "127.0.0.1:3322"
psk.identity = "node-a"
psk.secret.ref = "my_psk"
[secrets.my_psk]
source.env = "LOADS_VALID_REMOTE_SERVER_CONFIG_PSK"
[danger_zone]
enabled = true
allow_env_secrets = true
        "#;

        let value: toml::Value = toml::from_str(toml).unwrap();
        let config = RemoteStripeServerConfig::load_from_value(value, Path::new("."))
            .expect("remote stripe server config should load");

        assert_eq!(config.server.address, "127.0.0.1:3322");
        assert_eq!(config.server.psk.as_ref().unwrap().identity, "node-a");
        assert_eq!(config.secrets.len(), 1);
    }

    #[test]
    #[cfg(unix)]
    fn warns_on_loose_config_permissions() {
        use std::io::Write;
        use std::os::unix::fs::PermissionsExt;

        let dir = std::env::temp_dir().join("ubiblk-test-perms");
        let _ = std::fs::create_dir_all(&dir);

        // File with 0644 should be detected as loose
        let loose_path = dir.join("loose.toml");
        let mut f = std::fs::File::create(&loose_path).unwrap();
        f.write_all(b"[device]\ndata_path = \"/dev/x\"\n").unwrap();
        std::fs::set_permissions(&loose_path, std::fs::Permissions::from_mode(0o644)).unwrap();

        let mode = get_file_mode(&loose_path).unwrap();
        assert_ne!(
            mode & 0o077,
            0,
            "0644 file should have group/other bits set"
        );

        // File with 0600 should not be flagged
        let tight_path = dir.join("tight.toml");
        let mut f = std::fs::File::create(&tight_path).unwrap();
        f.write_all(b"[device]\ndata_path = \"/dev/x\"\n").unwrap();
        std::fs::set_permissions(&tight_path, std::fs::Permissions::from_mode(0o600)).unwrap();

        let mode = get_file_mode(&tight_path).unwrap();
        assert_eq!(mode & 0o077, 0, "0600 file should have no group/other bits");

        // load_root_toml should succeed (warning only, not error) even with loose perms
        let result = load_root_toml(&loose_path, "test");
        assert!(result.is_ok(), "loose permissions should warn, not error");

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn rejects_remote_stripe_server_config_without_psk() {
        let toml = r#"
[server]
address = "127.0.0.1:3322"
        "#;
        let value: toml::Value = toml::from_str(toml).unwrap();
        let result = RemoteStripeServerConfig::load_from_value(value, Path::new("."));
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("Remote stripe source requires PSK unless danger_zone.allow_unencrypted_connection is enabled"));
    }
}
