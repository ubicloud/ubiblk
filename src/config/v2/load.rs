use std::{collections::HashMap, path::Path};

use super::{tuning::TuningSection, Config, DeviceSection, EncryptionSection};
use crate::{
    config::v2::{
        includes::resolve_includes,
        secrets::{parse_secrets, resolve_secrets, ResolvedSecret},
        stripe_source::StripeSourceConfig,
        DangerZone,
    },
    ubiblk_error, Result, ResultExt,
};

impl Config {
    pub fn load(path: &Path) -> Result<Self> {
        let content = std::fs::read_to_string(path).context("Loading config failed".to_string())?;

        let root: toml::Value = toml::from_str(&content).map_err(|e| {
            ubiblk_error!(InvalidParameter {
                description: format!("Failed to parse TOML config: {}", e),
            })
        })?;

        let config_dir = path.parent().unwrap_or_else(|| Path::new("."));

        Self::load_from_value(root, config_dir)
    }

    fn load_from_value(root: toml::Value, config_dir: &Path) -> Result<Self> {
        let merged = resolve_includes(root, config_dir)?;
        Self::validate_top_level_keys(&merged)?;

        let danger_zone: DangerZone = match merged.get("danger_zone") {
            Some(value) => value.clone().try_into().map_err(|e| {
                ubiblk_error!(InvalidParameter {
                    description: format!("Failed to parse danger_zone section: {}", e),
                })
            })?,
            None => DangerZone::default(),
        };

        let device: DeviceSection = match merged.get("device") {
            Some(value) => value.clone().try_into().map_err(|e| {
                ubiblk_error!(InvalidParameter {
                    description: format!("Failed to parse device section: {}", e),
                })
            })?,
            None => {
                return Err(ubiblk_error!(InvalidParameter {
                    description: "Missing required [device] section".to_string(),
                }))
            }
        };

        let tuning: TuningSection = match merged.get("tuning") {
            Some(value) => value.clone().try_into().map_err(|e| {
                ubiblk_error!(InvalidParameter {
                    description: format!("Failed to parse tuning section: {}", e),
                })
            })?,
            None => TuningSection::default(),
        };
        tuning.validate()?;

        let encryption: Option<EncryptionSection> = match merged.get("encryption") {
            Some(value) => Some(value.clone().try_into().map_err(|e| {
                ubiblk_error!(InvalidParameter {
                    description: format!("Failed to parse encryption section: {}", e),
                })
            })?),
            None => None,
        };

        let stripe_source: Option<StripeSourceConfig> = match merged.get("stripe_source") {
            Some(value) => Some(value.clone().try_into().map_err(|e| {
                ubiblk_error!(InvalidParameter {
                    description: format!("Failed to parse stripe_source section: {}", e),
                })
            })?),
            None => None,
        };

        let secret_defs = parse_secrets(&merged)?;
        let resolved_secrets = resolve_secrets(&secret_defs, &danger_zone)?;

        if let Some(stripe_source) = &stripe_source {
            stripe_source.validate(&danger_zone)?;
            stripe_source.validate_secrets(&resolved_secrets)?;
        }

        if let Some(encryption) = &encryption {
            encryption.validate_secrets(&resolved_secrets)?;
        } else if !(danger_zone.enabled && danger_zone.allow_unencrypted_disk) {
            return Err(ubiblk_error!(InvalidParameter {
                description: "Disk encryption is required unless danger_zone.allow_unencrypted_disk is enabled".to_string(),
            }));
        }

        Ok(Config {
            device,
            tuning,
            encryption,
            danger_zone,
            stripe_source,
            secrets: resolved_secrets,
        })
    }

    fn validate_top_level_keys(root: &toml::Value) -> Result<()> {
        let allowed_keys = [
            "device",
            "tuning",
            "encryption",
            "danger_zone",
            "stripe_source",
            "secrets",
        ];
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
        println!("result: {:?}", result);
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
}
