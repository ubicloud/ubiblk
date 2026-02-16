pub mod includes;
pub mod load;
pub mod secrets;
pub mod stripe_source;
pub mod tuning;

use log::warn;
use serde::Deserialize;
use std::{collections::HashMap, path::PathBuf};

use crate::config::v2::{
    secrets::SecretRef,
    stripe_source::{ArchiveStorageConfig, RemoteStripeConfig},
};

pub const MAX_NUM_QUEUES: usize = 63;

/// Fully resolved configuration loaded from TOML files.
///
/// All secret references have been resolved to byte values, and all
/// validation checks have passed.
#[derive(Debug, Clone)]
pub struct Config {
    pub device: DeviceSection,
    pub tuning: tuning::TuningSection,
    pub encryption: Option<EncryptionSection>,
    pub danger_zone: DangerZone,
    pub stripe_source: Option<stripe_source::StripeSourceConfig>,

    /// Resolved secret values keyed by name.
    pub secrets: HashMap<String, secrets::ResolvedSecret>,
}

#[derive(Debug, Clone)]
pub struct ArchiveTargetConfig {
    pub target: ArchiveStorageConfig,
    pub danger_zone: DangerZone,

    // Resolved secret values keyed by name.
    pub secrets: HashMap<String, secrets::ResolvedSecret>,
}

#[derive(Debug, Clone)]
pub struct RemoteStripeServerConfig {
    pub server: RemoteStripeConfig,
    pub danger_zone: DangerZone,

    // Resolved secret values keyed by name.
    pub secrets: HashMap<String, secrets::ResolvedSecret>,
}

/// Safety overrides that must be explicitly opted into.
///
/// The `enabled` flag must be `true` for any individual bypass to take effect.
/// This two-step mechanism prevents accidental insecure configurations.
#[derive(Debug, Clone, Deserialize, PartialEq, Default)]
#[serde(deny_unknown_fields)]
pub struct DangerZone {
    #[serde(default)]
    pub enabled: bool,
    #[serde(default)]
    pub allow_unencrypted_disk: bool,
    #[serde(default)]
    pub allow_inline_plaintext_secrets: bool,
    #[serde(default)]
    pub allow_secret_over_regular_file: bool,
    #[serde(default)]
    pub allow_unencrypted_connection: bool,
}

impl DangerZone {
    /// Returns the names of `allow_*` flags that are set to `true` but ignored
    /// because `enabled` is `false`.
    pub fn ignored_flags(&self) -> Vec<&'static str> {
        if self.enabled {
            return Vec::new();
        }
        let mut flags = Vec::new();
        if self.allow_unencrypted_disk {
            flags.push("allow_unencrypted_disk");
        }
        if self.allow_inline_plaintext_secrets {
            flags.push("allow_inline_plaintext_secrets");
        }
        if self.allow_secret_over_regular_file {
            flags.push("allow_secret_over_regular_file");
        }
        if self.allow_unencrypted_connection {
            flags.push("allow_unencrypted_connection");
        }
        flags
    }

    /// Logs a warning if any `allow_*` flags are set but `enabled` is `false`.
    pub fn warn_ignored_flags(&self) {
        let ignored = self.ignored_flags();
        if !ignored.is_empty() {
            warn!(
                "danger_zone has flags set but enabled = false; ignored flags: {}",
                ignored.join(", ")
            );
        }
    }
}

/// Core device paths and identity.
#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct DeviceSection {
    pub data_path: PathBuf,
    pub metadata_path: Option<PathBuf>,
    pub vhost_socket: Option<PathBuf>,
    pub rpc_socket: Option<PathBuf>,
    #[serde(default = "default_device_id")]
    pub device_id: String,
    #[serde(default)]
    pub track_written: bool,
}

fn default_device_id() -> String {
    "ubiblk".to_string()
}

/// Encryption settings. The `xts_key` field uses a `ref` sub-key
/// (e.g. `xts_key.ref = "key-name"`) that is resolved by the secret module.
#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct EncryptionSection {
    pub xts_key: SecretRef,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ignored_flags_empty_when_all_defaults() {
        let dz = DangerZone::default();
        assert!(dz.ignored_flags().is_empty());
    }

    #[test]
    fn ignored_flags_empty_when_enabled() {
        let dz = DangerZone {
            enabled: true,
            allow_unencrypted_disk: true,
            allow_unencrypted_connection: true,
            ..DangerZone::default()
        };
        assert!(dz.ignored_flags().is_empty());
    }

    #[test]
    fn ignored_flags_lists_set_flags_when_not_enabled() {
        let dz = DangerZone {
            enabled: false,
            allow_unencrypted_disk: true,
            allow_inline_plaintext_secrets: true,
            ..DangerZone::default()
        };
        let flags = dz.ignored_flags();
        assert_eq!(
            flags,
            vec!["allow_unencrypted_disk", "allow_inline_plaintext_secrets"]
        );
    }

    #[test]
    fn ignored_flags_lists_all_flags_when_all_set_without_enabled() {
        let dz = DangerZone {
            enabled: false,
            allow_unencrypted_disk: true,
            allow_inline_plaintext_secrets: true,
            allow_secret_over_regular_file: true,
            allow_unencrypted_connection: true,
        };
        let flags = dz.ignored_flags();
        assert_eq!(flags.len(), 4);
        assert!(flags.contains(&"allow_unencrypted_disk"));
        assert!(flags.contains(&"allow_inline_plaintext_secrets"));
        assert!(flags.contains(&"allow_secret_over_regular_file"));
        assert!(flags.contains(&"allow_unencrypted_connection"));
    }
}
