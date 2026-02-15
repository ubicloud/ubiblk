pub mod includes;
pub mod load;
pub mod secrets;
pub mod stripe_source;
pub mod tuning;

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
