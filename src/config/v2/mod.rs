pub mod secrets;

use serde::Deserialize;

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
    pub allow_inline_plaintext_secret: bool,
    #[serde(default)]
    pub allow_secret_over_regular_file: bool,
    #[serde(default)]
    pub allow_unencrypted_connection: bool,
}
