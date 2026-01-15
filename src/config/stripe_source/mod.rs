use serde::Deserialize;

pub mod archive;
pub mod raw;
pub mod remote;

pub use archive::{ArchiveStripeSourceConfig, AwsCredentials};
pub use raw::RawStripeSourceConfig;
pub use remote::RemoteStripeSourceConfig;

#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case", tag = "source")]
pub enum StripeSourceConfig {
    /// Use a raw image file as the stripe source.
    Raw {
        #[serde(flatten)]
        config: RawStripeSourceConfig,
    },

    /// Use a remote stripe server (identified by address or URL).
    Remote {
        #[serde(flatten)]
        config: RemoteStripeSourceConfig,
    },

    /// Use an archive store (e.g. directory or S3 bucket) as the stripe source.
    Archive {
        #[serde(flatten)]
        config: ArchiveStripeSourceConfig,
    },
}
