use serde::Deserialize;
use std::{collections::HashMap, path::Path};

use super::{
    load::resolve_path,
    secrets::ResolvedSecret,
    stripe_source::ArchiveStorageConfig,
    tuning::{IoEngine, TuningSection},
    DeviceSection,
};
use crate::{ubiblk_error, Result};

/// Most stripes a spill device tracks. Each costs a few dozen bytes of memory
/// whether or not it is ever used.
pub const MAX_SPILL_STRIPES: u64 = 1 << 24;

/// Most memory the transfer buffers may take together.
pub const MAX_SPILL_TRANSFER_BYTES: u64 = 1 << 30;

/// A device larger than its local disk, with evicted stripes in an object
/// store.
#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct SpillSection {
    /// Logical capacity, in MiB.
    pub size_mb: u64,
    pub store: ArchiveStorageConfig,
    #[serde(default = "default_max_concurrent_transfers")]
    pub max_concurrent_transfers: usize,
}

fn default_max_concurrent_transfers() -> usize {
    16
}

impl SpillSection {
    pub fn resolve_paths(&mut self, config_dir: &Path) {
        if let ArchiveStorageConfig::Filesystem { path, .. } = &mut self.store {
            *path = resolve_path(path.clone(), config_dir);
        }
    }

    pub fn size_bytes(&self) -> Option<u64> {
        self.size_mb.checked_mul(1024 * 1024)
    }

    pub fn validate(
        &self,
        device: &DeviceSection,
        tuning: &TuningSection,
        has_stripe_source: bool,
        secrets: &HashMap<String, ResolvedSecret>,
    ) -> Result<()> {
        let refuse = |description: String| {
            Err(ubiblk_error!(InvalidParameter {
                description: description
            }))
        };

        let Some(size_bytes) = self.size_bytes().filter(|size| *size > 0) else {
            return refuse(format!(
                "spill size_mb {} is not a usable size",
                self.size_mb
            ));
        };
        if self.max_concurrent_transfers == 0 {
            return refuse("spill max_concurrent_transfers must be greater than 0".to_string());
        }

        let shift = device.stripe_sector_count_shift()?;
        let stripe_bytes = (1u64 << shift) * 512;
        let stripes = size_bytes.div_ceil(stripe_bytes);
        if stripes > MAX_SPILL_STRIPES {
            return refuse(format!(
                "a {} MiB spill device has {stripes} stripes, more than the {MAX_SPILL_STRIPES} \
                 it can track; use a larger stripe_sector_count_shift",
                self.size_mb
            ));
        }
        let transfer_bytes = (self.max_concurrent_transfers as u64).checked_mul(stripe_bytes);
        if transfer_bytes.is_none_or(|bytes| bytes > MAX_SPILL_TRANSFER_BYTES) {
            return refuse(format!(
                "{} concurrent transfers of {stripe_bytes} bytes need more than \
                 {MAX_SPILL_TRANSFER_BYTES} bytes of buffers",
                self.max_concurrent_transfers
            ));
        }

        if device.metadata_path.is_some() || has_stripe_source {
            return refuse(
                "spill cannot be combined with lazy metadata or a stripe source".to_string(),
            );
        }
        if tuning.io_engine == IoEngine::Sync {
            return refuse(
                "spill needs io_uring; the sync engine would block its worker".to_string(),
            );
        }
        if tuning.write_through {
            return refuse("spill does not support write_through".to_string());
        }

        match &self.store {
            ArchiveStorageConfig::Filesystem {
                archive_kek,
                autofetch,
                ..
            }
            | ArchiveStorageConfig::S3 {
                archive_kek,
                autofetch,
                ..
            } => {
                if archive_kek.is_some() || *autofetch {
                    return refuse("spill.store does not use archive_kek or autofetch".to_string());
                }
            }
        }
        self.store.validate(secrets)
    }
}
