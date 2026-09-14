//! Configuration for the nonpersistent, single-queue spill device.
use std::{collections::HashMap, path::Path};

use serde::Deserialize;

use super::{secrets::ResolvedSecret, stripe_source::ArchiveStorageConfig, DeviceSection};
use crate::Result;

#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct SpillSection {
    pub size_mb: u64,
    pub store: ArchiveStorageConfig,
}

impl SpillSection {
    pub fn resolve_paths(&mut self, directory: &Path) {
        if let ArchiveStorageConfig::Filesystem { path, .. } = &mut self.store {
            if path.is_relative() {
                *path = directory.join(&*path);
            }
        }
    }

    pub fn sector_count(&self) -> Result<u64> {
        self.size_mb
            .checked_mul(2048)
            .filter(|n| *n > 0)
            .ok_or_else(|| {
                crate::ubiblk_error!(InvalidParameter {
                    description: "spill.size_mb must be positive and fit in sectors".to_string(),
                })
            })
    }

    pub fn validate(&self, secrets: &HashMap<String, ResolvedSecret>) -> Result<()> {
        self.sector_count()?;
        self.store.validate(secrets)
    }
}

impl DeviceSection {
    pub fn validate_stripe_geometry(&self) -> Result<()> {
        if self
            .stripe_sector_count_shift
            .is_some_and(|shift| !(6..=16).contains(&shift))
        {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: "device.stripe_sector_count_shift must be between 6 and 16"
                    .to_string(),
            }));
        }
        Ok(())
    }

    pub fn stripe_sectors(&self) -> Result<u64> {
        self.validate_stripe_geometry()?;
        Ok(1u64
            << self
                .stripe_sector_count_shift
                .unwrap_or(crate::block_device::DEFAULT_STRIPE_SECTOR_COUNT_SHIFT))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn spill_capacity_and_paths_are_checked() {
        let mut config: SpillSection =
            toml::from_str("size_mb = 4\n[store]\nstorage = 'filesystem'\npath = 'cold'").unwrap();
        config.resolve_paths(Path::new("/tmp/device"));
        assert_eq!(config.sector_count().unwrap(), 8192);
        assert!(
            matches!(&config.store, ArchiveStorageConfig::Filesystem { path, .. } if path == Path::new("/tmp/device/cold"))
        );
        for invalid in [0, u64::MAX] {
            config.size_mb = invalid;
            assert!(config.sector_count().is_err());
        }
    }
}
