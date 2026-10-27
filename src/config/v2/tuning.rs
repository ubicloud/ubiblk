use serde::Deserialize;

use crate::{backends::SECTOR_SIZE, config::v2::MAX_NUM_QUEUES, ubiblk_error};

/// I/O engine selection.
#[derive(Debug, Clone, Deserialize, PartialEq, Default)]
#[serde(rename_all = "snake_case")]
pub enum IoEngine {
    #[default]
    IoUring,
    Sync,
}

/// Performance tuning knobs.
#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct TuningSection {
    #[serde(default = "default_num_queues")]
    pub num_queues: usize,
    #[serde(default = "default_queue_size")]
    pub queue_size: usize,
    #[serde(default = "default_seg_size_max")]
    pub seg_size_max: u32,
    #[serde(default = "default_seg_count_max")]
    pub seg_count_max: u32,
    /// Advertised physical block size in bytes; logical sectors remain 512 bytes.
    #[serde(default = "default_io_size")]
    pub physical_block_size: u32,
    /// Advertised minimum efficient I/O size in bytes.
    #[serde(default = "default_io_size")]
    pub min_io_size: u32,
    /// Advertised optimal sustained I/O size in bytes.
    #[serde(default = "default_io_size")]
    pub opt_io_size: u32,
    #[serde(default = "default_poll_timeout_us")]
    pub poll_timeout_us: u64,
    #[serde(default)]
    pub cpus: Option<Vec<usize>>,
    #[serde(default)]
    pub io_engine: IoEngine,
    #[serde(default)]
    pub write_through: bool,
}

impl Default for TuningSection {
    fn default() -> Self {
        Self {
            num_queues: default_num_queues(),
            queue_size: default_queue_size(),
            seg_size_max: default_seg_size_max(),
            seg_count_max: default_seg_count_max(),
            physical_block_size: default_io_size(),
            min_io_size: default_io_size(),
            opt_io_size: default_io_size(),
            poll_timeout_us: default_poll_timeout_us(),
            cpus: None,
            io_engine: IoEngine::default(),
            write_through: false,
        }
    }
}

impl TuningSection {
    pub fn validate(&self) -> crate::Result<()> {
        for (name, size) in [
            ("physical_block_size", self.physical_block_size),
            ("min_io_size", self.min_io_size),
            ("opt_io_size", self.opt_io_size),
        ] {
            if size < SECTOR_SIZE as u32 || !size.is_power_of_two() {
                return Err(ubiblk_error!(InvalidParameter {
                    description: format!(
                        "{name} {size} is invalid (must be a power of two, at least {SECTOR_SIZE} bytes)"
                    ),
                }));
            }
        }
        if self.min_io_size < self.physical_block_size {
            return Err(ubiblk_error!(InvalidParameter {
                description: "min_io_size must be at least physical_block_size".to_string(),
            }));
        }
        if self.min_io_size / SECTOR_SIZE as u32 > u16::MAX as u32 {
            return Err(ubiblk_error!(InvalidParameter {
                description: "min_io_size exceeds the virtio limit of 65535 logical blocks"
                    .to_string(),
            }));
        }
        if self.opt_io_size < self.min_io_size {
            return Err(ubiblk_error!(InvalidParameter {
                description: "opt_io_size must be at least min_io_size".to_string(),
            }));
        }
        if self.num_queues == 0 || self.num_queues > MAX_NUM_QUEUES {
            return Err(ubiblk_error!(InvalidParameter {
                description: format!(
                    "num_queues {} is out of range (must be 1..={})",
                    self.num_queues, MAX_NUM_QUEUES
                ),
            }));
        }
        if self.queue_size == 0 || self.queue_size > 65536 || !self.queue_size.is_power_of_two() {
            return Err(ubiblk_error!(InvalidParameter {
                description: format!(
                    "queue_size {} is invalid (must be a non-zero power of two, max 65536)",
                    self.queue_size
                )
            }));
        }
        if self.seg_size_max == 0 || self.seg_size_max > 1_048_576 {
            return Err(ubiblk_error!(InvalidParameter {
                description: format!(
                    "seg_size_max {} is out of range (must be 1..=1048576)",
                    self.seg_size_max
                )
            }));
        }
        if self.seg_count_max == 0 || self.seg_count_max > 256 {
            return Err(ubiblk_error!(InvalidParameter {
                description: format!(
                    "seg_count_max {} is out of range (must be 1..=256)",
                    self.seg_count_max
                )
            }));
        }
        if let Some(cpus) = &self.cpus {
            if cpus.len() != self.num_queues {
                return Err(ubiblk_error!(InvalidParameter {
                    description: format!(
                        "Length of cpus ({}) does not match num_queues ({})",
                        cpus.len(),
                        self.num_queues
                    )
                }));
            }
        }
        if self.poll_timeout_us > 10_000_000 {
            return Err(ubiblk_error!(InvalidParameter {
                description: format!(
                    "poll_timeout_us {} is out of range (must be 1..=10000000)",
                    self.poll_timeout_us
                )
            }));
        }
        Ok(())
    }
}

fn default_num_queues() -> usize {
    1
}

fn default_queue_size() -> usize {
    64
}

fn default_seg_size_max() -> u32 {
    65536
}

fn default_seg_count_max() -> u32 {
    4
}

fn default_io_size() -> u32 {
    4096
}

fn default_poll_timeout_us() -> u64 {
    1000
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_tuning_section_is_valid() {
        let tuning = TuningSection::default();
        assert!(tuning.validate().is_ok());
    }

    #[test]
    fn omitted_topology_fields_default_to_4k() {
        for input in ["", "physical_block_size = 512"] {
            let tuning: TuningSection = toml::from_str(input).unwrap();
            assert_eq!(
                tuning.physical_block_size,
                if input.is_empty() { 4096 } else { 512 }
            );
            assert_eq!(tuning.min_io_size, 4096);
            assert_eq!(tuning.opt_io_size, 4096);
            tuning.validate().unwrap();
        }
    }

    #[test]
    fn topology_rejects_zero_small_and_non_power_of_two_sizes() {
        for field in ["physical_block_size", "min_io_size", "opt_io_size"] {
            for size in [0, 256, 768] {
                let input = format!("{field} = {size}");
                let tuning: TuningSection = toml::from_str(&input).unwrap();
                let err = tuning.validate().unwrap_err().to_string();
                assert!(err.contains(field), "{input}: {err}");
            }
        }
    }

    #[test]
    fn topology_validates_ordering_and_virtio_field_limit() {
        for (input, expected_error) in [
            ("physical_block_size = 8192", "physical_block_size"),
            ("min_io_size = 8192", "opt_io_size"),
            (
                "min_io_size = 33554432\nopt_io_size = 33554432",
                "65535 logical blocks",
            ),
        ] {
            let tuning: TuningSection = toml::from_str(input).unwrap();
            let err = tuning.validate().unwrap_err().to_string();
            assert!(err.contains(expected_error), "{input}: {err}");
        }

        for input in [
            "physical_block_size = 512\nmin_io_size = 512\nopt_io_size = 512",
            "physical_block_size = 16777216\nmin_io_size = 16777216\nopt_io_size = 2147483648",
        ] {
            let tuning: TuningSection = toml::from_str(input).unwrap();
            tuning.validate().unwrap();
        }
    }

    #[test]
    fn tuning_section_rejects_invalid_num_queues() {
        let mut tuning = TuningSection {
            num_queues: 0,
            ..Default::default()
        };
        assert!(tuning.validate().is_err());
        tuning.num_queues = 257;
        assert!(tuning.validate().is_err());
    }

    #[test]
    fn tuning_section_rejects_invalid_queue_size() {
        let mut tuning = TuningSection {
            queue_size: 0,
            ..Default::default()
        };
        assert!(tuning.validate().is_err());
        tuning.queue_size = 3; // not a power of two
        assert!(tuning.validate().is_err());
        tuning.queue_size = 65537;
        assert!(tuning.validate().is_err());
    }

    #[test]
    fn tuning_section_rejects_invalid_seg_size_max() {
        let mut tuning = TuningSection {
            seg_size_max: 0,
            ..Default::default()
        };
        assert!(tuning.validate().is_err());
        tuning.seg_size_max = 1_048_577;
        assert!(tuning.validate().is_err());
    }

    #[test]
    fn tuning_section_rejects_invalid_seg_count_max() {
        let mut tuning = TuningSection {
            seg_count_max: 0,
            ..Default::default()
        };
        assert!(tuning.validate().is_err());
        tuning.seg_count_max = 257;
        assert!(tuning.validate().is_err());
    }

    #[test]
    fn tuning_section_rejects_mismatched_cpus_length() {
        let tuning = TuningSection {
            num_queues: 2,
            cpus: Some(vec![0]), // length does not match num_queues
            ..Default::default()
        };
        assert!(tuning.validate().is_err());
    }

    #[test]
    fn tuning_section_rejects_invalid_poll_timeout() {
        let tuning = TuningSection {
            poll_timeout_us: 10_000_001,
            ..Default::default()
        };
        assert!(tuning.validate().is_err());
    }
}
