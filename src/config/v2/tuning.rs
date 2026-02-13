use serde::Deserialize;

use crate::ubiblk_error;

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
            poll_timeout_us: default_poll_timeout_us(),
            cpus: None,
            io_engine: IoEngine::default(),
            write_through: false,
        }
    }
}

impl TuningSection {
    pub fn validate(&self) -> crate::Result<()> {
        if self.num_queues == 0 || self.num_queues > 256 {
            return Err(ubiblk_error!(InvalidParameter {
                description: format!(
                    "num_queues {} is out of range (must be 1..=256)",
                    self.num_queues
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
