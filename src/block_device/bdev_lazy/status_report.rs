use super::metadata::SharedMetadataState;
use serde::{Deserialize, Serialize};

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
struct StripesRecord {
    total: u64,
    no_source: u64,
    fetched: u64,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct StatusReport {
    stripes: StripesRecord,
}

impl StatusReport {
    pub fn new(total: u64, no_source: u64, fetched: u64) -> Self {
        StatusReport {
            stripes: StripesRecord {
                total,
                no_source,
                fetched,
            },
        }
    }
}

#[derive(Debug, Clone)]
pub struct StatusReporter {
    shared_state: SharedMetadataState,
    target_sector_count: u64,
}

impl StatusReporter {
    pub fn new(shared_state: SharedMetadataState, target_sector_count: u64) -> Self {
        StatusReporter {
            shared_state,
            target_sector_count,
        }
    }

    pub fn report(&self) -> StatusReport {
        let stripe_sector_count = self.shared_state.stripe_sector_count();
        let total_stripes = self.target_sector_count.div_ceil(stripe_sector_count);
        StatusReport::new(
            total_stripes,
            self.shared_state.no_source_stripes(),
            self.shared_state.fetched_stripes(),
        )
    }
}
