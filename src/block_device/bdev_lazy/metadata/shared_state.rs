use super::UbiMetadata;
use std::sync::{
    atomic::{AtomicU64, AtomicU8, Ordering},
    Arc,
};

#[derive(Debug, Clone)]
pub struct SharedMetadataState {
    stripe_headers: Arc<Vec<AtomicU8>>,
    stripe_sector_count_shift: u8,
    fetched_stripes: Arc<AtomicU64>,
    no_source_stripes: Arc<AtomicU64>,
}

const STRIPE_FETCHED_BIT: u8 = 0;
const STRIPE_WRITTEN_BIT: u8 = 1;
const STRIPE_NO_SOURCE_DATA_BIT: u8 = 2;

impl SharedMetadataState {
    pub fn new(metadata: &UbiMetadata) -> Self {
        let stripe_headers = Arc::new(
            metadata
                .stripe_headers
                .iter()
                .map(|h| AtomicU8::new(*h))
                .collect::<Vec<_>>(),
        );

        let (mut fetched_stripes, mut no_source_stripes) = (0, 0);
        for header in metadata.stripe_headers.iter() {
            if header & (1 << STRIPE_FETCHED_BIT) != 0 {
                fetched_stripes += 1;
            }
            if header & (1 << STRIPE_NO_SOURCE_DATA_BIT) != 0 {
                no_source_stripes += 1;
            }
        }

        Self {
            stripe_headers,
            stripe_sector_count_shift: metadata.stripe_sector_count_shift,
            fetched_stripes: Arc::new(AtomicU64::new(fetched_stripes)),
            no_source_stripes: Arc::new(AtomicU64::new(no_source_stripes)),
        }
    }

    pub fn stripe_sector_count(&self) -> u64 {
        1u64 << self.stripe_sector_count_shift
    }

    pub fn sector_to_stripe_id(&self, sector: u64) -> usize {
        (sector >> self.stripe_sector_count_shift) as usize
    }

    pub fn stripe_fetched_if_needed(&self, stripe_id: usize) -> bool {
        let header = self.stripe_headers[stripe_id].load(Ordering::Acquire);
        header & ((1 << STRIPE_FETCHED_BIT) | (1 << STRIPE_NO_SOURCE_DATA_BIT)) != 0
    }

    #[cfg(test)]
    pub fn stripe_fetched(&self, stripe_id: usize) -> bool {
        let header = self.stripe_headers[stripe_id].load(Ordering::Acquire);
        header & (1 << STRIPE_FETCHED_BIT) != 0
    }

    pub fn stripe_written(&self, stripe_id: usize) -> bool {
        let header = self.stripe_headers[stripe_id].load(Ordering::Acquire);
        header & (1 << STRIPE_WRITTEN_BIT) != 0
    }

    pub fn set_stripe_header(&self, stripe_id: usize, header: u8) {
        let prev = self.stripe_headers[stripe_id].swap(header, Ordering::AcqRel);
        if prev & (1 << STRIPE_FETCHED_BIT) == 0 && header & (1 << STRIPE_FETCHED_BIT) != 0 {
            self.fetched_stripes.fetch_add(1, Ordering::AcqRel);
        }
    }

    pub fn fetched_stripes(&self) -> u64 {
        self.fetched_stripes.load(Ordering::Acquire)
    }

    pub fn no_source_stripes(&self) -> u64 {
        self.no_source_stripes.load(Ordering::Acquire)
    }
}
