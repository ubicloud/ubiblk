use super::UbiMetadata;
use std::sync::{
    atomic::{AtomicU8, Ordering},
    Arc,
};

#[derive(Debug, Clone)]
pub struct SharedMetadataState {
    stripe_headers: Arc<Vec<AtomicU8>>,
    stripe_sector_count_shift: u8,
}

impl SharedMetadataState {
    pub fn new(metadata: &UbiMetadata) -> Self {
        let stripe_headers = Arc::new(
            metadata
                .stripe_headers
                .iter()
                .map(|h| AtomicU8::new(*h))
                .collect::<Vec<_>>(),
        );

        Self {
            stripe_headers,
            stripe_sector_count_shift: metadata.stripe_sector_count_shift,
        }
    }

    pub fn stripe_sector_count(&self) -> u64 {
        1u64 << self.stripe_sector_count_shift
    }

    pub fn sector_to_stripe_id(&self, sector: u64) -> usize {
        (sector >> self.stripe_sector_count_shift) as usize
    }

    pub fn stripe_fetched(&self, stripe_id: usize) -> bool {
        let header = self.stripe_headers[stripe_id].load(Ordering::Acquire);
        header & (1 << 0) != 0
    }

    pub fn stripe_written(&self, stripe_id: usize) -> bool {
        let header = self.stripe_headers[stripe_id].load(Ordering::Acquire);
        header & (1 << 1) != 0
    }

    pub fn set_stripe_header(&self, stripe_id: usize, header: u8) {
        self.stripe_headers[stripe_id].store(header, Ordering::Release);
    }
}
