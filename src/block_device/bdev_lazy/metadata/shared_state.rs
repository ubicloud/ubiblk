use super::UbiMetadata;
use std::sync::{
    atomic::{AtomicU64, AtomicU8, Ordering},
    Arc,
};

#[derive(Debug, Clone)]
pub struct SharedMetadataState {
    stripe_fetch_states: Arc<Vec<AtomicU8>>,
    stripe_write_states: Arc<Vec<AtomicU8>>,
    stripe_sector_count_shift: u8,
    fetched_stripes_count: Arc<AtomicU64>,
    no_source_stripes_count: Arc<AtomicU64>,
}

pub const NotFetched: u8 = 0b0000_0000;
pub const Fetched: u8 = 0b0000_0001;
pub const Failed: u8 = 0b0000_0010;
pub const NoSource: u8 = 0b0000_0100;

pub const NotWritten: u8 = 0b0000_0000;
pub const Written: u8 = 0b0000_0001;

const METADATA_STRIPE_FETCHED_BITMASK: u8 = 1 << 0;
const METADATA_STRIPE_WRITTEN_BITMASK: u8 = 1 << 1;
const METADATA_STRIPE_NO_SOURCE_DATA_BITMASK: u8 = 1 << 2;

impl SharedMetadataState {
    pub fn new(metadata: &UbiMetadata) -> Self {
        let (mut stripe_fetch_states, mut stripe_write_states) = (Vec::new(), Vec::new());
        let (mut fetched_stripes_count, mut no_source_stripes_count) = (0, 0);
        for header in metadata.stripe_headers.iter() {
            let (mut fetch_state, mut write_state) = (NotFetched, NotWritten);
            if header & METADATA_STRIPE_FETCHED_BITMASK != 0 {
                fetch_state = Fetched;
                fetched_stripes_count += 1;
            }
            if header & METADATA_STRIPE_WRITTEN_BITMASK != 0 {
                write_state = Written;
            }
            if header & METADATA_STRIPE_NO_SOURCE_DATA_BITMASK != 0 {
                fetch_state = NoSource;
                no_source_stripes_count += 1;
            }
            stripe_fetch_states.push(AtomicU8::new(fetch_state));
            stripe_write_states.push(AtomicU8::new(write_state));
        }

        Self {
            stripe_fetch_states: Arc::new(stripe_fetch_states),
            stripe_write_states: Arc::new(stripe_write_states),
            stripe_sector_count_shift: metadata.stripe_sector_count_shift,
            fetched_stripes_count: Arc::new(AtomicU64::new(fetched_stripes_count)),
            no_source_stripes_count: Arc::new(AtomicU64::new(no_source_stripes_count)),
        }
    }

    pub fn stripe_sector_count(&self) -> u64 {
        1u64 << self.stripe_sector_count_shift
    }

    pub fn sector_to_stripe_id(&self, sector: u64) -> usize {
        (sector >> self.stripe_sector_count_shift) as usize
    }

    pub fn stripe_fetched_if_needed(&self, stripe_id: usize) -> bool {
        let state = self.stripe_fetch_states[stripe_id].load(Ordering::Acquire);
        state == Fetched || state == NoSource
    }

    #[cfg(test)]
    pub fn stripe_fetched(&self, stripe_id: usize) -> bool {
        self.stripe_fetch_states[stripe_id].load(Ordering::Acquire) == Fetched
    }

    pub fn stripe_written(&self, stripe_id: usize) -> bool {
        self.stripe_write_states[stripe_id].load(Ordering::Acquire) == Written
    }

    pub fn stripe_fetch_state(&self, stripe_id: usize) -> u8 {
        self.stripe_fetch_states[stripe_id].load(Ordering::Acquire)
    }

    pub fn set_stripe_header(&self, stripe_id: usize, header: u8) {
        if header & METADATA_STRIPE_FETCHED_BITMASK != 0 {
            let prev = self.stripe_fetch_states[stripe_id].swap(Fetched, Ordering::AcqRel);
            if prev & METADATA_STRIPE_FETCHED_BITMASK == 0
                && header & METADATA_STRIPE_FETCHED_BITMASK != 0
            {
                self.fetched_stripes_count.fetch_add(1, Ordering::AcqRel);
            }
        }
        if header & METADATA_STRIPE_WRITTEN_BITMASK != 0 {
            self.stripe_write_states[stripe_id].store(Written, Ordering::Release)
        }
    }

    pub fn set_stripe_failed(&self, stripe_id: usize) {
        self.stripe_fetch_states[stripe_id].store(Failed, Ordering::Release)
    }

    pub fn fetched_stripes(&self) -> u64 {
        self.fetched_stripes_count.load(Ordering::Acquire)
    }

    pub fn no_source_stripes(&self) -> u64 {
        self.no_source_stripes_count.load(Ordering::Acquire)
    }
}
