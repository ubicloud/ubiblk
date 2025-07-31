use super::UbiMetadata;
use std::sync::{
    atomic::{AtomicU64, AtomicU8, Ordering},
    Arc,
};

#[derive(Debug, Clone)]
pub struct SharedMetadataState {
    stripe_headers: Arc<Vec<AtomicU8>>,
    metadata_version: Arc<AtomicU64>,
    metadata_version_flushed: Arc<AtomicU64>,
}

impl SharedMetadataState {
    pub fn new(metadata: &UbiMetadata) -> Self {
        let stripe_headers = metadata.stripe_headers.clone();
        // Start at version 1 so initial state is not considered flushed.
        let metadata_version = Arc::new(AtomicU64::new(1));
        let metadata_version_flushed = Arc::new(AtomicU64::new(0));

        Self {
            stripe_headers,
            metadata_version,
            metadata_version_flushed,
        }
    }

    pub fn increment_version(&self) {
        // Use a strong ordering here because updates to the metadata version
        // coordinate flush operations across multiple threads.  Other callers
        // only perform `Acquire` loads, so `SeqCst` ensures they observe the
        // increment once the update is complete.
        self.metadata_version.fetch_add(1, Ordering::SeqCst);
    }

    pub fn set_flushed_version(&self, version: u64) {
        self.metadata_version_flushed
            .store(version, Ordering::Release);
    }

    pub fn flushed_version(&self) -> u64 {
        self.metadata_version_flushed.load(Ordering::Acquire)
    }

    pub fn current_version(&self) -> u64 {
        self.metadata_version.load(Ordering::Acquire)
    }

    pub fn needs_flush(&self) -> bool {
        let flushed = self.metadata_version_flushed.load(Ordering::Acquire);
        let current = self.metadata_version.load(Ordering::Acquire);
        current > flushed
    }

    pub fn stripe_fetched(&self, stripe_id: usize) -> bool {
        let header = self.stripe_headers[stripe_id].load(Ordering::SeqCst);
        header & (1 << 0) != 0
    }

    pub fn stripe_written(&self, stripe_id: usize) -> bool {
        let header = self.stripe_headers[stripe_id].load(Ordering::SeqCst);
        header & (1 << 1) != 0
    }

    pub fn set_stripe_fetched(&self, stripe_id: usize) {
        let prev_header = self.stripe_headers[stripe_id].fetch_or(1 << 0, Ordering::SeqCst);
        if prev_header & (1 << 0) == 0 {
            self.increment_version();
        }
    }

    pub fn set_stripe_written(&self, stripe_id: usize) {
        let prev_header = self.stripe_headers[stripe_id].fetch_or(1 << 1, Ordering::SeqCst);
        if prev_header & (1 << 1) == 0 {
            self.increment_version();
        }
    }
}
