use std::sync::atomic::{AtomicBool, AtomicU8, AtomicUsize, Ordering};
use std::sync::Arc;

/// Phase constants for the operation state machine.
pub const NORMAL: u8 = 0;
pub const STALLING: u8 = 1;
pub const OPERATING: u8 = 2;

/// Shared state between all `OpsIoChannel` instances and the bgworker.
///
/// All fields are atomic and wrapped in `Arc` so that cloning is cheap
/// and sharing across threads is safe.
#[derive(Clone)]
pub struct OpsSharedState {
    /// Normal(0): pass-through. Hot path is one atomic load.
    /// Stalling(1): queue all new IO, drain in-flight.
    /// Operating(2): reads/writes gated by stripe_locks + gate_reads.
    phase: Arc<AtomicU8>,

    /// Per-stripe lock. `true` = not yet processed, writes must wait.
    /// If `gate_reads` is true, reads also wait.
    /// Only meaningful when phase == Operating.
    /// Bgworker stores `false` (Release) after process_stripe + on_stripe_done.
    stripe_locks: Arc<Vec<AtomicBool>>,

    /// Whether the current operation gates reads (`false` = snapshot, `true` = rekey).
    /// Set when operation begins, cleared when phase returns to Normal.
    gate_reads: Arc<AtomicBool>,

    /// Barrier counter: how many channels have fully drained.
    /// Bgworker proceeds to Operating when drained == num_channels.
    channels_drained: Arc<AtomicUsize>,

    /// Total active OpsIoChannels.
    /// Incremented in `create_channel()`, decremented in `Drop`.
    num_channels: Arc<AtomicUsize>,

    /// Progress: stripes processed (bgworker increments after process + unlock).
    stripes_processed: Arc<AtomicUsize>,
}

impl OpsSharedState {
    pub fn new(stripe_count: usize) -> Self {
        let mut locks = Vec::with_capacity(stripe_count);
        for _ in 0..stripe_count {
            locks.push(AtomicBool::new(false));
        }

        OpsSharedState {
            phase: Arc::new(AtomicU8::new(NORMAL)),
            stripe_locks: Arc::new(locks),
            gate_reads: Arc::new(AtomicBool::new(false)),
            channels_drained: Arc::new(AtomicUsize::new(0)),
            num_channels: Arc::new(AtomicUsize::new(0)),
            stripes_processed: Arc::new(AtomicUsize::new(0)),
        }
    }

    // --- Phase ---

    pub fn phase(&self) -> u8 {
        self.phase.load(Ordering::Acquire)
    }

    pub fn set_phase(&self, phase: u8) {
        self.phase.store(phase, Ordering::Release);
    }

    /// Attempt to transition from `NORMAL` to `STALLING`. Returns `true` on success.
    pub fn try_begin_stalling(&self) -> bool {
        self.phase
            .compare_exchange(NORMAL, STALLING, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
    }

    // --- Stripe locks ---

    pub fn stripe_locked(&self, stripe_id: usize) -> bool {
        self.stripe_locks[stripe_id].load(Ordering::Acquire)
    }

    pub fn lock_stripe(&self, stripe_id: usize) {
        self.stripe_locks[stripe_id].store(true, Ordering::Release);
    }

    pub fn unlock_stripe(&self, stripe_id: usize) {
        self.stripe_locks[stripe_id].store(false, Ordering::Release);
    }

    pub fn lock_all_stripes(&self) {
        for lock in self.stripe_locks.iter() {
            lock.store(true, Ordering::Release);
        }
    }

    pub fn unlock_all_stripes(&self) {
        for lock in self.stripe_locks.iter() {
            lock.store(false, Ordering::Release);
        }
    }

    pub fn stripe_count(&self) -> usize {
        self.stripe_locks.len()
    }

    // --- Gate reads ---

    pub fn gate_reads(&self) -> bool {
        self.gate_reads.load(Ordering::Acquire)
    }

    pub fn set_gate_reads(&self, gate: bool) {
        self.gate_reads.store(gate, Ordering::Release);
    }

    // --- Drain barrier ---

    pub fn channels_drained(&self) -> usize {
        self.channels_drained.load(Ordering::Acquire)
    }

    pub fn signal_drained(&self) {
        self.channels_drained.fetch_add(1, Ordering::Release);
    }

    pub fn reset_drained(&self) {
        self.channels_drained.store(0, Ordering::Release);
    }

    // --- Channel count ---

    pub fn num_channels(&self) -> usize {
        self.num_channels.load(Ordering::Acquire)
    }

    pub fn add_channel(&self) {
        self.num_channels.fetch_add(1, Ordering::Release);
    }

    pub fn remove_channel(&self) {
        self.num_channels.fetch_sub(1, Ordering::Release);
    }

    // --- Progress ---

    pub fn stripes_processed(&self) -> usize {
        self.stripes_processed.load(Ordering::Acquire)
    }

    pub fn increment_stripes_processed(&self) {
        self.stripes_processed.fetch_add(1, Ordering::Release);
    }

    pub fn reset_stripes_processed(&self) {
        self.stripes_processed.store(0, Ordering::Release);
    }
}
