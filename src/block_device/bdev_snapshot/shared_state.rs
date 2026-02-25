use std::sync::{
    atomic::{AtomicU8, AtomicUsize, Ordering},
    Condvar, Mutex,
};

pub const STATE_IDLE: u8 = 0;
pub const STATE_DRAINING: u8 = 1;
pub const STATE_SNAPSHOTTING: u8 = 2;
pub const STATE_RESUMING: u8 = 3;

/// Shared state between all SnapshotIoChannels and the snapshot coordinator.
///
/// The coordinator (RPC thread) is the only writer of the `state` field;
/// channels are readers of state and writers of counters.
pub struct SnapshotSharedState {
    /// Current snapshot state. Written by coordinator, read by channels.
    state: AtomicU8,

    /// Number of channels that have confirmed they are drained.
    pub(crate) drain_count: AtomicUsize,

    /// Number of channels that have confirmed they have resumed.
    pub(crate) resume_count: AtomicUsize,

    /// Total number of IoChannels. Incremented in create_channel().
    pub(crate) num_channels: AtomicUsize,

    /// Notification mechanism: coordinator waits on this when drain/resume
    /// counts haven't reached num_channels yet. Channels signal it after
    /// incrementing a counter.
    pub(crate) notify: (Mutex<()>, Condvar),
}

impl Default for SnapshotSharedState {
    fn default() -> Self {
        Self::new()
    }
}

impl SnapshotSharedState {
    pub fn new() -> Self {
        SnapshotSharedState {
            state: AtomicU8::new(STATE_IDLE),
            drain_count: AtomicUsize::new(0),
            resume_count: AtomicUsize::new(0),
            num_channels: AtomicUsize::new(0),
            notify: (Mutex::new(()), Condvar::new()),
        }
    }

    /// Returns the current snapshot state.
    pub fn state(&self) -> u8 {
        self.state.load(Ordering::Acquire)
    }

    /// Sets the snapshot state. Only called by the coordinator.
    pub fn set_state(&self, state: u8) {
        self.state.store(state, Ordering::Release);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    #[test]
    fn test_initial_state() {
        let state = SnapshotSharedState::new();
        assert_eq!(state.state(), STATE_IDLE);
        assert_eq!(state.drain_count.load(Ordering::Acquire), 0);
        assert_eq!(state.resume_count.load(Ordering::Acquire), 0);
        assert_eq!(state.num_channels.load(Ordering::Acquire), 0);
    }

    #[test]
    fn test_state_transitions() {
        let state = SnapshotSharedState::new();
        assert_eq!(state.state(), STATE_IDLE);

        state.set_state(STATE_DRAINING);
        assert_eq!(state.state(), STATE_DRAINING);

        state.set_state(STATE_SNAPSHOTTING);
        assert_eq!(state.state(), STATE_SNAPSHOTTING);

        state.set_state(STATE_RESUMING);
        assert_eq!(state.state(), STATE_RESUMING);

        state.set_state(STATE_IDLE);
        assert_eq!(state.state(), STATE_IDLE);
    }

    #[test]
    fn test_counter_increments() {
        let state = Arc::new(SnapshotSharedState::new());

        state.num_channels.fetch_add(1, Ordering::SeqCst);
        state.num_channels.fetch_add(1, Ordering::SeqCst);
        assert_eq!(state.num_channels.load(Ordering::Acquire), 2);

        state.drain_count.fetch_add(1, Ordering::AcqRel);
        assert_eq!(state.drain_count.load(Ordering::Acquire), 1);
        state.drain_count.fetch_add(1, Ordering::AcqRel);
        assert_eq!(state.drain_count.load(Ordering::Acquire), 2);
    }

    #[test]
    fn test_condvar_notification() {
        let state = Arc::new(SnapshotSharedState::new());
        let state2 = state.clone();

        state.num_channels.fetch_add(1, Ordering::SeqCst);

        let handle = std::thread::spawn(move || {
            // Simulate channel draining
            std::thread::sleep(std::time::Duration::from_millis(50));
            state2.drain_count.fetch_add(1, Ordering::AcqRel);
            let (lock, cvar) = &state2.notify;
            let _guard = lock.lock().unwrap();
            cvar.notify_one();
        });

        // Wait for drain_count to reach 1
        let (lock, cvar) = &state.notify;
        let guard = lock.lock().unwrap();
        let result = cvar
            .wait_timeout_while(guard, std::time::Duration::from_secs(5), |_| {
                state.drain_count.load(Ordering::Acquire) < 1
            })
            .unwrap();
        assert!(!result.1.timed_out());
        assert_eq!(state.drain_count.load(Ordering::Acquire), 1);

        handle.join().unwrap();
    }
}
