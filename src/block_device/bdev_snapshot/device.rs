use std::collections::VecDeque;
use std::sync::atomic::Ordering;
use std::sync::Arc;

use crate::block_device::{BlockDevice, IoChannel, SharedBuffer};
use crate::Result;

use super::handle::SnapshotHandle;
use super::shared_state::{
    SnapshotSharedState, STATE_DRAINING, STATE_IDLE, STATE_RESUMING, STATE_SNAPSHOTTING,
};

/// A block device wrapper that supports live snapshots.
///
/// Wraps an inner BlockDevice and intercepts I/O to support coordinated
/// drain/resume across all channels during a snapshot operation.
pub struct SnapshotBlockDevice {
    base: Box<dyn BlockDevice>,
    shared: Arc<SnapshotSharedState>,
}

impl SnapshotBlockDevice {
    pub fn new(base: Box<dyn BlockDevice>) -> Self {
        SnapshotBlockDevice {
            base,
            shared: Arc::new(SnapshotSharedState::new()),
        }
    }

    /// Returns a handle that can be used by the RPC thread to trigger snapshots.
    pub fn snapshot_handle(&self) -> SnapshotHandle {
        SnapshotHandle::new(self.shared.clone())
    }
}

impl BlockDevice for SnapshotBlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>> {
        let base_channel = self.base.create_channel()?;
        self.shared.num_channels.fetch_add(1, Ordering::SeqCst);
        Ok(Box::new(SnapshotIoChannel::new(
            base_channel,
            self.shared.clone(),
        )))
    }

    fn sector_count(&self) -> u64 {
        self.base.sector_count()
    }

    fn clone(&self) -> Box<dyn BlockDevice> {
        Box::new(SnapshotBlockDevice {
            base: self.base.clone(),
            shared: self.shared.clone(),
        })
    }
}

/// A queued I/O request, stored while the snapshot layer is draining or snapshotting.
struct QueuedRequest {
    kind: QueuedRequestKind,
    id: usize,
}

enum QueuedRequestKind {
    Read {
        sector_offset: u64,
        sector_count: u32,
        buf: SharedBuffer,
    },
    Write {
        sector_offset: u64,
        sector_count: u32,
        buf: SharedBuffer,
    },
    Flush,
}

/// Per-channel snapshot state tracking.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ChannelDrainState {
    /// Channel is operating normally (Idle state).
    Normal,
    /// Channel has stopped sending new I/O to base, waiting for base.busy() == false.
    WaitingForDrain,
    /// Channel has confirmed drain (incremented drain_count).
    Drained,
    /// Channel is replaying queued I/O after swap.
    Replaying,
}

pub struct SnapshotIoChannel {
    base: Box<dyn IoChannel>,
    shared: Arc<SnapshotSharedState>,
    queued_requests: VecDeque<QueuedRequest>,
    local_state: ChannelDrainState,
}

impl SnapshotIoChannel {
    fn new(base: Box<dyn IoChannel>, shared: Arc<SnapshotSharedState>) -> Self {
        SnapshotIoChannel {
            base,
            shared,
            queued_requests: VecDeque::new(),
            local_state: ChannelDrainState::Normal,
        }
    }

    /// Check if we should be queuing I/O instead of passing through.
    fn should_queue(&self) -> bool {
        self.shared.state() != STATE_IDLE
    }

    /// Replay all queued requests against the base channel.
    fn replay_queued_requests(&mut self) {
        while let Some(req) = self.queued_requests.pop_front() {
            match req.kind {
                QueuedRequestKind::Read {
                    sector_offset,
                    sector_count,
                    buf,
                } => {
                    self.base.add_read(sector_offset, sector_count, buf, req.id);
                }
                QueuedRequestKind::Write {
                    sector_offset,
                    sector_count,
                    buf,
                } => {
                    self.base
                        .add_write(sector_offset, sector_count, buf, req.id);
                }
                QueuedRequestKind::Flush => {
                    self.base.add_flush(req.id);
                }
            }
        }
        // Submit all replayed requests in one batch.
        if let Err(e) = self.base.submit() {
            log::error!("Failed to submit replayed requests after snapshot: {e}");
        }
    }

    fn poll_draining(&mut self) -> Vec<(usize, bool)> {
        let results = self.base.poll();

        if self.local_state == ChannelDrainState::WaitingForDrain && !self.base.busy() {
            self.local_state = ChannelDrainState::Drained;
            self.shared.drain_count.fetch_add(1, Ordering::AcqRel);
            let (lock, cvar) = &self.shared.notify;
            let _guard = lock.lock().unwrap();
            cvar.notify_one();
        }

        results
    }

    fn poll_snapshotting(&mut self) -> Vec<(usize, bool)> {
        Vec::new()
    }

    fn poll_resuming(&mut self) -> Vec<(usize, bool)> {
        if self.local_state == ChannelDrainState::Drained {
            self.local_state = ChannelDrainState::Replaying;
            self.replay_queued_requests();
            self.local_state = ChannelDrainState::Normal;
            self.shared.resume_count.fetch_add(1, Ordering::AcqRel);
            let (lock, cvar) = &self.shared.notify;
            let _guard = lock.lock().unwrap();
            cvar.notify_one();
        }
        self.base.poll()
    }
}

impl Drop for SnapshotIoChannel {
    fn drop(&mut self) {
        self.shared.num_channels.fetch_sub(1, Ordering::SeqCst);
    }
}

impl IoChannel for SnapshotIoChannel {
    fn add_read(
        &mut self,
        sector_offset: u64,
        sector_count: u32,
        buf: SharedBuffer,
        id: usize,
    ) {
        if self.should_queue() {
            self.queued_requests.push_back(QueuedRequest {
                kind: QueuedRequestKind::Read {
                    sector_offset,
                    sector_count,
                    buf,
                },
                id,
            });
            return;
        }
        self.base.add_read(sector_offset, sector_count, buf, id);
    }

    fn add_write(
        &mut self,
        sector_offset: u64,
        sector_count: u32,
        buf: SharedBuffer,
        id: usize,
    ) {
        if self.should_queue() {
            self.queued_requests.push_back(QueuedRequest {
                kind: QueuedRequestKind::Write {
                    sector_offset,
                    sector_count,
                    buf,
                },
                id,
            });
            return;
        }
        self.base.add_write(sector_offset, sector_count, buf, id);
    }

    fn add_flush(&mut self, id: usize) {
        if self.should_queue() {
            self.queued_requests.push_back(QueuedRequest {
                kind: QueuedRequestKind::Flush,
                id,
            });
            return;
        }
        self.base.add_flush(id);
    }

    fn submit(&mut self) -> Result<()> {
        if self.should_queue() {
            return Ok(());
        }
        self.base.submit()
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        let state = self.shared.state();
        match state {
            STATE_IDLE => {
                self.local_state = ChannelDrainState::Normal;
                self.base.poll()
            }
            STATE_DRAINING => {
                if self.local_state == ChannelDrainState::Normal {
                    self.local_state = ChannelDrainState::WaitingForDrain;
                }
                self.poll_draining()
            }
            STATE_SNAPSHOTTING => self.poll_snapshotting(),
            STATE_RESUMING => self.poll_resuming(),
            _ => unreachable!("invalid snapshot state: {state}"),
        }
    }

    fn busy(&self) -> bool {
        self.base.busy() || !self.queued_requests.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backends::SECTOR_SIZE;
    use crate::block_device::{bdev_test::TestBlockDevice, shared_buffer};

    #[test]
    fn test_passthrough_idle() {
        let base = TestBlockDevice::new(4096);
        let snapshot_dev = SnapshotBlockDevice::new(Box::new(base));
        let mut ch = snapshot_dev.create_channel().unwrap();

        let buf = shared_buffer(SECTOR_SIZE);
        ch.add_write(0, 1, buf.clone(), 1);
        ch.submit().unwrap();
        let results = ch.poll();
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], (1, true));

        ch.add_read(0, 1, buf.clone(), 2);
        ch.submit().unwrap();
        let results = ch.poll();
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], (2, true));
    }

    #[test]
    fn test_flush_passthrough() {
        let base = TestBlockDevice::new(4096);
        let snapshot_dev = SnapshotBlockDevice::new(Box::new(base));
        let mut ch = snapshot_dev.create_channel().unwrap();

        ch.add_flush(1);
        ch.submit().unwrap();
        let results = ch.poll();
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], (1, true));
    }

    #[test]
    fn test_sector_count_delegation() {
        let base = TestBlockDevice::new(4096);
        let snapshot_dev = SnapshotBlockDevice::new(Box::new(base));
        assert_eq!(snapshot_dev.sector_count(), 4096 / SECTOR_SIZE as u64);
    }

    #[test]
    fn test_num_channels_incremented() {
        let base = TestBlockDevice::new(4096);
        let snapshot_dev = SnapshotBlockDevice::new(Box::new(base));
        assert_eq!(
            snapshot_dev
                .shared
                .num_channels
                .load(Ordering::Acquire),
            0
        );
        let _ch1 = snapshot_dev.create_channel().unwrap();
        assert_eq!(
            snapshot_dev
                .shared
                .num_channels
                .load(Ordering::Acquire),
            1
        );
        let _ch2 = snapshot_dev.create_channel().unwrap();
        assert_eq!(
            snapshot_dev
                .shared
                .num_channels
                .load(Ordering::Acquire),
            2
        );
    }

    #[test]
    fn test_queuing_when_draining() {
        let base = TestBlockDevice::new(4096);
        let snapshot_dev = SnapshotBlockDevice::new(Box::new(base));
        let mut ch = snapshot_dev.create_channel().unwrap();

        // Force state to DRAINING.
        snapshot_dev.shared.set_state(STATE_DRAINING);

        let buf = shared_buffer(SECTOR_SIZE);
        ch.add_read(0, 1, buf.clone(), 1);
        ch.add_write(0, 1, buf.clone(), 2);
        ch.add_flush(3);

        // submit should be a no-op.
        ch.submit().unwrap();

        // busy should be true because of queued requests.
        assert!(ch.busy());

        // Reset to idle.
        snapshot_dev.shared.set_state(STATE_IDLE);
    }

    #[test]
    fn test_queuing_when_snapshotting() {
        let base = TestBlockDevice::new(4096);
        let snapshot_dev = SnapshotBlockDevice::new(Box::new(base));
        let mut ch = snapshot_dev.create_channel().unwrap();

        snapshot_dev.shared.set_state(STATE_SNAPSHOTTING);

        let buf = shared_buffer(SECTOR_SIZE);
        ch.add_read(0, 1, buf.clone(), 1);
        ch.submit().unwrap();

        // poll returns empty during snapshotting.
        let results = ch.poll();
        assert!(results.is_empty());
        assert!(ch.busy());

        snapshot_dev.shared.set_state(STATE_IDLE);
    }

    #[test]
    fn test_drain_state_machine() {
        let base = TestBlockDevice::new(4096);
        let snapshot_dev = SnapshotBlockDevice::new(Box::new(base));
        let mut ch = snapshot_dev.create_channel().unwrap();

        // Start with some in-flight I/O.
        let buf = shared_buffer(SECTOR_SIZE);
        ch.add_write(0, 1, buf.clone(), 1);
        ch.submit().unwrap();

        // Transition to draining.
        snapshot_dev.shared.set_state(STATE_DRAINING);

        // poll should return the in-flight completion and then report drained
        // (because TestBlockDevice completes immediately in add_write).
        let results = ch.poll();
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], (1, true));

        // Channel should have reported drained since base.busy() == false.
        assert_eq!(
            snapshot_dev
                .shared
                .drain_count
                .load(Ordering::Acquire),
            1
        );

        snapshot_dev.shared.set_state(STATE_IDLE);
    }

    #[test]
    fn test_resume_replays_queued_io() {
        let base = TestBlockDevice::new(4096);
        let snapshot_dev = SnapshotBlockDevice::new(Box::new(base));
        let mut ch = snapshot_dev.create_channel().unwrap();

        // Simulate drain: transition to draining.
        snapshot_dev.shared.set_state(STATE_DRAINING);

        // Queue some I/O.
        let buf = shared_buffer(SECTOR_SIZE);
        ch.add_write(0, 1, buf.clone(), 10);
        ch.add_read(0, 1, buf.clone(), 11);
        ch.add_flush(12);

        // poll during draining — base has no in-flight, so it reports drained.
        let results = ch.poll();
        assert!(results.is_empty());
        assert_eq!(
            snapshot_dev
                .shared
                .drain_count
                .load(Ordering::Acquire),
            1
        );

        // Transition to snapshotting (swap phase).
        snapshot_dev.shared.set_state(STATE_SNAPSHOTTING);
        let results = ch.poll();
        assert!(results.is_empty());

        // Transition to resuming.
        snapshot_dev.shared.set_state(STATE_RESUMING);

        // poll during resuming should replay queued I/O and return results.
        let results = ch.poll();
        // TestBlockDevice completes immediately, so all 3 requests should complete.
        assert_eq!(results.len(), 3);

        // Channel should have incremented resume_count.
        assert_eq!(
            snapshot_dev
                .shared
                .resume_count
                .load(Ordering::Acquire),
            1
        );

        // busy should now be false.
        assert!(!ch.busy());

        snapshot_dev.shared.set_state(STATE_IDLE);
    }

    #[test]
    fn test_queued_requests_fifo_order() {
        let base = TestBlockDevice::new(4096);
        let snapshot_dev = SnapshotBlockDevice::new(Box::new(base));
        let mut ch = snapshot_dev.create_channel().unwrap();

        // Force state to draining, then queue I/O.
        snapshot_dev.shared.set_state(STATE_DRAINING);

        let buf = shared_buffer(SECTOR_SIZE);
        ch.add_write(0, 1, buf.clone(), 100);
        ch.add_flush(101);
        ch.add_read(0, 1, buf.clone(), 102);

        // Drain.
        ch.poll();

        // Resume.
        snapshot_dev.shared.set_state(STATE_RESUMING);
        let results = ch.poll();

        // Verify all 3 requests completed (TestBlockDevice completes inline).
        assert_eq!(results.len(), 3);
        let ids: Vec<usize> = results.iter().map(|(id, _)| *id).collect();
        // TestBlockDevice returns completions in the order add_* was called,
        // which should be FIFO: 100, 101, 102.
        assert_eq!(ids, vec![100, 101, 102]);

        snapshot_dev.shared.set_state(STATE_IDLE);
    }

    #[test]
    fn test_busy_with_queued_and_base() {
        let base = TestBlockDevice::new(4096);
        let snapshot_dev = SnapshotBlockDevice::new(Box::new(base));
        let mut ch = snapshot_dev.create_channel().unwrap();

        // Initially not busy.
        assert!(!ch.busy());

        // Add I/O — TestBlockDevice queues completions in add_*, so busy after add.
        let buf = shared_buffer(SECTOR_SIZE);
        ch.add_write(0, 1, buf.clone(), 1);
        // TestBlockDevice's busy() returns true if finished_requests is non-empty.
        assert!(ch.busy());
        ch.submit().unwrap();
        // Poll to drain.
        ch.poll();
        assert!(!ch.busy());

        // Queue requests.
        snapshot_dev.shared.set_state(STATE_DRAINING);
        ch.add_write(0, 1, buf.clone(), 2);
        assert!(ch.busy()); // busy because queued_requests is non-empty.

        snapshot_dev.shared.set_state(STATE_IDLE);
    }

    #[test]
    fn test_clone_shares_state() {
        let base = TestBlockDevice::new(4096);
        let snapshot_dev = SnapshotBlockDevice::new(Box::new(base));
        let _ch = snapshot_dev.create_channel().unwrap();

        let cloned = BlockDevice::clone(&snapshot_dev);
        let _ch2 = cloned.create_channel().unwrap();

        // Both share the same shared state, so num_channels should be 2.
        assert_eq!(
            snapshot_dev
                .shared
                .num_channels
                .load(Ordering::Acquire),
            2
        );
    }

    #[test]
    fn test_full_snapshot_lifecycle() {
        // Tests the complete snapshot lifecycle with a single channel:
        // Idle → Draining → Snapshotting → Resuming → Idle
        let base = TestBlockDevice::new(4096);
        let snapshot_dev = SnapshotBlockDevice::new(Box::new(base));
        let mut ch = snapshot_dev.create_channel().unwrap();
        let handle = snapshot_dev.snapshot_handle();

        // Use a thread for the coordinator since trigger_snapshot blocks.
        let shared = snapshot_dev.shared.clone();
        let coord = std::thread::spawn(move || {
            handle.trigger_snapshot(|| Ok(()))
        });

        // Wait until state is DRAINING.
        while shared.state() == STATE_IDLE {
            std::thread::yield_now();
        }
        assert_eq!(shared.state(), STATE_DRAINING);

        // Poll to drain (no in-flight I/O).
        ch.poll();

        // Wait for state to become RESUMING (coordinator does SNAPSHOTTING then RESUMING).
        while shared.state() != STATE_RESUMING {
            std::thread::yield_now();
        }

        // Poll to resume.
        ch.poll();

        // Coordinator should complete.
        let result = coord.join().unwrap();
        assert!(result.is_ok());
        assert_eq!(shared.state(), STATE_IDLE);
    }

    #[test]
    fn test_num_channels_decremented_on_drop() {
        let base = TestBlockDevice::new(4096);
        let snapshot_dev = SnapshotBlockDevice::new(Box::new(base));

        let ch1 = snapshot_dev.create_channel().unwrap();
        let ch2 = snapshot_dev.create_channel().unwrap();
        assert_eq!(snapshot_dev.shared.num_channels.load(Ordering::Acquire), 2);

        drop(ch1);
        assert_eq!(snapshot_dev.shared.num_channels.load(Ordering::Acquire), 1);

        drop(ch2);
        assert_eq!(snapshot_dev.shared.num_channels.load(Ordering::Acquire), 0);
    }

    #[test]
    fn test_snapshot_after_channel_drop() {
        // Create 2 channels, drop 1, trigger snapshot with only the surviving channel.
        let base = TestBlockDevice::new(4096);
        let snapshot_dev = SnapshotBlockDevice::new(Box::new(base));

        let ch1 = snapshot_dev.create_channel().unwrap();
        let mut ch2 = snapshot_dev.create_channel().unwrap();
        assert_eq!(snapshot_dev.shared.num_channels.load(Ordering::Acquire), 2);

        // Drop ch1 — num_channels should be 1.
        drop(ch1);
        assert_eq!(snapshot_dev.shared.num_channels.load(Ordering::Acquire), 1);

        let handle = snapshot_dev.snapshot_handle();
        let shared = snapshot_dev.shared.clone();

        // trigger_snapshot should only wait for 1 channel (the surviving one).
        let coord = std::thread::spawn(move || handle.trigger_snapshot(|| Ok(())));

        // Wait until state is DRAINING.
        while shared.state() == STATE_IDLE {
            std::thread::yield_now();
        }
        assert_eq!(shared.state(), STATE_DRAINING);

        // Only ch2 needs to drain.
        ch2.poll();

        // Wait for RESUMING.
        while shared.state() != STATE_RESUMING {
            std::thread::yield_now();
        }

        // ch2 resumes.
        ch2.poll();

        let result = coord.join().unwrap();
        assert!(result.is_ok());
        assert_eq!(shared.state(), STATE_IDLE);
    }
}
