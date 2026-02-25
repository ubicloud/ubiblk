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

    /// Multi-channel snapshot drain integration test.
    ///
    /// Exercises the full snapshot lifecycle with 4 channels, each with different
    /// I/O patterns (some with in-flight I/O, some idle, some queuing I/O during
    /// drain). The coordinator runs on a separate thread while the main thread
    /// drives all channels through drain/resume. Verifies that:
    /// - The coordinator blocks until ALL channels confirm drain
    /// - I/O queued during drain is replayed correctly on resume
    /// - Data written before and after the snapshot is consistent
    /// - The swap_fn executes only after all channels are quiesced
    #[test]
    fn test_multi_channel_snapshot_drain() {
        use std::sync::atomic::AtomicBool;

        let base = TestBlockDevice::new(4096);
        let snapshot_dev = SnapshotBlockDevice::new(Box::new(base));
        let handle = snapshot_dev.snapshot_handle();
        let shared = snapshot_dev.shared.clone();

        // Create 4 channels.
        let mut ch1 = snapshot_dev.create_channel().unwrap();
        let mut ch2 = snapshot_dev.create_channel().unwrap();
        let mut ch3 = snapshot_dev.create_channel().unwrap();
        let mut ch4 = snapshot_dev.create_channel().unwrap();
        assert_eq!(shared.num_channels.load(Ordering::Acquire), 4);

        // Write initial data via ch1 before snapshot (0xAA at sector 0).
        let write_buf = shared_buffer(SECTOR_SIZE);
        write_buf.borrow_mut().as_mut_slice().fill(0xAA);
        ch1.add_write(0, 1, write_buf.clone(), 1);
        ch1.submit().unwrap();
        let results = ch1.poll();
        assert_eq!(results, vec![(1, true)]);

        // Track whether swap_fn was called.
        let swap_called = Arc::new(AtomicBool::new(false));
        let swap_called2 = swap_called.clone();

        // Coordinator thread triggers snapshot (blocks until all channels drain).
        let coord = std::thread::spawn(move || {
            handle.trigger_snapshot(|| {
                swap_called2.store(true, Ordering::SeqCst);
                Ok(())
            })
        });

        // Wait for draining state.
        while shared.state() == STATE_IDLE {
            std::thread::yield_now();
        }
        assert_eq!(shared.state(), STATE_DRAINING);

        // --- Drain phase: each channel behaves differently ---

        // Channel 1: idle channel, just poll to drain.
        ch1.poll();

        // Channel 2: queue a write + flush during drain (replayed on resume).
        let write_buf2 = shared_buffer(SECTOR_SIZE);
        write_buf2.borrow_mut().as_mut_slice().fill(0xBB);
        ch2.add_write(1, 1, write_buf2.clone(), 20);
        ch2.add_flush(21);
        ch2.poll(); // drain (no in-flight I/O in base)

        // Channel 3: queue a read during drain.
        let read_buf = shared_buffer(SECTOR_SIZE);
        ch3.add_read(0, 1, read_buf.clone(), 30);
        ch3.poll(); // drain

        // Verify: 3 channels drained, coordinator still blocked waiting for ch4.
        assert_eq!(shared.drain_count.load(Ordering::Acquire), 3);
        assert!(!swap_called.load(Ordering::SeqCst));

        // Channel 4: last channel drains — this unblocks the coordinator.
        ch4.poll();

        // Wait for coordinator to finish swap and enter RESUMING.
        while shared.state() != STATE_RESUMING {
            std::thread::yield_now();
        }
        assert!(swap_called.load(Ordering::SeqCst));

        // --- Resume phase: all channels replay queued I/O ---
        ch1.poll();
        ch2.poll();
        ch3.poll();
        ch4.poll();

        // Coordinator completes.
        let result = coord.join().unwrap();
        assert!(result.is_ok());
        assert_eq!(shared.state(), STATE_IDLE);
        assert_eq!(shared.drain_count.load(Ordering::Acquire), 4);
        assert_eq!(shared.resume_count.load(Ordering::Acquire), 4);

        // --- Post-snapshot verification ---

        // Verify ch2's queued write (0xBB at sector 1) was replayed.
        let verify_buf = shared_buffer(SECTOR_SIZE);
        ch2.add_read(1, 1, verify_buf.clone(), 50);
        ch2.submit().unwrap();
        let results = ch2.poll();
        assert_eq!(results, vec![(50, true)]);
        assert_eq!(verify_buf.borrow().as_slice()[0], 0xBB);

        // Verify ch3's queued read (sector 0, written as 0xAA before snapshot).
        assert_eq!(read_buf.borrow().as_slice()[0], 0xAA);

        // Verify original data at sector 0 is intact.
        let verify_buf2 = shared_buffer(SECTOR_SIZE);
        ch1.add_read(0, 1, verify_buf2.clone(), 60);
        ch1.submit().unwrap();
        let results = ch1.poll();
        assert_eq!(results, vec![(60, true)]);
        assert_eq!(verify_buf2.borrow().as_slice()[0], 0xAA);
    }

    /// Multi-channel drain with staggered channel drain timing.
    ///
    /// Tests that the coordinator correctly waits for ALL channels even when
    /// they drain at very different times. Channels 1 and 2 drain immediately,
    /// while channels 3 and 4 drain later after queuing additional I/O.
    /// Also verifies that multiple snapshots can be performed in sequence.
    #[test]
    fn test_multi_channel_staggered_drain_and_repeat() {
        let base = TestBlockDevice::new(4 * SECTOR_SIZE as u64);
        let snapshot_dev = SnapshotBlockDevice::new(Box::new(base));
        let shared = snapshot_dev.shared.clone();

        let mut ch1 = snapshot_dev.create_channel().unwrap();
        let mut ch2 = snapshot_dev.create_channel().unwrap();
        let mut ch3 = snapshot_dev.create_channel().unwrap();

        // --- First snapshot ---
        let handle = snapshot_dev.snapshot_handle();
        let swap_count = Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let swap_count2 = swap_count.clone();

        let coord = std::thread::spawn(move || {
            handle.trigger_snapshot(|| {
                swap_count2.fetch_add(1, Ordering::SeqCst);
                Ok(())
            })
        });

        while shared.state() == STATE_IDLE {
            std::thread::yield_now();
        }

        // Ch1 drains immediately.
        ch1.poll();
        assert_eq!(shared.drain_count.load(Ordering::Acquire), 1);

        // Ch2 queues I/O then drains.
        let buf = shared_buffer(SECTOR_SIZE);
        buf.borrow_mut().as_mut_slice().fill(0x11);
        ch2.add_write(0, 1, buf.clone(), 200);
        ch2.poll();
        assert_eq!(shared.drain_count.load(Ordering::Acquire), 2);

        // Ch3 queues multiple operations then drains (last to drain).
        let buf2 = shared_buffer(SECTOR_SIZE);
        buf2.borrow_mut().as_mut_slice().fill(0x22);
        ch3.add_write(1, 1, buf2.clone(), 300);
        ch3.add_write(2, 1, buf2.clone(), 301);
        ch3.add_flush(302);
        ch3.poll();

        // All drained.
        assert_eq!(shared.drain_count.load(Ordering::Acquire), 3);

        // Wait for RESUMING.
        while shared.state() != STATE_RESUMING {
            std::thread::yield_now();
        }

        // Resume all channels.
        ch1.poll();
        ch2.poll();
        ch3.poll();

        let result = coord.join().unwrap();
        assert!(result.is_ok());
        assert_eq!(swap_count.load(Ordering::SeqCst), 1);
        assert_eq!(shared.state(), STATE_IDLE);

        // Verify ch2's queued write landed (0x11 at sector 0).
        let verify = shared_buffer(SECTOR_SIZE);
        ch2.add_read(0, 1, verify.clone(), 400);
        ch2.submit().unwrap();
        let results = ch2.poll();
        assert_eq!(results, vec![(400, true)]);
        assert_eq!(verify.borrow().as_slice()[0], 0x11);

        // Verify ch3's queued writes landed (0x22 at sectors 1 and 2).
        let verify2 = shared_buffer(SECTOR_SIZE);
        ch3.add_read(1, 1, verify2.clone(), 401);
        ch3.submit().unwrap();
        ch3.poll();
        assert_eq!(verify2.borrow().as_slice()[0], 0x22);

        let verify3 = shared_buffer(SECTOR_SIZE);
        ch3.add_read(2, 1, verify3.clone(), 402);
        ch3.submit().unwrap();
        ch3.poll();
        assert_eq!(verify3.borrow().as_slice()[0], 0x22);

        // --- Second snapshot: verify the mechanism resets correctly ---
        let handle2 = snapshot_dev.snapshot_handle();
        let swap_count3 = swap_count.clone();
        let coord2 = std::thread::spawn(move || {
            handle2.trigger_snapshot(|| {
                swap_count3.fetch_add(1, Ordering::SeqCst);
                Ok(())
            })
        });

        while shared.state() == STATE_IDLE {
            std::thread::yield_now();
        }

        // All 3 channels drain.
        ch1.poll();
        ch2.poll();
        ch3.poll();

        while shared.state() != STATE_RESUMING {
            std::thread::yield_now();
        }

        ch1.poll();
        ch2.poll();
        ch3.poll();

        let result = coord2.join().unwrap();
        assert!(result.is_ok());
        assert_eq!(swap_count.load(Ordering::SeqCst), 2);
        assert_eq!(shared.state(), STATE_IDLE);

        // Data from first snapshot is still readable.
        let verify_final = shared_buffer(SECTOR_SIZE);
        ch1.add_read(0, 1, verify_final.clone(), 500);
        ch1.submit().unwrap();
        ch1.poll();
        assert_eq!(verify_final.borrow().as_slice()[0], 0x11);
    }
}
