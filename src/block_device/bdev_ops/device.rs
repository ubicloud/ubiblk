use crate::block_device::{BlockDevice, IoChannel, SharedBuffer};
use crate::Result;

use super::shared_state::{OpsSharedState, NORMAL, OPERATING, STALLING};

use std::collections::VecDeque;
use std::sync::mpsc::Sender;

use log::error;

/// A queued IO request (read or write) waiting for stripe unlock or phase change.
struct QueuedRequest {
    id: usize,
    sector_offset: u64,
    sector_count: u32,
    buf: SharedBuffer,
    stripe_id_first: usize,
    stripe_id_last: usize,
}

/// Message sent from `OpsIoChannel` to the bgworker to request priority processing.
pub enum OpsRequest {
    /// Request the bgworker to process and unlock the given stripe next.
    PriorityProcess { stripe_id: usize },
}

/// `OpsIoChannel` wraps an inner `IoChannel` and gates reads/writes during
/// stripe operations (snapshot, rekey, etc.).
///
/// When no operation is active (phase == Normal), this is a single atomic load
/// on the hot path — pass through to inner channel.
pub struct OpsIoChannel {
    inner: Box<dyn IoChannel>,
    shared: OpsSharedState,
    ops_request_ch: Sender<OpsRequest>,
    queued_writes: VecDeque<QueuedRequest>,
    queued_reads: VecDeque<QueuedRequest>,
    queued_flushes: Vec<usize>,
    stall_signaled: bool,
    stripe_sector_count_shift: u8,
}

impl OpsIoChannel {
    fn sector_to_stripe(&self, sector: u64) -> usize {
        (sector >> self.stripe_sector_count_shift) as usize
    }

    fn all_stripes_unlocked(&self, first: usize, last: usize) -> bool {
        (first..=last).all(|s| !self.shared.stripe_locked(s))
    }

    fn send_priority_for_locked_stripes(&self, first: usize, last: usize) {
        for s in first..=last {
            if self.shared.stripe_locked(s) {
                let _ = self
                    .ops_request_ch
                    .send(OpsRequest::PriorityProcess { stripe_id: s });
            }
        }
    }

    /// Retry queued writes whose stripes are now unlocked.
    fn process_queued_writes(&mut self) {
        let mut forwarded = Vec::new();

        while let Some(front) = self.queued_writes.front() {
            if !self.all_stripes_unlocked(front.stripe_id_first, front.stripe_id_last) {
                break;
            }
            let req = self.queued_writes.pop_front().unwrap();
            self.inner
                .add_write(req.sector_offset, req.sector_count, req.buf, req.id);
            forwarded.push(req.id);
        }

        if !forwarded.is_empty() {
            if let Err(e) = self.inner.submit() {
                error!("Failed to submit {} queued writes: {}", forwarded.len(), e);
            }
        }
    }

    /// Retry queued reads whose stripes are now unlocked.
    fn process_queued_reads(&mut self) {
        let mut forwarded = Vec::new();

        while let Some(front) = self.queued_reads.front() {
            if !self.all_stripes_unlocked(front.stripe_id_first, front.stripe_id_last) {
                break;
            }
            let req = self.queued_reads.pop_front().unwrap();
            self.inner
                .add_read(req.sector_offset, req.sector_count, req.buf, req.id);
            forwarded.push(req.id);
        }

        if !forwarded.is_empty() {
            if let Err(e) = self.inner.submit() {
                error!("Failed to submit {} queued reads: {}", forwarded.len(), e);
            }
        }
    }

    /// Drain any queued flushes (which were held during stalling).
    fn drain_queued_flushes(&mut self) {
        if self.queued_flushes.is_empty() {
            return;
        }
        let flushes: Vec<usize> = self.queued_flushes.drain(..).collect();
        for id in &flushes {
            self.inner.add_flush(*id);
        }
        if let Err(e) = self.inner.submit() {
            error!("Failed to submit {} queued flushes: {}", flushes.len(), e);
        }
    }
}

impl IoChannel for OpsIoChannel {
    fn add_read(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        let phase = self.shared.phase();
        if phase == NORMAL {
            self.inner.add_read(sector_offset, sector_count, buf, id);
            return;
        }

        if phase == STALLING || self.shared.gate_reads() {
            // Queue the read — during stalling all IO is queued,
            // during operating with gate_reads=true reads to locked stripes wait.
            let first = self.sector_to_stripe(sector_offset);
            let last = self.sector_to_stripe(sector_offset + sector_count as u64 - 1);

            // If operating and all stripes unlocked, pass through
            if phase == OPERATING && self.all_stripes_unlocked(first, last) {
                self.inner.add_read(sector_offset, sector_count, buf, id);
                return;
            }

            self.queued_reads.push_back(QueuedRequest {
                id,
                sector_offset,
                sector_count,
                buf,
                stripe_id_first: first,
                stripe_id_last: last,
            });
            return;
        }

        // Operating but gate_reads=false: reads pass through
        self.inner.add_read(sector_offset, sector_count, buf, id);
    }

    fn add_write(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        let phase = self.shared.phase();
        if phase == NORMAL {
            self.inner.add_write(sector_offset, sector_count, buf, id);
            return;
        }

        let first = self.sector_to_stripe(sector_offset);
        let last = self.sector_to_stripe(sector_offset + sector_count as u64 - 1);

        if phase == OPERATING && self.all_stripes_unlocked(first, last) {
            self.inner.add_write(sector_offset, sector_count, buf, id);
            return;
        }

        // Queue the write and request priority processing for locked stripes
        if phase == OPERATING {
            self.send_priority_for_locked_stripes(first, last);
        }

        self.queued_writes.push_back(QueuedRequest {
            id,
            sector_offset,
            sector_count,
            buf,
            stripe_id_first: first,
            stripe_id_last: last,
        });
    }

    fn add_flush(&mut self, id: usize) {
        let phase = self.shared.phase();
        if phase == NORMAL || phase == OPERATING {
            self.inner.add_flush(id);
            return;
        }
        // Stalling: queue flushes until drain completes
        self.queued_flushes.push(id);
    }

    fn submit(&mut self) -> Result<()> {
        self.inner.submit()
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        let phase = self.shared.phase();

        // Retry queued requests when stripes unlock or phase changes
        if phase == OPERATING || phase == NORMAL {
            self.process_queued_writes();
            if phase == NORMAL || self.shared.gate_reads() {
                self.process_queued_reads();
            }
            self.drain_queued_flushes();
        }

        // Drain check during stalling
        if phase == STALLING && !self.stall_signaled && !self.inner.busy() {
            self.shared.signal_drained();
            self.stall_signaled = true;
        }

        // Reset stall signal when returning to normal
        if phase == NORMAL && self.stall_signaled {
            self.stall_signaled = false;
        }

        self.inner.poll()
    }

    fn busy(&self) -> bool {
        self.inner.busy()
            || !self.queued_writes.is_empty()
            || !self.queued_reads.is_empty()
            || !self.queued_flushes.is_empty()
    }
}

impl Drop for OpsIoChannel {
    fn drop(&mut self) {
        self.shared.remove_channel();
        if !self.stall_signaled && self.shared.phase() == STALLING {
            self.shared.signal_drained();
        }
    }
}

/// `OpsBlockDevice` wraps a base `BlockDevice` and creates `OpsIoChannel`
/// instances that gate IO during stripe operations.
pub struct OpsBlockDevice {
    base: Box<dyn BlockDevice>,
    shared: OpsSharedState,
    ops_request_ch: Sender<OpsRequest>,
    stripe_sector_count_shift: u8,
}

impl OpsBlockDevice {
    pub fn new(
        base: Box<dyn BlockDevice>,
        shared: OpsSharedState,
        ops_request_ch: Sender<OpsRequest>,
        stripe_sector_count_shift: u8,
    ) -> Box<Self> {
        Box::new(OpsBlockDevice {
            base,
            shared,
            ops_request_ch,
            stripe_sector_count_shift,
        })
    }

    pub fn shared_state(&self) -> &OpsSharedState {
        &self.shared
    }
}

impl BlockDevice for OpsBlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>> {
        let inner = self.base.create_channel()?;
        self.shared.add_channel();
        Ok(Box::new(OpsIoChannel {
            inner,
            shared: self.shared.clone(),
            ops_request_ch: self.ops_request_ch.clone(),
            queued_writes: VecDeque::new(),
            queued_reads: VecDeque::new(),
            queued_flushes: Vec::new(),
            stall_signaled: false,
            stripe_sector_count_shift: self.stripe_sector_count_shift,
        }))
    }

    fn sector_count(&self) -> u64 {
        self.base.sector_count()
    }

    fn clone(&self) -> Box<dyn BlockDevice> {
        Box::new(OpsBlockDevice {
            base: self.base.clone(),
            shared: self.shared.clone(),
            ops_request_ch: self.ops_request_ch.clone(),
            stripe_sector_count_shift: self.stripe_sector_count_shift,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backends::SECTOR_SIZE;
    use crate::block_device::{bdev_test::TestBlockDevice, shared_buffer};
    use std::sync::mpsc;

    fn setup(stripe_sector_count_shift: u8) -> (Box<OpsBlockDevice>, mpsc::Receiver<OpsRequest>) {
        let base = TestBlockDevice::new(1024 * 1024);
        let stripe_count = base
            .sector_count()
            .div_ceil(1u64 << stripe_sector_count_shift) as usize;
        let shared = OpsSharedState::new(stripe_count);
        let (tx, rx) = mpsc::channel();
        let device = OpsBlockDevice::new(Box::new(base), shared, tx, stripe_sector_count_shift);
        (device, rx)
    }

    #[test]
    fn normal_phase_passthrough() {
        let (device, _rx) = setup(3); // 8-sector stripes
        let mut ch = device.create_channel().unwrap();

        let buf = shared_buffer(SECTOR_SIZE);
        buf.borrow_mut().as_mut_slice()[0..5].copy_from_slice(b"Hello");

        ch.add_write(0, 1, buf.clone(), 1);
        ch.submit().unwrap();
        let results = ch.poll();
        assert_eq!(results, vec![(1, true)]);

        let read_buf = shared_buffer(SECTOR_SIZE);
        ch.add_read(0, 1, read_buf.clone(), 2);
        ch.submit().unwrap();
        let results = ch.poll();
        assert_eq!(results, vec![(2, true)]);
        assert_eq!(&read_buf.borrow().as_slice()[0..5], b"Hello");
    }

    #[test]
    fn stalling_queues_all_io() {
        let (device, _rx) = setup(3);
        let mut ch = device.create_channel().unwrap();

        // Transition to stalling
        assert!(device.shared.try_begin_stalling());

        let buf = shared_buffer(SECTOR_SIZE);
        ch.add_write(0, 1, buf.clone(), 1);
        ch.add_read(0, 1, buf.clone(), 2);
        ch.add_flush(3);
        ch.submit().unwrap();

        // Poll should detect drain (inner not busy) and signal
        let results = ch.poll();
        assert!(results.is_empty()); // queued, not forwarded

        // Writes and reads are queued
        assert!(ch.busy());
    }

    #[test]
    fn drain_signal_on_stall() {
        let (device, _rx) = setup(3);
        let mut ch = device.create_channel().unwrap();

        assert!(device.shared.try_begin_stalling());

        // Inner channel is not busy, poll should signal drain
        let _ = ch.poll();
        assert_eq!(device.shared.channels_drained(), 1);

        // Second poll shouldn't double-signal
        let _ = ch.poll();
        assert_eq!(device.shared.channels_drained(), 1);
    }

    #[test]
    fn operating_gates_writes_on_locked_stripes() {
        let (device, rx) = setup(3);
        let mut ch = device.create_channel().unwrap();

        // Lock stripe 0 and enter operating phase
        device.shared.lock_stripe(0);
        device.shared.set_phase(OPERATING);

        let buf = shared_buffer(SECTOR_SIZE);
        ch.add_write(0, 1, buf.clone(), 1); // sector 0 -> stripe 0 (locked)
        ch.submit().unwrap();

        // Write should be queued, not forwarded
        let results = ch.poll();
        assert!(results.is_empty());
        assert!(ch.busy());

        // Should have sent a priority request for stripe 0
        let msg = rx.try_recv().unwrap();
        match msg {
            OpsRequest::PriorityProcess { stripe_id } => assert_eq!(stripe_id, 0),
        }

        // Unlock stripe 0 -> write should proceed
        device.shared.unlock_stripe(0);
        let results = ch.poll();
        assert_eq!(results, vec![(1, true)]);
    }

    #[test]
    fn operating_passthrough_unlocked_writes() {
        let (device, _rx) = setup(3);
        let mut ch = device.create_channel().unwrap();

        device.shared.set_phase(OPERATING);
        // All stripes unlocked by default

        let buf = shared_buffer(SECTOR_SIZE);
        ch.add_write(0, 1, buf.clone(), 1);
        ch.submit().unwrap();
        let results = ch.poll();
        assert_eq!(results, vec![(1, true)]);
    }

    #[test]
    fn operating_gates_reads_when_gate_reads_true() {
        let (device, _rx) = setup(3);
        let mut ch = device.create_channel().unwrap();

        device.shared.lock_stripe(0);
        device.shared.set_gate_reads(true);
        device.shared.set_phase(OPERATING);

        let buf = shared_buffer(SECTOR_SIZE);
        ch.add_read(0, 1, buf.clone(), 1); // locked + gate_reads=true -> queued
        ch.submit().unwrap();

        let results = ch.poll();
        assert!(results.is_empty());
        assert!(ch.busy());

        // Unlock -> read should proceed
        device.shared.unlock_stripe(0);
        let results = ch.poll();
        assert_eq!(results, vec![(1, true)]);
    }

    #[test]
    fn operating_reads_passthrough_when_gate_reads_false() {
        let (device, _rx) = setup(3);
        let mut ch = device.create_channel().unwrap();

        device.shared.lock_stripe(0);
        device.shared.set_gate_reads(false);
        device.shared.set_phase(OPERATING);

        let buf = shared_buffer(SECTOR_SIZE);
        ch.add_read(0, 1, buf.clone(), 1); // locked but gate_reads=false -> pass through
        ch.submit().unwrap();

        let results = ch.poll();
        assert_eq!(results, vec![(1, true)]);
    }

    #[test]
    fn phase_cas_prevents_concurrent_operations() {
        let (device, _rx) = setup(3);

        assert!(device.shared.try_begin_stalling());
        assert!(!device.shared.try_begin_stalling()); // second attempt fails
    }

    #[test]
    fn channel_count_tracking() {
        let (device, _rx) = setup(3);
        assert_eq!(device.shared.num_channels(), 0);

        let ch1 = device.create_channel().unwrap();
        assert_eq!(device.shared.num_channels(), 1);

        let ch2 = device.create_channel().unwrap();
        assert_eq!(device.shared.num_channels(), 2);

        drop(ch1);
        assert_eq!(device.shared.num_channels(), 1);

        drop(ch2);
        assert_eq!(device.shared.num_channels(), 0);
    }

    #[test]
    fn drop_signals_drain_during_stalling() {
        let (device, _rx) = setup(3);
        let ch = device.create_channel().unwrap();

        assert!(device.shared.try_begin_stalling());
        assert_eq!(device.shared.channels_drained(), 0);

        drop(ch); // Should signal drain on drop
        assert_eq!(device.shared.channels_drained(), 1);
    }

    #[test]
    fn queued_io_drains_on_return_to_normal() {
        let (device, _rx) = setup(3);
        let mut ch = device.create_channel().unwrap();

        // Enter stalling to queue IO
        assert!(device.shared.try_begin_stalling());

        let buf = shared_buffer(SECTOR_SIZE);
        buf.borrow_mut().as_mut_slice()[0..4].copy_from_slice(b"test");
        ch.add_write(0, 1, buf.clone(), 1);
        ch.add_flush(2);

        // Return to normal
        device.shared.set_phase(NORMAL);

        // Poll should drain queued writes and flushes
        let results = ch.poll();
        assert_eq!(results.len(), 2);
        assert!(!ch.busy());
    }

    #[test]
    fn flush_passthrough_during_normal_and_operating() {
        let (device, _rx) = setup(3);
        let mut ch = device.create_channel().unwrap();

        // Normal: flush passes through
        ch.add_flush(1);
        ch.submit().unwrap();
        let results = ch.poll();
        assert_eq!(results, vec![(1, true)]);

        // Operating: flush also passes through
        device.shared.set_phase(OPERATING);
        ch.add_flush(2);
        ch.submit().unwrap();
        let results = ch.poll();
        assert_eq!(results, vec![(2, true)]);
    }
}
