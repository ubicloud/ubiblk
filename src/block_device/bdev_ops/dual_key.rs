use crate::block_device::{IoChannel, SharedBuffer};
use crate::crypt::XtsBlockCipher;
use crate::Result;

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

/// Per-stripe tracking of which key to use during online rekey.
///
/// Each stripe starts as `false` (old key). When the bgworker finishes
/// rekeying a stripe, it calls `mark_rekeyed(stripe_id)` — which stores
/// `true` with `Release` ordering — **before** the stripe lock is released.
///
/// Frontend threads observe the rekeyed flag via `is_rekeyed(stripe_id)`
/// with `Acquire` ordering, synchronized through the stripe lock's
/// Release/Acquire chain (see unified-ops-architecture.md Appendix A).
pub struct DualKeyState {
    rekeyed: Vec<AtomicBool>,
}

impl DualKeyState {
    pub fn new(stripe_count: usize) -> Self {
        let mut rekeyed = Vec::with_capacity(stripe_count);
        for _ in 0..stripe_count {
            rekeyed.push(AtomicBool::new(false));
        }
        DualKeyState { rekeyed }
    }

    /// Mark a stripe as rekeyed. Called by `RekeyOperation::on_stripe_done()`
    /// while the stripe is still locked (before unlock).
    pub fn mark_rekeyed(&self, stripe_id: usize) {
        self.rekeyed[stripe_id].store(true, Ordering::Release);
    }

    /// Check if a stripe has been rekeyed. Called by `DualKeyCryptIoChannel`
    /// on frontend threads.
    pub fn is_rekeyed(&self, stripe_id: usize) -> bool {
        self.rekeyed[stripe_id].load(Ordering::Acquire)
    }

    pub fn stripe_count(&self) -> usize {
        self.rekeyed.len()
    }
}

/// Tracks an in-flight read request so we can decrypt it on completion.
struct PendingRead {
    sector_offset: u64,
    sector_count: u32,
    buf: SharedBuffer,
}

/// `DualKeyCryptIoChannel` sits between `OpsIoChannel` and `LazyIoChannel`
/// during an online rekey operation. It holds both old and new XTS ciphers
/// and routes encryption/decryption based on `DualKeyState.rekeyed[stripe_id]`.
///
/// ## Stack position
/// ```text
/// OpsIoChannel
///     |
/// DualKeyCryptIoChannel  <-- this layer
///     |
/// LazyIoChannel
///     |
/// CryptIoChannel         <-- steady-state (bypassed during rekey)
///     |
/// UringIoChannel
/// ```
///
/// ## Ordering proof (from unified-ops-architecture.md Appendix A)
///
/// The `stripe_locks[s].store(false, Release)` on the bgworker happens-after
/// `rekeyed[s].store(true, Release)` (program order). The frontend's
/// `stripe_locks[s].load(Acquire)` synchronizes-with, establishing that
/// subsequent `rekeyed[s].load(Acquire)` observes `true`. Therefore, reads
/// to an unlocked-and-rekeyed stripe always use the new key.
pub struct DualKeyCryptIoChannel {
    base: Box<dyn IoChannel>,
    old_xts: XtsBlockCipher,
    new_xts: XtsBlockCipher,
    dual_key_state: Arc<DualKeyState>,
    stripe_sector_count_shift: u8,
    /// Tracks in-flight reads by request ID so we can decrypt on completion.
    pending_reads: Vec<Option<PendingRead>>,
}

impl DualKeyCryptIoChannel {
    pub fn new(
        base: Box<dyn IoChannel>,
        old_xts: XtsBlockCipher,
        new_xts: XtsBlockCipher,
        dual_key_state: Arc<DualKeyState>,
        stripe_sector_count_shift: u8,
    ) -> Self {
        DualKeyCryptIoChannel {
            base,
            old_xts,
            new_xts,
            dual_key_state,
            stripe_sector_count_shift,
            pending_reads: Vec::new(),
        }
    }

    fn sector_to_stripe(&self, sector: u64) -> usize {
        (sector >> self.stripe_sector_count_shift) as usize
    }

    /// Select the correct cipher for the given sector's stripe.
    fn select_cipher_mut(&mut self, sector_offset: u64) -> &mut XtsBlockCipher {
        let stripe_id = self.sector_to_stripe(sector_offset);
        if self.dual_key_state.is_rekeyed(stripe_id) {
            &mut self.new_xts
        } else {
            &mut self.old_xts
        }
    }
}

impl IoChannel for DualKeyCryptIoChannel {
    fn add_read(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        // Store the read request so we can decrypt on completion.
        if id >= self.pending_reads.len() {
            self.pending_reads.resize_with(id + 1, || None);
        }
        self.pending_reads[id] = Some(PendingRead {
            sector_offset,
            sector_count,
            buf: buf.clone(),
        });
        self.base.add_read(sector_offset, sector_count, buf, id);
    }

    fn add_write(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        // Encrypt with the correct key before writing.
        let cipher = self.select_cipher_mut(sector_offset);
        cipher.encrypt(
            buf.borrow_mut().as_mut_slice(),
            sector_offset,
            sector_count as u64,
        );
        self.base.add_write(sector_offset, sector_count, buf, id);
    }

    fn add_flush(&mut self, id: usize) {
        self.base.add_flush(id);
    }

    fn submit(&mut self) -> Result<()> {
        self.base.submit()
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        let mut results = vec![];
        for (id, success) in self.base.poll() {
            if id < self.pending_reads.len() {
                if let Some(req) = self.pending_reads[id].take() {
                    if success {
                        // Decrypt with the correct key.
                        let stripe_id = self.sector_to_stripe(req.sector_offset);
                        let cipher = if self.dual_key_state.is_rekeyed(stripe_id) {
                            &mut self.new_xts
                        } else {
                            &mut self.old_xts
                        };
                        cipher.decrypt(
                            req.buf.borrow_mut().as_mut_slice(),
                            req.sector_offset,
                            req.sector_count as u64,
                        );
                    }
                    results.push((id, success));
                    continue;
                }
            }
            results.push((id, success));
        }
        results
    }

    fn busy(&self) -> bool {
        self.base.busy()
    }
}

/// `DualKeyCryptBlockDevice` creates `DualKeyCryptIoChannel` instances.
/// Used during online rekey to wrap the base block device.
pub struct DualKeyCryptBlockDevice {
    base: Box<dyn crate::block_device::BlockDevice>,
    old_xts: XtsBlockCipher,
    new_xts: XtsBlockCipher,
    dual_key_state: Arc<DualKeyState>,
    stripe_sector_count_shift: u8,
}

impl DualKeyCryptBlockDevice {
    pub fn new(
        base: Box<dyn crate::block_device::BlockDevice>,
        old_xts: XtsBlockCipher,
        new_xts: XtsBlockCipher,
        dual_key_state: Arc<DualKeyState>,
        stripe_sector_count_shift: u8,
    ) -> Box<Self> {
        Box::new(DualKeyCryptBlockDevice {
            base,
            old_xts,
            new_xts,
            dual_key_state,
            stripe_sector_count_shift,
        })
    }

    pub fn dual_key_state(&self) -> Arc<DualKeyState> {
        self.dual_key_state.clone()
    }
}

impl crate::block_device::BlockDevice for DualKeyCryptBlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>> {
        let base_channel = self.base.create_channel()?;
        Ok(Box::new(DualKeyCryptIoChannel::new(
            base_channel,
            self.old_xts.clone(),
            self.new_xts.clone(),
            self.dual_key_state.clone(),
            self.stripe_sector_count_shift,
        )))
    }

    fn sector_count(&self) -> u64 {
        self.base.sector_count()
    }

    fn clone(&self) -> Box<dyn crate::block_device::BlockDevice> {
        Box::new(DualKeyCryptBlockDevice {
            base: self.base.clone(),
            old_xts: self.old_xts.clone(),
            new_xts: self.new_xts.clone(),
            dual_key_state: self.dual_key_state.clone(),
            stripe_sector_count_shift: self.stripe_sector_count_shift,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backends::SECTOR_SIZE;
    use crate::block_device::{
        bdev_test::TestBlockDevice, shared_buffer, wait_for_completion, BlockDevice,
    };
    use std::time::Duration;

    fn make_test_keys() -> (XtsBlockCipher, XtsBlockCipher) {
        let old = XtsBlockCipher::new(vec![1u8; 32], vec![2u8; 32]).unwrap();
        let new = XtsBlockCipher::new(vec![3u8; 32], vec![4u8; 32]).unwrap();
        (old, new)
    }

    #[test]
    fn dual_key_state_initially_not_rekeyed() {
        let state = DualKeyState::new(4);
        for i in 0..4 {
            assert!(!state.is_rekeyed(i));
        }
    }

    #[test]
    fn dual_key_state_mark_rekeyed() {
        let state = DualKeyState::new(4);
        state.mark_rekeyed(1);
        assert!(!state.is_rekeyed(0));
        assert!(state.is_rekeyed(1));
        assert!(!state.is_rekeyed(2));
    }

    #[test]
    fn write_read_old_key() {
        let (old_xts, new_xts) = make_test_keys();
        let base = TestBlockDevice::new(8 * SECTOR_SIZE as u64); // 8 sectors
        let state = Arc::new(DualKeyState::new(1)); // 1 stripe

        let mut ch = DualKeyCryptIoChannel::new(
            base.create_channel().unwrap(),
            old_xts.clone(),
            new_xts,
            state,
            3, // 8-sector stripes
        );

        // Write plaintext through dual-key channel (should encrypt with old key)
        let buf = shared_buffer(SECTOR_SIZE);
        buf.borrow_mut().as_mut_slice()[0..5].copy_from_slice(b"Hello");
        ch.add_write(0, 1, buf.clone(), 0);
        ch.submit().unwrap();
        wait_for_completion(&mut ch, 0, Duration::from_secs(1)).unwrap();

        // Read back through dual-key channel (should decrypt with old key)
        let read_buf = shared_buffer(SECTOR_SIZE);
        ch.add_read(0, 1, read_buf.clone(), 1);
        ch.submit().unwrap();
        wait_for_completion(&mut ch, 1, Duration::from_secs(1)).unwrap();

        assert_eq!(&read_buf.borrow().as_slice()[0..5], b"Hello");
    }

    #[test]
    fn write_read_new_key_after_rekey() {
        let (old_xts, new_xts) = make_test_keys();
        let base = TestBlockDevice::new(8 * SECTOR_SIZE as u64);
        let state = Arc::new(DualKeyState::new(1));

        let mut ch = DualKeyCryptIoChannel::new(
            base.create_channel().unwrap(),
            old_xts,
            new_xts.clone(),
            state.clone(),
            3,
        );

        // Mark stripe 0 as rekeyed
        state.mark_rekeyed(0);

        // Write plaintext through dual-key channel (should encrypt with new key)
        let buf = shared_buffer(SECTOR_SIZE);
        buf.borrow_mut().as_mut_slice()[0..5].copy_from_slice(b"World");
        ch.add_write(0, 1, buf.clone(), 0);
        ch.submit().unwrap();
        wait_for_completion(&mut ch, 0, Duration::from_secs(1)).unwrap();

        // Read back (should decrypt with new key)
        let read_buf = shared_buffer(SECTOR_SIZE);
        ch.add_read(0, 1, read_buf.clone(), 1);
        ch.submit().unwrap();
        wait_for_completion(&mut ch, 1, Duration::from_secs(1)).unwrap();

        assert_eq!(&read_buf.borrow().as_slice()[0..5], b"World");
    }

    #[test]
    fn mixed_key_state_two_stripes() {
        let (old_xts, new_xts) = make_test_keys();
        let stripe_shift = 3u8; // 8 sectors per stripe
        let base = TestBlockDevice::new(16 * SECTOR_SIZE as u64); // 2 stripes
        let state = Arc::new(DualKeyState::new(2));

        // Mark only stripe 0 as rekeyed
        state.mark_rekeyed(0);

        let mut ch = DualKeyCryptIoChannel::new(
            base.create_channel().unwrap(),
            old_xts,
            new_xts,
            state,
            stripe_shift,
        );

        // Write to stripe 0 (rekeyed -> new key)
        let buf0 = shared_buffer(SECTOR_SIZE);
        buf0.borrow_mut().as_mut_slice()[0..2].copy_from_slice(b"S0");
        ch.add_write(0, 1, buf0.clone(), 0);
        ch.submit().unwrap();
        wait_for_completion(&mut ch, 0, Duration::from_secs(1)).unwrap();

        // Write to stripe 1 (not rekeyed -> old key)
        let buf1 = shared_buffer(SECTOR_SIZE);
        buf1.borrow_mut().as_mut_slice()[0..2].copy_from_slice(b"S1");
        ch.add_write(8, 1, buf1.clone(), 1);
        ch.submit().unwrap();
        wait_for_completion(&mut ch, 1, Duration::from_secs(1)).unwrap();

        // Read back both
        let read0 = shared_buffer(SECTOR_SIZE);
        ch.add_read(0, 1, read0.clone(), 2);
        ch.submit().unwrap();
        wait_for_completion(&mut ch, 2, Duration::from_secs(1)).unwrap();

        let read1 = shared_buffer(SECTOR_SIZE);
        ch.add_read(8, 1, read1.clone(), 3);
        ch.submit().unwrap();
        wait_for_completion(&mut ch, 3, Duration::from_secs(1)).unwrap();

        assert_eq!(&read0.borrow().as_slice()[0..2], b"S0");
        assert_eq!(&read1.borrow().as_slice()[0..2], b"S1");
    }

    #[test]
    fn dual_key_block_device_creates_channels() {
        let (old_xts, new_xts) = make_test_keys();
        let base = TestBlockDevice::new(8 * SECTOR_SIZE as u64);
        let state = Arc::new(DualKeyState::new(1));

        let bdev = DualKeyCryptBlockDevice::new(Box::new(base), old_xts, new_xts, state.clone(), 3);

        assert_eq!(bdev.sector_count(), 8 * SECTOR_SIZE as u64 / 512);

        let mut ch = bdev.create_channel().unwrap();
        let buf = shared_buffer(SECTOR_SIZE);
        buf.borrow_mut().as_mut_slice()[0..4].copy_from_slice(b"test");
        ch.add_write(0, 1, buf.clone(), 0);
        ch.submit().unwrap();
        wait_for_completion(ch.as_mut(), 0, Duration::from_secs(1)).unwrap();

        let read_buf = shared_buffer(SECTOR_SIZE);
        ch.add_read(0, 1, read_buf.clone(), 1);
        ch.submit().unwrap();
        wait_for_completion(ch.as_mut(), 1, Duration::from_secs(1)).unwrap();
        assert_eq!(&read_buf.borrow().as_slice()[0..4], b"test");
    }

    #[test]
    fn flush_passes_through() {
        let (old_xts, new_xts) = make_test_keys();
        let base = TestBlockDevice::new(8 * SECTOR_SIZE as u64);
        let state = Arc::new(DualKeyState::new(1));

        let mut ch =
            DualKeyCryptIoChannel::new(base.create_channel().unwrap(), old_xts, new_xts, state, 3);

        ch.add_flush(0);
        ch.submit().unwrap();
        let results = ch.poll();
        assert_eq!(results, vec![(0, true)]);
    }
}
