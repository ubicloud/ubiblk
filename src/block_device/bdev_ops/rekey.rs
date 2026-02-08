use crate::block_device::{shared_buffer, wait_for_completion};
use crate::crypt::XtsBlockCipher;
use crate::Result;

use super::dual_key::DualKeyState;
use super::operation::{OperationContext, StripeOperation};
use crate::block_device::bdev_lazy::metadata::types::ops_type;

use log::{error, info};
use std::sync::Arc;
use std::time::Duration;

const IO_TIMEOUT: Duration = Duration::from_secs(30);

/// `RekeyOperation` implements `StripeOperation` for online data key rotation.
///
/// For each stripe, it reads from the target device, decrypts with the old key,
/// re-encrypts with the new key, writes back, and flushes. The critical ordering
/// property is that `on_stripe_done()` advances `DualKeyState.rekeyed[stripe_id]`
/// **before** the stripe lock is released (see unified-ops-architecture.md Section 5.3).
///
/// - `gate_reads()` = `true`: reads must use the correct key, so locked stripes
///   must wait until the bgworker has finished rekeying and switched the cipher.
/// - `supports_cancel()` = `false`: partial rekey leaves mixed-key state on disk.
pub struct RekeyOperation {
    old_xts: XtsBlockCipher,
    new_xts: XtsBlockCipher,
    dual_key_state: Arc<DualKeyState>,
    stripe_size_sectors: Option<u64>,
}

impl RekeyOperation {
    pub fn new(
        old_xts: XtsBlockCipher,
        new_xts: XtsBlockCipher,
        dual_key_state: Arc<DualKeyState>,
    ) -> Self {
        RekeyOperation {
            old_xts,
            new_xts,
            dual_key_state,
            stripe_size_sectors: None,
        }
    }

    pub fn dual_key_state(&self) -> Arc<DualKeyState> {
        self.dual_key_state.clone()
    }
}

impl StripeOperation for RekeyOperation {
    fn name(&self) -> &str {
        "rekey"
    }

    fn ops_type(&self) -> u8 {
        ops_type::REKEY
    }

    fn ops_id(&self) -> u64 {
        // Rekey operations don't have a unique ID — use 0.
        0
    }

    fn gate_reads(&self) -> bool {
        true
    }

    fn begin(&mut self, ctx: &mut OperationContext) -> Result<()> {
        self.stripe_size_sectors = Some(1u64 << ctx.stripe_sector_count_shift);
        info!(
            "Rekey operation beginning: {} stripes, {} sectors/stripe",
            ctx.stripe_count,
            self.stripe_size_sectors.unwrap()
        );
        Ok(())
    }

    fn process_stripe(&mut self, stripe_id: usize, ctx: &mut OperationContext) -> Result<()> {
        let stripe_size_sectors = self.stripe_size_sectors.unwrap();
        let offset = (stripe_id as u64) * stripe_size_sectors;
        let sector_count = stripe_size_sectors as u32;
        let buf_size = sector_count as usize * 512; // SECTOR_SIZE = 512

        let buf = shared_buffer(buf_size);

        // 1. Read from target (encrypted with old key — raw, not through CryptIoChannel)
        let read_id = stripe_id * 3;
        ctx.target_channel
            .add_read(offset, sector_count, buf.clone(), read_id);
        ctx.target_channel.submit()?;
        wait_for_completion(ctx.target_channel, read_id, IO_TIMEOUT)?;

        // 2. Decrypt with old key, re-encrypt with new key (in-place)
        {
            let mut data = buf.borrow_mut();
            self.old_xts
                .decrypt(data.as_mut_slice(), offset, stripe_size_sectors);
            self.new_xts
                .encrypt(data.as_mut_slice(), offset, stripe_size_sectors);
        }

        // 3. Write back to target + flush
        let write_id = stripe_id * 3 + 1;
        ctx.target_channel
            .add_write(offset, sector_count, buf, write_id);
        ctx.target_channel.submit()?;
        wait_for_completion(ctx.target_channel, write_id, IO_TIMEOUT)?;

        let flush_id = stripe_id * 3 + 2;
        ctx.target_channel.add_flush(flush_id);
        ctx.target_channel.submit()?;
        wait_for_completion(ctx.target_channel, flush_id, IO_TIMEOUT)?;

        Ok(())
    }

    fn on_stripe_done(&mut self, stripe_id: usize, _ctx: &mut OperationContext) -> Result<()> {
        // CRITICAL: switch dual-key cipher BEFORE stripe lock is released.
        // After this, any read to this stripe will use the new key.
        // The Release ordering on this store, combined with the Release ordering
        // on stripe_locks[s].store(false) and the frontend's Acquire load on
        // stripe_locks[s], establishes the happens-before chain ensuring the
        // frontend observes rekeyed[s] == true.
        self.dual_key_state.mark_rekeyed(stripe_id);
        Ok(())
    }

    fn complete(&mut self, _ctx: &mut OperationContext) -> Result<()> {
        info!("Rekey operation completed successfully");
        // Config update (persisting new key, removing pending fields) is handled
        // by the RPC layer after this returns.
        Ok(())
    }

    fn on_failure(&mut self, error: &str, _ctx: &mut OperationContext) {
        // Rekey cannot be canceled mid-operation. Persist failure state.
        // Recovery will resume from the last completed stripe on restart.
        error!("Rekey failed: {}. Recovery required on restart.", error);
    }

    fn supports_cancel(&self) -> bool {
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backends::SECTOR_SIZE;
    use crate::block_device::bdev_ops::shared_state::OpsSharedState;
    use crate::block_device::bdev_test::TestBlockDevice;
    use crate::block_device::BlockDevice;

    fn make_test_keys() -> (XtsBlockCipher, XtsBlockCipher) {
        let old = XtsBlockCipher::new(vec![1u8; 32], vec![2u8; 32]).unwrap();
        let new = XtsBlockCipher::new(vec![3u8; 32], vec![4u8; 32]).unwrap();
        (old, new)
    }

    #[test]
    fn rekey_operation_properties() {
        let (old_xts, new_xts) = make_test_keys();
        let state = Arc::new(DualKeyState::new(4));
        let op = RekeyOperation::new(old_xts, new_xts, state);

        assert_eq!(op.name(), "rekey");
        assert!(op.gate_reads());
        assert!(!op.supports_cancel());
    }

    #[test]
    fn rekey_process_stripe_reencrypts() {
        let stripe_sector_count_shift = 3u8; // 8 sectors per stripe
        let stripe_size_sectors = 1u64 << stripe_sector_count_shift;
        let stripe_size_bytes = stripe_size_sectors as usize * SECTOR_SIZE;
        let num_stripes = 2;
        let dev_size = (stripe_size_bytes * num_stripes) as u64;

        let (mut old_xts, new_xts) = make_test_keys();
        let state = Arc::new(DualKeyState::new(num_stripes));

        // Create target device with data encrypted under old key
        let target = TestBlockDevice::new(dev_size);
        let plaintext: Vec<u8> = (0..stripe_size_bytes).map(|i| (i % 251) as u8).collect();
        let mut encrypted = plaintext.clone();
        old_xts.encrypt(&mut encrypted, 0, stripe_size_sectors);
        target.write(0, &encrypted, stripe_size_bytes);

        let mut target_ch = target.create_channel().unwrap();
        let ops_shared = OpsSharedState::new(num_stripes);

        let mut op = RekeyOperation::new(old_xts, new_xts.clone(), state.clone());

        let mut ctx = OperationContext {
            target_channel: target_ch.as_mut(),
            stripe_sector_count_shift,
            stripe_count: num_stripes,
            shared: &ops_shared,
        };

        op.begin(&mut ctx).unwrap();
        op.process_stripe(0, &mut ctx).unwrap();
        op.on_stripe_done(0, &mut ctx).unwrap();

        // Verify: stripe 0 is now encrypted with new key
        assert!(state.is_rekeyed(0));
        assert!(!state.is_rekeyed(1));

        let mut read_back = vec![0u8; stripe_size_bytes];
        target.read(0, &mut read_back, stripe_size_bytes);
        let mut decrypted = read_back.clone();
        let mut new_xts_clone = new_xts.clone();
        new_xts_clone.decrypt(&mut decrypted, 0, stripe_size_sectors);
        assert_eq!(decrypted, plaintext);
    }

    #[test]
    fn rekey_full_lifecycle() {
        let stripe_sector_count_shift = 3u8;
        let stripe_size_sectors = 1u64 << stripe_sector_count_shift;
        let stripe_size_bytes = stripe_size_sectors as usize * SECTOR_SIZE;
        let num_stripes = 4;
        let dev_size = (stripe_size_bytes * num_stripes) as u64;

        let (mut old_xts, new_xts) = make_test_keys();
        let state = Arc::new(DualKeyState::new(num_stripes));

        let target = TestBlockDevice::new(dev_size);

        // Write distinct patterns per stripe, encrypted with old key
        let mut all_plaintext = vec![0u8; stripe_size_bytes * num_stripes];
        for s in 0..num_stripes {
            let pattern: Vec<u8> = (0..stripe_size_bytes)
                .map(|i| ((s + i) % 253) as u8)
                .collect();
            all_plaintext[s * stripe_size_bytes..(s + 1) * stripe_size_bytes]
                .copy_from_slice(&pattern);
        }
        let mut encrypted = all_plaintext.clone();
        let total_sectors = stripe_size_sectors * num_stripes as u64;
        old_xts.encrypt(&mut encrypted, 0, total_sectors);
        target.write(0, &encrypted, stripe_size_bytes * num_stripes);

        let mut target_ch = target.create_channel().unwrap();
        let ops_shared = OpsSharedState::new(num_stripes);

        let mut op = RekeyOperation::new(old_xts, new_xts.clone(), state.clone());

        let mut ctx = OperationContext {
            target_channel: target_ch.as_mut(),
            stripe_sector_count_shift,
            stripe_count: num_stripes,
            shared: &ops_shared,
        };

        op.begin(&mut ctx).unwrap();

        for s in 0..num_stripes {
            op.process_stripe(s, &mut ctx).unwrap();
            op.on_stripe_done(s, &mut ctx).unwrap();
        }

        op.complete(&mut ctx).unwrap();

        // Verify: all stripes rekeyed, decryptable with new key
        for s in 0..num_stripes {
            assert!(state.is_rekeyed(s));
        }

        let mut device_data = vec![0u8; stripe_size_bytes * num_stripes];
        target.read(0, &mut device_data, stripe_size_bytes * num_stripes);
        let mut new_xts_clone = new_xts.clone();
        new_xts_clone.decrypt(&mut device_data, 0, total_sectors);
        assert_eq!(device_data, all_plaintext);
    }

    #[test]
    fn rekey_on_stripe_done_before_complete() {
        let (old_xts, new_xts) = make_test_keys();
        let state = Arc::new(DualKeyState::new(4));
        let target = TestBlockDevice::new(4096);
        let mut target_ch = target.create_channel().unwrap();
        let ops_shared = OpsSharedState::new(4);

        let mut op = RekeyOperation::new(old_xts, new_xts, state.clone());

        let mut ctx = OperationContext {
            target_channel: target_ch.as_mut(),
            stripe_sector_count_shift: 3,
            stripe_count: 4,
            shared: &ops_shared,
        };

        op.begin(&mut ctx).unwrap();

        // on_stripe_done marks the stripe as rekeyed
        assert!(!state.is_rekeyed(2));
        op.on_stripe_done(2, &mut ctx).unwrap();
        assert!(state.is_rekeyed(2));

        // Other stripes still not rekeyed
        assert!(!state.is_rekeyed(0));
        assert!(!state.is_rekeyed(1));
        assert!(!state.is_rekeyed(3));
    }
}
