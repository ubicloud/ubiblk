use crate::block_device::{shared_buffer, wait_for_completion, BlockDevice, IoChannel};
use crate::Result;

use super::operation::{OperationContext, StripeOperation};

use log::error;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

const IO_TIMEOUT: Duration = Duration::from_secs(30);

/// Wrapper that asserts `Send` for an `IoChannel`.
///
/// SAFETY: The wrapped `IoChannel` is created and used exclusively on the bgworker
/// thread. It is stored in `SnapshotOperation` which is `Send` (so it can be moved
/// to the bgworker thread once), but the channel itself is `!Send` because it may
/// contain `Rc<RefCell<...>>` buffers. The channel is `None` when the operation is
/// sent to the bgworker, populated in `begin()` on the bgworker thread, and only
/// accessed on that same thread for the entire operation lifetime.
struct SendIoChannel(Option<Box<dyn IoChannel>>);

// SAFETY: See doc comment on SendIoChannel.
unsafe impl Send for SendIoChannel {}

/// `SnapshotOperation` implements `StripeOperation` for point-in-time snapshots.
///
/// For each stripe, it reads from the target device and writes to a staging device.
/// After all stripes are copied and unlocked, the staging data can be uploaded or
/// used directly (for LocalFs destinations, the staging file IS the final artifact).
///
/// - `gate_reads()` = `false`: target data is unchanged during copy, reads pass through.
/// - `supports_cancel()` = `true`: cancellation releases locks and discards staging.
pub struct SnapshotOperation {
    staging_device: Box<dyn BlockDevice>,
    staging_channel: SendIoChannel,
    snapshot_id: u64,
    /// Shared with uploader thread: stripes locally copied and flushed to staging.
    stripes_copied: Arc<AtomicUsize>,
    /// Shared with uploader thread: error from upload (if any).
    upload_error: Arc<Mutex<Option<String>>>,
    /// Stripe size in sectors (derived from stripe_sector_count_shift).
    stripe_size_sectors: Option<u64>,
}

impl SnapshotOperation {
    pub fn new(staging_device: Box<dyn BlockDevice>, snapshot_id: u64) -> Self {
        SnapshotOperation {
            staging_device,
            staging_channel: SendIoChannel(None),
            snapshot_id,
            stripes_copied: Arc::new(AtomicUsize::new(0)),
            upload_error: Arc::new(Mutex::new(None)),
            stripe_size_sectors: None,
        }
    }

    /// Returns the shared `stripes_copied` counter for use by an uploader thread.
    pub fn stripes_copied(&self) -> Arc<AtomicUsize> {
        self.stripes_copied.clone()
    }

    /// Returns the shared upload error mutex for use by an uploader thread.
    pub fn upload_error(&self) -> Arc<Mutex<Option<String>>> {
        self.upload_error.clone()
    }

    /// Returns the snapshot ID.
    pub fn snapshot_id(&self) -> u64 {
        self.snapshot_id
    }
}

impl StripeOperation for SnapshotOperation {
    fn name(&self) -> &str {
        "snapshot"
    }

    fn gate_reads(&self) -> bool {
        false
    }

    fn begin(&mut self, ctx: &mut OperationContext) -> Result<()> {
        self.staging_channel.0 = Some(self.staging_device.create_channel()?);
        self.stripe_size_sectors = Some(1u64 << ctx.stripe_sector_count_shift);
        self.stripes_copied.store(0, Ordering::Release);
        Ok(())
    }

    fn process_stripe(&mut self, stripe_id: usize, ctx: &mut OperationContext) -> Result<()> {
        let stripe_size_sectors = self.stripe_size_sectors.unwrap();
        let offset = (stripe_id as u64) * stripe_size_sectors;
        let sector_count = stripe_size_sectors as u32;
        let buf_size = sector_count as usize * 512; // SECTOR_SIZE = 512

        let buf = shared_buffer(buf_size);

        // Read stripe from target device
        let read_id = stripe_id * 3; // unique request IDs per stripe
        ctx.target_channel
            .add_read(offset, sector_count, buf.clone(), read_id);
        ctx.target_channel.submit()?;
        wait_for_completion(ctx.target_channel, read_id, IO_TIMEOUT)?;

        // Write stripe to staging device
        let staging = self
            .staging_channel
            .0
            .as_deref_mut()
            .expect("staging_channel must be set during active operation");
        let write_id = stripe_id * 2;
        staging.add_write(offset, sector_count, buf, write_id);
        staging.submit()?;
        wait_for_completion(staging, write_id, IO_TIMEOUT)?;

        // Flush staging device to ensure durability before unlock
        let flush_id = stripe_id * 2 + 1;
        staging.add_flush(flush_id);
        staging.submit()?;
        wait_for_completion(staging, flush_id, IO_TIMEOUT)?;

        Ok(())
    }

    fn on_stripe_done(&mut self, _stripe_id: usize, _ctx: &mut OperationContext) -> Result<()> {
        // Update shared progress for uploader thread
        self.stripes_copied.fetch_add(1, Ordering::Release);
        Ok(())
    }

    fn complete(&mut self, _ctx: &mut OperationContext) -> Result<()> {
        // Close the staging channel
        self.staging_channel.0 = None;
        // Uploader thread continues independently (if S3).
        // For LocalFs, the staging file is the final artifact — snapshot is done.
        Ok(())
    }

    fn on_failure(&mut self, error: &str, _ctx: &mut OperationContext) {
        self.staging_channel.0 = None;
        // Staging file preserved for retry or cleanup.
        error!("Snapshot {} failed: {}", self.snapshot_id, error);
    }

    fn supports_cancel(&self) -> bool {
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backends::SECTOR_SIZE;
    use crate::block_device::bdev_ops::shared_state::OpsSharedState;
    use crate::block_device::bdev_test::TestBlockDevice;

    #[test]
    fn snapshot_operation_properties() {
        let staging = TestBlockDevice::new(1024 * 1024);
        let op = SnapshotOperation::new(Box::new(staging), 1);

        assert_eq!(op.name(), "snapshot");
        assert!(!op.gate_reads());
        assert!(op.supports_cancel());
        assert_eq!(op.snapshot_id(), 1);
    }

    #[test]
    fn snapshot_begin_creates_staging_channel() {
        let staging = TestBlockDevice::new(1024 * 1024);
        let target = TestBlockDevice::new(1024 * 1024);
        let mut target_ch = target.create_channel().unwrap();
        let ops_shared = OpsSharedState::new(4);

        let mut op = SnapshotOperation::new(Box::new(staging), 1);
        assert!(op.staging_channel.0.is_none());

        let mut ctx = OperationContext {
            target_channel: target_ch.as_mut(),
            stripe_sector_count_shift: 3, // 8 sectors per stripe
            stripe_count: 4,
            shared: &ops_shared,
        };
        op.begin(&mut ctx).unwrap();
        assert!(op.staging_channel.0.is_some());
    }

    #[test]
    fn snapshot_process_stripe_copies_data() {
        let stripe_sector_count_shift = 3u8; // 8 sectors per stripe = 4096 bytes
        let stripe_size = (1u64 << stripe_sector_count_shift) as usize * SECTOR_SIZE;
        let num_stripes = 4;
        let dev_size = (stripe_size * num_stripes) as u64;

        let target = TestBlockDevice::new(dev_size);
        let staging = TestBlockDevice::new(dev_size);

        // Write known data to target stripe 0
        let pattern = vec![0xAB; stripe_size];
        target.write(0, &pattern, stripe_size);

        let mut target_ch = target.create_channel().unwrap();
        let ops_shared = OpsSharedState::new(num_stripes);

        let mut op = SnapshotOperation::new(staging.clone(), 1);
        let mut ctx = OperationContext {
            target_channel: target_ch.as_mut(),
            stripe_sector_count_shift,
            stripe_count: num_stripes,
            shared: &ops_shared,
        };

        op.begin(&mut ctx).unwrap();
        op.process_stripe(0, &mut ctx).unwrap();

        // Verify staging has the same data
        let mut read_back = vec![0u8; stripe_size];
        staging.read(0, &mut read_back, stripe_size);
        assert_eq!(read_back, pattern);
    }

    #[test]
    fn snapshot_on_stripe_done_increments_counter() {
        let staging = TestBlockDevice::new(1024 * 1024);
        let target = TestBlockDevice::new(1024 * 1024);
        let mut target_ch = target.create_channel().unwrap();
        let ops_shared = OpsSharedState::new(4);

        let mut op = SnapshotOperation::new(Box::new(staging), 1);
        let counter = op.stripes_copied();
        assert_eq!(counter.load(Ordering::Acquire), 0);

        let mut ctx = OperationContext {
            target_channel: target_ch.as_mut(),
            stripe_sector_count_shift: 3,
            stripe_count: 4,
            shared: &ops_shared,
        };
        op.begin(&mut ctx).unwrap();
        op.on_stripe_done(0, &mut ctx).unwrap();
        assert_eq!(counter.load(Ordering::Acquire), 1);

        op.on_stripe_done(1, &mut ctx).unwrap();
        assert_eq!(counter.load(Ordering::Acquire), 2);
    }

    #[test]
    fn snapshot_complete_closes_staging_channel() {
        let staging = TestBlockDevice::new(1024 * 1024);
        let target = TestBlockDevice::new(1024 * 1024);
        let mut target_ch = target.create_channel().unwrap();
        let ops_shared = OpsSharedState::new(4);

        let mut op = SnapshotOperation::new(Box::new(staging), 1);
        let mut ctx = OperationContext {
            target_channel: target_ch.as_mut(),
            stripe_sector_count_shift: 3,
            stripe_count: 4,
            shared: &ops_shared,
        };

        op.begin(&mut ctx).unwrap();
        assert!(op.staging_channel.0.is_some());

        op.complete(&mut ctx).unwrap();
        assert!(op.staging_channel.0.is_none());
    }

    #[test]
    fn snapshot_failure_closes_staging_channel() {
        let staging = TestBlockDevice::new(1024 * 1024);
        let target = TestBlockDevice::new(1024 * 1024);
        let mut target_ch = target.create_channel().unwrap();
        let ops_shared = OpsSharedState::new(4);

        let mut op = SnapshotOperation::new(Box::new(staging), 1);
        let mut ctx = OperationContext {
            target_channel: target_ch.as_mut(),
            stripe_sector_count_shift: 3,
            stripe_count: 4,
            shared: &ops_shared,
        };

        op.begin(&mut ctx).unwrap();
        assert!(op.staging_channel.0.is_some());

        op.on_failure("test error", &mut ctx);
        assert!(op.staging_channel.0.is_none());
    }

    #[test]
    fn snapshot_full_lifecycle() {
        let stripe_sector_count_shift = 3u8; // 8 sectors per stripe
        let stripe_size = (1u64 << stripe_sector_count_shift) as usize * SECTOR_SIZE;
        let num_stripes = 4;
        let dev_size = (stripe_size * num_stripes) as u64;

        let target = TestBlockDevice::new(dev_size);
        let staging = TestBlockDevice::new(dev_size);

        // Write distinct patterns to each stripe
        for s in 0..num_stripes {
            let pattern = vec![(s + 1) as u8; stripe_size];
            target.write(s * stripe_size, &pattern, stripe_size);
        }

        let mut target_ch = target.create_channel().unwrap();
        let ops_shared = OpsSharedState::new(num_stripes);

        let mut op = SnapshotOperation::new(staging.clone(), 42);
        let counter = op.stripes_copied();

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

        // Verify all stripes were copied correctly
        assert_eq!(counter.load(Ordering::Acquire), num_stripes);
        for s in 0..num_stripes {
            let expected = vec![(s + 1) as u8; stripe_size];
            let mut actual = vec![0u8; stripe_size];
            staging.read(s * stripe_size, &mut actual, stripe_size);
            assert_eq!(actual, expected, "stripe {s} mismatch");
        }
    }
}
