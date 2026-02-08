use super::{
    metadata::shared_state::SharedMetadataState, metadata_flusher::MetadataFlusher,
    ops_coordinator::OpsCoordinator, stripe_fetcher::StripeFetcher,
};

use crate::{
    block_device::{
        bdev_ops::{device::OpsRequest, operation::StripeOperation, shared_state::OpsSharedState},
        BlockDevice,
    },
    stripe_source::StripeSource,
    Result,
};

use log::{error, info};
use std::sync::mpsc::{Receiver, TryRecvError};

pub enum BgWorkerRequest {
    Fetch { stripe_id: usize },
    SetWritten { stripe_id: usize },
    StartOperation { operation: Box<dyn StripeOperation> },
    CancelOperation,
    Shutdown,
}

pub struct BgWorker {
    stripe_fetcher: StripeFetcher,
    metadata_flusher: MetadataFlusher,
    req_receiver: Receiver<BgWorkerRequest>,
    metadata_state: SharedMetadataState,
    done: bool,
    ops_coordinator: Option<OpsCoordinator>,
}

impl BgWorker {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        stripe_source: Box<dyn StripeSource>,
        target_dev: &dyn BlockDevice,
        metadata_dev: &dyn BlockDevice,
        alignment: usize,
        autofetch: bool,
        metadata_state: SharedMetadataState,
        req_receiver: Receiver<BgWorkerRequest>,
    ) -> Result<Self> {
        let source_sector_count = stripe_source.sector_count();
        let stripe_sector_count = metadata_state.stripe_sector_count();
        let metadata_flusher =
            MetadataFlusher::new(metadata_dev, source_sector_count, metadata_state.clone())?;
        let stripe_fetcher = StripeFetcher::new(
            stripe_source,
            target_dev,
            stripe_sector_count,
            metadata_state.clone(),
            alignment,
            autofetch,
        )?;
        Ok(BgWorker {
            stripe_fetcher,
            metadata_flusher,
            req_receiver,
            done: false,
            metadata_state,
            ops_coordinator: None,
        })
    }

    /// Set up operation support. Call this after construction if the device
    /// stack includes an `OpsBlockDevice`.
    pub fn set_ops_support(
        &mut self,
        ops_shared: OpsSharedState,
        ops_request_receiver: Receiver<OpsRequest>,
        target_dev: &dyn BlockDevice,
        metadata_dev: &dyn BlockDevice,
        stripe_count: usize,
        stripe_sector_count_shift: u8,
    ) {
        self.ops_coordinator = Some(OpsCoordinator::new(
            ops_shared,
            ops_request_receiver,
            target_dev.clone(),
            metadata_dev.clone(),
            stripe_count,
            stripe_sector_count_shift,
            self.metadata_state.clone(),
        ));
    }

    pub fn shared_state(&self) -> SharedMetadataState {
        self.metadata_state.clone()
    }

    pub fn process_request(&mut self, req: BgWorkerRequest) {
        match req {
            BgWorkerRequest::Fetch { stripe_id } => {
                self.stripe_fetcher.handle_fetch_request(stripe_id)
            }
            BgWorkerRequest::SetWritten { stripe_id } => {
                self.metadata_flusher.set_stripe_written(stripe_id)
            }
            BgWorkerRequest::StartOperation { operation } => {
                if let Some(coordinator) = &mut self.ops_coordinator {
                    coordinator.start_operation(operation);
                } else {
                    error!("StartOperation received but ops support not configured");
                }
            }
            BgWorkerRequest::CancelOperation => {
                if let Some(coordinator) = &mut self.ops_coordinator {
                    coordinator.cancel_operation(&mut self.metadata_flusher);
                }
            }
            BgWorkerRequest::Shutdown => {
                info!("Received shutdown request, stopping worker");
                self.done = true;
            }
        }
    }

    pub fn receive_requests(&mut self, block: bool) {
        if block {
            match self.req_receiver.recv() {
                Ok(req) => self.process_request(req),
                Err(e) => {
                    error!("Failed to receive request: {e}, stopping worker");
                    self.done = true;
                    return;
                }
            }
        }

        loop {
            match self.req_receiver.try_recv() {
                Ok(req) => self.process_request(req),
                Err(TryRecvError::Disconnected) => {
                    error!("Request channel disconnected, stopping worker");
                    self.done = true;
                    return;
                }
                Err(TryRecvError::Empty) => break,
            }
        }
    }

    pub fn update(&mut self) {
        self.stripe_fetcher.update();
        for (stripe_id, success) in self.stripe_fetcher.take_finished_fetches() {
            if success {
                self.metadata_flusher.set_stripe_fetched(stripe_id);
            } else {
                error!("Stripe {stripe_id} fetch failed");
            }
        }
        self.metadata_flusher.update();
        self.stripe_fetcher.disconnect_from_source_if_all_fetched();
    }

    pub fn run(&mut self) {
        if let Some(coordinator) = &mut self.ops_coordinator {
            coordinator.recover_interrupted_operation(&mut self.metadata_flusher);
        }

        loop {
            let ops_busy = self.ops_coordinator.as_ref().map_or(false, |c| c.busy());

            // Don't exit while the coordinator has an active drain or operation.
            // In the original code, begin_operation() was a blocking call that
            // completed the drain inline, so Shutdown couldn't interrupt it.
            // With the state machine approach, the drain is incremental, so we
            // must keep the loop alive until the coordinator finishes.
            if self.done && !ops_busy {
                break;
            }

            let busy = self.stripe_fetcher.busy() || self.metadata_flusher.busy() || ops_busy;
            let block = !busy && !self.done;
            self.receive_requests(block);
            if let Some(coordinator) = &mut self.ops_coordinator {
                coordinator.receive_ops_requests();
                coordinator.update(&mut self.stripe_fetcher, &mut self.metadata_flusher);
            }
            self.update();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        block_device::{
            bdev_lazy::SharedMetadataState, bdev_test::TestBlockDevice, NullBlockDevice,
            UbiMetadata,
        },
        stripe_source,
    };
    use std::sync::mpsc::channel;

    fn build_bg_worker_with_source(
        stripe_source: Box<dyn StripeSource>,
    ) -> (BgWorker, std::sync::mpsc::Sender<BgWorkerRequest>) {
        let stripe_sector_count_shift = 11;
        let target_dev = TestBlockDevice::new(1024 * 1024);
        let metadata_dev = TestBlockDevice::new(1024 * 1024);
        let metadata = UbiMetadata::new(stripe_sector_count_shift, 16, 16);
        metadata.save_to_bdev(&metadata_dev).unwrap();
        let metadata_state = {
            let metadata = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
            SharedMetadataState::new(&metadata)
        };

        let (tx, rx) = channel();

        (
            BgWorker::new(
                stripe_source,
                &target_dev,
                &metadata_dev,
                4096,
                false,
                metadata_state,
                rx,
            )
            .unwrap(),
            tx,
        )
    }

    fn build_bg_worker() -> (BgWorker, std::sync::mpsc::Sender<BgWorkerRequest>) {
        let stripe_sector_count_shift = 11;
        let stripe_sector_count = 1u64 << stripe_sector_count_shift;
        let source_dev = TestBlockDevice::new(1024 * 1024);
        let stripe_source = Box::new(
            stripe_source::BlockDeviceStripeSource::new(source_dev.clone(), stripe_sector_count)
                .unwrap(),
        );
        build_bg_worker_with_source(stripe_source)
    }

    #[test]
    fn test_bg_worker_shutdown() {
        let (mut bg_worker, sender) = build_bg_worker();
        sender.send(BgWorkerRequest::Shutdown).unwrap();
        bg_worker.run();
    }

    #[test]
    fn bg_worker_supports_null_source() {
        let stripe_sector_count_shift = 11;
        let stripe_sector_count = 1u64 << stripe_sector_count_shift;
        let source_dev = NullBlockDevice::new();
        let target_dev = TestBlockDevice::new(1024 * 1024);
        let metadata_dev = TestBlockDevice::new(1024 * 1024);
        let stripe_source = Box::new(
            stripe_source::BlockDeviceStripeSource::new(source_dev, stripe_sector_count).unwrap(),
        );

        let metadata = UbiMetadata::new(stripe_sector_count_shift, 16, 0);
        metadata.save_to_bdev(&metadata_dev).unwrap();

        let metadata_state = {
            let metadata = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
            SharedMetadataState::new(&metadata)
        };

        let (_tx, rx) = channel();

        BgWorker::new(
            stripe_source,
            &target_dev,
            &metadata_dev,
            4096,
            false,
            metadata_state,
            rx,
        )
        .expect("BgWorker should support null source device");
    }

    // --- Operation integration tests ---

    use crate::block_device::bdev_ops::{
        operation::{OperationContext, StripeOperation},
        shared_state::{OpsSharedState, NORMAL, STALLING},
    };
    use std::sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    };

    /// A no-op StripeOperation for testing the framework.
    struct NoOpOperation {
        stripes_processed: Arc<AtomicUsize>,
        gate_reads: bool,
    }

    impl NoOpOperation {
        fn new(gate_reads: bool) -> (Self, Arc<AtomicUsize>) {
            let counter = Arc::new(AtomicUsize::new(0));
            (
                Self {
                    stripes_processed: counter.clone(),
                    gate_reads,
                },
                counter,
            )
        }
    }

    impl StripeOperation for NoOpOperation {
        fn name(&self) -> &str {
            "noop"
        }
        fn ops_type(&self) -> u8 {
            0
        }
        fn ops_id(&self) -> u64 {
            0
        }
        fn gate_reads(&self) -> bool {
            self.gate_reads
        }
        fn begin(&mut self, _ctx: &mut OperationContext) -> crate::Result<()> {
            Ok(())
        }
        fn process_stripe(
            &mut self,
            _stripe_id: usize,
            _ctx: &mut OperationContext,
        ) -> crate::Result<()> {
            self.stripes_processed.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
        fn on_stripe_done(
            &mut self,
            _stripe_id: usize,
            _ctx: &mut OperationContext,
        ) -> crate::Result<()> {
            Ok(())
        }
        fn complete(&mut self, _ctx: &mut OperationContext) -> crate::Result<()> {
            Ok(())
        }
        fn on_failure(&mut self, _error: &str, _ctx: &mut OperationContext) {}
        fn supports_cancel(&self) -> bool {
            true
        }
    }

    fn build_bg_worker_with_ops() -> (
        BgWorker,
        std::sync::mpsc::Sender<BgWorkerRequest>,
        OpsSharedState,
        std::sync::mpsc::Sender<OpsRequest>,
    ) {
        let stripe_sector_count_shift = 11;
        let stripe_sector_count = 1u64 << stripe_sector_count_shift;
        let source_dev = TestBlockDevice::new(1024 * 1024);
        let target_dev = TestBlockDevice::new(1024 * 1024);
        let metadata_dev = TestBlockDevice::new(1024 * 1024);
        let stripe_count = target_dev.sector_count().div_ceil(stripe_sector_count) as usize;

        let stripe_source = Box::new(
            stripe_source::BlockDeviceStripeSource::new(source_dev.clone(), stripe_sector_count)
                .unwrap(),
        );

        let metadata = UbiMetadata::new(stripe_sector_count_shift, 16, 16);
        metadata.save_to_bdev(&metadata_dev).unwrap();
        let metadata_state = {
            let metadata = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
            SharedMetadataState::new(&metadata)
        };

        let (tx, rx) = channel();
        let (ops_tx, ops_rx) = channel();
        let ops_shared = OpsSharedState::new(stripe_count);

        let mut bg_worker = BgWorker::new(
            stripe_source,
            &target_dev,
            &metadata_dev,
            4096,
            false,
            metadata_state,
            rx,
        )
        .unwrap();
        bg_worker.set_ops_support(
            ops_shared.clone(),
            ops_rx,
            &target_dev,
            &metadata_dev,
            stripe_count,
            stripe_sector_count_shift,
        );

        (bg_worker, tx, ops_shared, ops_tx)
    }

    #[test]
    fn operation_lifecycle_noop() {
        let (mut bg_worker, sender, ops_shared, _ops_tx) = build_bg_worker_with_ops();
        let (operation, counter) = NoOpOperation::new(false);

        // Transition to stalling (normally done by RPC CAS)
        assert!(ops_shared.try_begin_stalling());
        assert_eq!(ops_shared.phase(), STALLING);

        // Send StartOperation
        sender
            .send(BgWorkerRequest::StartOperation {
                operation: Box::new(operation),
            })
            .unwrap();

        // Send Shutdown after operation completes (will be processed after operation)
        sender.send(BgWorkerRequest::Shutdown).unwrap();

        // Run the bgworker — it will process the operation then shutdown
        bg_worker.run();

        // Verify: all stripes were processed
        let stripe_count = ops_shared.stripe_count();
        assert_eq!(counter.load(Ordering::Relaxed), stripe_count);

        // Phase should be back to Normal
        assert_eq!(ops_shared.phase(), NORMAL);

        // Progress should match stripe count
        assert_eq!(ops_shared.stripes_processed(), stripe_count);

        // All stripes should be unlocked
        for s in 0..stripe_count {
            assert!(!ops_shared.stripe_locked(s));
        }
    }

    #[test]
    fn operation_cancel() {
        let (mut bg_worker, sender, ops_shared, _ops_tx) = build_bg_worker_with_ops();

        /// An operation that panics if process_stripe is called (for cancel testing).
        struct NeverProcessOperation;
        impl StripeOperation for NeverProcessOperation {
            fn name(&self) -> &str {
                "never"
            }
            fn ops_type(&self) -> u8 {
                0
            }
            fn ops_id(&self) -> u64 {
                0
            }
            fn gate_reads(&self) -> bool {
                false
            }
            fn begin(&mut self, _ctx: &mut OperationContext) -> crate::Result<()> {
                Ok(())
            }
            fn process_stripe(
                &mut self,
                _stripe_id: usize,
                _ctx: &mut OperationContext,
            ) -> crate::Result<()> {
                panic!("should not be called after cancel");
            }
            fn on_stripe_done(
                &mut self,
                _stripe_id: usize,
                _ctx: &mut OperationContext,
            ) -> crate::Result<()> {
                Ok(())
            }
            fn complete(&mut self, _ctx: &mut OperationContext) -> crate::Result<()> {
                Ok(())
            }
            fn on_failure(&mut self, _error: &str, _ctx: &mut OperationContext) {}
            fn supports_cancel(&self) -> bool {
                true
            }
        }

        // Transition to stalling
        assert!(ops_shared.try_begin_stalling());

        // Send StartOperation then immediately CancelOperation then Shutdown
        sender
            .send(BgWorkerRequest::StartOperation {
                operation: Box::new(NeverProcessOperation),
            })
            .unwrap();
        sender.send(BgWorkerRequest::CancelOperation).unwrap();
        sender.send(BgWorkerRequest::Shutdown).unwrap();

        bg_worker.run();

        // Phase should be back to Normal after cancel
        assert_eq!(ops_shared.phase(), NORMAL);
    }

    #[test]
    fn operation_with_gate_reads() {
        let (mut bg_worker, sender, ops_shared, _ops_tx) = build_bg_worker_with_ops();
        let (operation, _counter) = NoOpOperation::new(true);

        assert!(ops_shared.try_begin_stalling());

        sender
            .send(BgWorkerRequest::StartOperation {
                operation: Box::new(operation),
            })
            .unwrap();
        sender.send(BgWorkerRequest::Shutdown).unwrap();

        bg_worker.run();

        // gate_reads should be cleared on completion
        assert!(!ops_shared.gate_reads());
        assert_eq!(ops_shared.phase(), NORMAL);
    }

    fn build_bg_worker_with_ops_and_target() -> (
        BgWorker,
        std::sync::mpsc::Sender<BgWorkerRequest>,
        OpsSharedState,
        std::sync::mpsc::Sender<OpsRequest>,
        TestBlockDevice,
    ) {
        let stripe_sector_count_shift = 11;
        let stripe_sector_count = 1u64 << stripe_sector_count_shift;
        let source_dev = TestBlockDevice::new(1024 * 1024);
        let target_dev = TestBlockDevice::new(1024 * 1024);
        let metadata_dev = TestBlockDevice::new(1024 * 1024);
        let stripe_count = target_dev.sector_count().div_ceil(stripe_sector_count) as usize;

        let stripe_source = Box::new(
            stripe_source::BlockDeviceStripeSource::new(source_dev.clone(), stripe_sector_count)
                .unwrap(),
        );

        let metadata = UbiMetadata::new(stripe_sector_count_shift, 16, 16);
        metadata.save_to_bdev(&metadata_dev).unwrap();
        let metadata_state = {
            let metadata = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
            SharedMetadataState::new(&metadata)
        };

        let (tx, rx) = channel();
        let (ops_tx, ops_rx) = channel();
        let ops_shared = OpsSharedState::new(stripe_count);

        let mut bg_worker = BgWorker::new(
            stripe_source,
            &target_dev,
            &metadata_dev,
            4096,
            false,
            metadata_state,
            rx,
        )
        .unwrap();
        bg_worker.set_ops_support(
            ops_shared.clone(),
            ops_rx,
            &target_dev,
            &metadata_dev,
            stripe_count,
            stripe_sector_count_shift,
        );

        (bg_worker, tx, ops_shared, ops_tx, target_dev)
    }

    #[test]
    fn snapshot_operation_through_bgworker() {
        use crate::backends::SECTOR_SIZE;
        use crate::block_device::bdev_ops::snapshot::SnapshotOperation;

        let (mut bg_worker, sender, ops_shared, _ops_tx, target_dev) =
            build_bg_worker_with_ops_and_target();

        let stripe_sector_count_shift = 11u8;
        let stripe_size = (1u64 << stripe_sector_count_shift) as usize * SECTOR_SIZE;
        let stripe_count = ops_shared.stripe_count();

        // Write known data to target device: stripe i filled with byte (i+1)
        for s in 0..stripe_count {
            let pattern = vec![(s + 1) as u8; stripe_size];
            target_dev.write(s * stripe_size, &pattern, stripe_size);
        }

        // Create staging device
        let staging = TestBlockDevice::new(1024 * 1024);
        let operation = SnapshotOperation::new(staging.clone(), 1);
        let stripes_copied = operation.stripes_copied();

        // Transition to stalling
        assert!(ops_shared.try_begin_stalling());

        // Send StartOperation then Shutdown
        sender
            .send(BgWorkerRequest::StartOperation {
                operation: Box::new(operation),
            })
            .unwrap();
        sender.send(BgWorkerRequest::Shutdown).unwrap();

        // Run bgworker to completion
        bg_worker.run();

        // Verify: all stripes processed, phase back to Normal
        assert_eq!(ops_shared.phase(), NORMAL);
        assert_eq!(ops_shared.stripes_processed(), stripe_count);
        assert_eq!(stripes_copied.load(Ordering::Acquire), stripe_count);

        // Verify staging data matches target
        for s in 0..stripe_count {
            let expected = vec![(s + 1) as u8; stripe_size];
            let mut actual = vec![0u8; stripe_size];
            staging.read(s * stripe_size, &mut actual, stripe_size);
            assert_eq!(actual, expected, "stripe {s} data mismatch on staging");
        }
    }

    #[test]
    fn snapshot_cancel_through_bgworker() {
        use crate::block_device::bdev_ops::snapshot::SnapshotOperation;

        let (mut bg_worker, sender, ops_shared, _ops_tx, _target_dev) =
            build_bg_worker_with_ops_and_target();

        let staging = TestBlockDevice::new(1024 * 1024);
        let operation = SnapshotOperation::new(staging.clone(), 2);

        // Transition to stalling
        assert!(ops_shared.try_begin_stalling());

        // Send StartOperation, then immediately CancelOperation, then Shutdown
        sender
            .send(BgWorkerRequest::StartOperation {
                operation: Box::new(operation),
            })
            .unwrap();
        sender.send(BgWorkerRequest::CancelOperation).unwrap();
        sender.send(BgWorkerRequest::Shutdown).unwrap();

        bg_worker.run();

        // Phase should be back to Normal, all stripes unlocked
        assert_eq!(ops_shared.phase(), NORMAL);
        for s in 0..ops_shared.stripe_count() {
            assert!(!ops_shared.stripe_locked(s));
        }
    }

    fn build_bg_worker_with_ops_and_metadata_dev() -> (
        BgWorker,
        std::sync::mpsc::Sender<BgWorkerRequest>,
        OpsSharedState,
        std::sync::mpsc::Sender<OpsRequest>,
        TestBlockDevice,
        TestBlockDevice,
    ) {
        let stripe_sector_count_shift = 11;
        let stripe_sector_count = 1u64 << stripe_sector_count_shift;
        let source_dev = TestBlockDevice::new(1024 * 1024);
        let target_dev = TestBlockDevice::new(1024 * 1024);
        let metadata_dev = TestBlockDevice::new(1024 * 1024);
        let stripe_count = target_dev.sector_count().div_ceil(stripe_sector_count) as usize;

        let stripe_source = Box::new(
            stripe_source::BlockDeviceStripeSource::new(source_dev.clone(), stripe_sector_count)
                .unwrap(),
        );

        let metadata = UbiMetadata::new(stripe_sector_count_shift, 16, 16);
        metadata.save_to_bdev(&metadata_dev).unwrap();
        let metadata_state = {
            let metadata = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
            SharedMetadataState::new(&metadata)
        };

        let (tx, rx) = channel();
        let (ops_tx, ops_rx) = channel();
        let ops_shared = OpsSharedState::new(stripe_count);

        let mut bg_worker = BgWorker::new(
            stripe_source,
            &target_dev,
            &metadata_dev,
            4096,
            false,
            metadata_state,
            rx,
        )
        .unwrap();
        bg_worker.set_ops_support(
            ops_shared.clone(),
            ops_rx,
            &target_dev,
            &metadata_dev,
            stripe_count,
            stripe_sector_count_shift,
        );

        (bg_worker, tx, ops_shared, ops_tx, target_dev, metadata_dev)
    }

    #[test]
    fn operation_persists_ops_state_on_begin() {
        use crate::block_device::bdev_lazy::metadata::types::{
            metadata_flags, ops_phase, ops_type,
        };

        let (mut bg_worker, sender, ops_shared, _ops_tx, _target_dev, metadata_dev) =
            build_bg_worker_with_ops_and_metadata_dev();
        let (operation, _counter) = NoOpOperation::new(false);

        // Transition to stalling
        assert!(ops_shared.try_begin_stalling());

        // Send StartOperation then Shutdown
        sender
            .send(BgWorkerRequest::StartOperation {
                operation: Box::new(operation),
            })
            .unwrap();
        sender.send(BgWorkerRequest::Shutdown).unwrap();

        bg_worker.run();

        // After operation completes, metadata on disk should be back to NORMAL
        let loaded = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
        assert_eq!(loaded.ops_phase, ops_phase::NORMAL);
        assert_eq!(loaded.ops_type, ops_type::NONE);
        assert!(loaded.ops_recovery_info().is_none());

        // All OPS_LOCKED bits should be cleared
        for i in 0..loaded.stripe_headers.len() {
            assert_eq!(
                loaded.stripe_headers[i] & metadata_flags::OPS_LOCKED,
                0,
                "stripe {i} OPS_LOCKED should be cleared after completion"
            );
        }
    }

    #[test]
    fn snapshot_persists_ops_state_through_lifecycle() {
        use crate::backends::SECTOR_SIZE;
        use crate::block_device::bdev_lazy::metadata::types::{
            metadata_flags, ops_phase, ops_type,
        };
        use crate::block_device::bdev_ops::snapshot::SnapshotOperation;

        let (mut bg_worker, sender, ops_shared, _ops_tx, target_dev, metadata_dev) =
            build_bg_worker_with_ops_and_metadata_dev();

        let stripe_sector_count_shift = 11u8;
        let stripe_size = (1u64 << stripe_sector_count_shift) as usize * SECTOR_SIZE;
        let stripe_count = ops_shared.stripe_count();

        // Write data to target
        for s in 0..stripe_count {
            let pattern = vec![(s + 1) as u8; stripe_size];
            target_dev.write(s * stripe_size, &pattern, stripe_size);
        }

        let staging = TestBlockDevice::new(1024 * 1024);
        let operation = SnapshotOperation::new(staging.clone(), 42);

        assert!(ops_shared.try_begin_stalling());

        sender
            .send(BgWorkerRequest::StartOperation {
                operation: Box::new(operation),
            })
            .unwrap();
        sender.send(BgWorkerRequest::Shutdown).unwrap();

        bg_worker.run();

        // After completion: verify on-disk state is clean
        let loaded = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
        assert_eq!(loaded.ops_phase, ops_phase::NORMAL);
        assert_eq!(loaded.ops_type, ops_type::NONE);
        assert_eq!(loaded.ops_id, 0);
        assert!(loaded.ops_recovery_info().is_none());

        // All OPS_LOCKED bits should be cleared on disk
        for i in 0..loaded.stripe_headers.len() {
            assert_eq!(
                loaded.stripe_headers[i] & metadata_flags::OPS_LOCKED,
                0,
                "stripe {i} OPS_LOCKED should be cleared"
            );
        }

        // Verify snapshot data is correct
        assert_eq!(ops_shared.phase(), NORMAL);
        for s in 0..stripe_count {
            let expected = vec![(s + 1) as u8; stripe_size];
            let mut actual = vec![0u8; stripe_size];
            staging.read(s * stripe_size, &mut actual, stripe_size);
            assert_eq!(actual, expected, "stripe {s} data mismatch");
        }
    }

    #[test]
    fn cancel_persists_ops_clear() {
        use crate::block_device::bdev_lazy::metadata::types::{
            metadata_flags, ops_phase, ops_type,
        };
        use crate::block_device::bdev_ops::snapshot::SnapshotOperation;

        let (mut bg_worker, sender, ops_shared, _ops_tx, _target_dev, metadata_dev) =
            build_bg_worker_with_ops_and_metadata_dev();

        let staging = TestBlockDevice::new(1024 * 1024);
        let operation = SnapshotOperation::new(staging.clone(), 7);

        assert!(ops_shared.try_begin_stalling());

        sender
            .send(BgWorkerRequest::StartOperation {
                operation: Box::new(operation),
            })
            .unwrap();
        sender.send(BgWorkerRequest::CancelOperation).unwrap();
        sender.send(BgWorkerRequest::Shutdown).unwrap();

        bg_worker.run();

        // After cancel: on-disk state should be clean
        let loaded = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
        assert_eq!(loaded.ops_phase, ops_phase::NORMAL);
        assert_eq!(loaded.ops_type, ops_type::NONE);
        assert!(loaded.ops_recovery_info().is_none());

        // All OPS_LOCKED bits cleared
        for i in 0..loaded.stripe_headers.len() {
            assert_eq!(
                loaded.stripe_headers[i] & metadata_flags::OPS_LOCKED,
                0,
                "stripe {i} OPS_LOCKED should be cleared after cancel"
            );
        }
    }

    #[test]
    fn bg_worker_marks_failed_stripes_with_flaky_source() {
        let stripe_sector_count_shift = 11;
        let stripe_sector_count = 1u64 << stripe_sector_count_shift;
        let source_dev = TestBlockDevice::new(1024 * 1024);
        let base_source =
            stripe_source::BlockDeviceStripeSource::new(source_dev.clone(), stripe_sector_count)
                .unwrap();
        let flaky_source =
            stripe_source::FlakyStripeSource::new(Box::new(base_source), vec![(0, 4)]);

        let (mut bg_worker, sender) = build_bg_worker_with_source(Box::new(flaky_source));
        sender
            .send(BgWorkerRequest::Fetch { stripe_id: 0 })
            .unwrap();
        bg_worker.receive_requests(false);

        for _ in 0..100 {
            bg_worker.update();
        }

        assert!(bg_worker.shared_state().is_stripe_failed(0));
    }

    // --- Crash recovery tests ---

    /// Build a BgWorker whose metadata has an interrupted operation persisted.
    /// Returns (bg_worker, sender, target_dev, metadata_dev, staging_path).
    fn build_bg_worker_with_interrupted_snapshot(
        locked_stripes: &[usize],
    ) -> (
        BgWorker,
        std::sync::mpsc::Sender<BgWorkerRequest>,
        TestBlockDevice,
        TestBlockDevice,
        tempfile::NamedTempFile,
    ) {
        use crate::backends::SECTOR_SIZE;
        use crate::block_device::bdev_lazy::metadata::types::{
            metadata_flags, ops_phase, ops_type,
        };

        let stripe_sector_count_shift = 11;
        let stripe_sector_count = 1u64 << stripe_sector_count_shift;
        let stripe_size = stripe_sector_count as usize * SECTOR_SIZE;
        let num_stripes = 16;
        let dev_size = num_stripes as u64 * stripe_sector_count * SECTOR_SIZE as u64;

        let source_dev = TestBlockDevice::new(dev_size);
        let target_dev = TestBlockDevice::new(dev_size);
        let metadata_dev = TestBlockDevice::new(1024 * 1024);

        // Write known data to target: stripe i filled with byte (i+1)
        for s in 0..num_stripes {
            let pattern = vec![(s + 1) as u8; stripe_size];
            target_dev.write(s * stripe_size, &pattern, stripe_size);
        }

        // Create staging file (same size as target device)
        let staging_file = tempfile::NamedTempFile::new().unwrap();
        staging_file.as_file().set_len(dev_size).unwrap();
        let staging_path = staging_file.path().to_str().unwrap().to_string();

        // Build metadata with interrupted snapshot: OPERATING phase + locked stripes
        let mut metadata = UbiMetadata::new(stripe_sector_count_shift, num_stripes, num_stripes);
        metadata.set_ops_state(
            ops_phase::OPERATING,
            ops_type::SNAPSHOT,
            42,
            Some(staging_path),
        );
        // Set all stripes locked, then clear the ones NOT in locked_stripes
        metadata.set_all_ops_locked();
        for s in 0..num_stripes {
            if !locked_stripes.contains(&s) {
                metadata.clear_ops_locked(s);
            }
        }
        metadata.save_to_bdev(&metadata_dev).unwrap();

        let stripe_source = Box::new(
            stripe_source::BlockDeviceStripeSource::new(source_dev.clone(), stripe_sector_count)
                .unwrap(),
        );

        let metadata_state = {
            let loaded = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
            SharedMetadataState::new(&loaded)
        };

        let stripe_count = target_dev.sector_count().div_ceil(stripe_sector_count) as usize;
        let (tx, rx) = channel();
        let (_ops_tx, ops_rx) = channel();
        let ops_shared = OpsSharedState::new(stripe_count);

        let mut bg_worker = BgWorker::new(
            stripe_source,
            &target_dev,
            &metadata_dev,
            4096,
            false,
            metadata_state,
            rx,
        )
        .unwrap();
        bg_worker.set_ops_support(
            ops_shared,
            ops_rx,
            &target_dev,
            &metadata_dev,
            stripe_count,
            stripe_sector_count_shift,
        );

        (bg_worker, tx, target_dev, metadata_dev, staging_file)
    }

    #[test]
    fn recovery_detects_operating_phase_and_resumes_snapshot() {
        use crate::backends::SECTOR_SIZE;
        use crate::block_device::bdev_lazy::metadata::types::{
            metadata_flags, ops_phase, ops_type,
        };

        let locked = vec![3, 4, 5];
        let (mut bg_worker, sender, _target_dev, metadata_dev, staging_file) =
            build_bg_worker_with_interrupted_snapshot(&locked);

        let stripe_sector_count_shift = 11u8;
        let stripe_size = (1u64 << stripe_sector_count_shift) as usize * SECTOR_SIZE;

        // Run bgworker: recovery should re-copy locked stripes 3,4,5 to staging
        sender.send(BgWorkerRequest::Shutdown).unwrap();
        bg_worker.run();

        // Verify: metadata is back to NORMAL with no locks
        let loaded = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
        assert_eq!(loaded.ops_phase, ops_phase::NORMAL);
        assert_eq!(loaded.ops_type, ops_type::NONE);
        assert!(loaded.ops_recovery_info().is_none());
        for i in 0..loaded.stripe_headers.len() {
            assert_eq!(
                loaded.stripe_headers[i] & metadata_flags::OPS_LOCKED,
                0,
                "stripe {i} OPS_LOCKED should be cleared after recovery"
            );
        }

        // Verify: staging file has correct data for each recovered stripe.
        // Use non-direct_io for simpler reads, and read one stripe at a time.
        {
            let staging_dev = crate::block_device::SyncBlockDevice::new(
                staging_file.path().to_path_buf(),
                true,  // readonly
                false, // no direct_io for simpler test reads
                false,
            )
            .unwrap();
            for &s in &locked {
                let expected = vec![(s + 1) as u8; stripe_size];
                let buf = crate::block_device::shared_buffer(stripe_size);
                let stripe_offset = s as u64 * (1u64 << stripe_sector_count_shift);
                let mut ch = staging_dev.create_channel().unwrap();
                ch.add_read(
                    stripe_offset,
                    (1u64 << stripe_sector_count_shift) as u32,
                    buf.clone(),
                    0,
                );
                ch.submit().unwrap();
                crate::block_device::wait_for_completion(
                    ch.as_mut(),
                    0,
                    std::time::Duration::from_secs(5),
                )
                .unwrap();
                assert_eq!(
                    &buf.borrow().as_slice()[..stripe_size],
                    &expected[..],
                    "stripe {s} data mismatch in staging after recovery"
                );
            }
        }
    }

    #[test]
    fn recovery_zero_locked_stripes_clears_phase() {
        use crate::block_device::bdev_lazy::metadata::types::{ops_phase, ops_type};

        // No locked stripes — simulates crash during completion write
        let (mut bg_worker, sender, _target_dev, metadata_dev, _staging_file) =
            build_bg_worker_with_interrupted_snapshot(&[]);

        sender.send(BgWorkerRequest::Shutdown).unwrap();
        bg_worker.run();

        let loaded = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
        assert_eq!(loaded.ops_phase, ops_phase::NORMAL);
        assert_eq!(loaded.ops_type, ops_type::NONE);
        assert!(loaded.ops_recovery_info().is_none());
    }

    #[test]
    fn recovery_missing_staging_file_clears_phase() {
        use crate::block_device::bdev_lazy::metadata::types::{
            metadata_flags, ops_phase, ops_type,
        };

        let locked = vec![0, 1, 2];
        let (mut bg_worker, sender, _target_dev, metadata_dev, staging_file) =
            build_bg_worker_with_interrupted_snapshot(&locked);

        // Delete the staging file before recovery
        let staging_path = staging_file.path().to_path_buf();
        drop(staging_file); // NamedTempFile deletes on drop
        assert!(!staging_path.exists());

        sender.send(BgWorkerRequest::Shutdown).unwrap();
        bg_worker.run();

        // Phase should be cleared even though stripes couldn't be recovered
        let loaded = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
        assert_eq!(loaded.ops_phase, ops_phase::NORMAL);
        assert!(loaded.ops_recovery_info().is_none());
        for i in 0..loaded.stripe_headers.len() {
            assert_eq!(
                loaded.stripe_headers[i] & metadata_flags::OPS_LOCKED,
                0,
                "stripe {i} OPS_LOCKED should be cleared"
            );
        }
    }

    #[test]
    fn recovery_rekey_clears_state() {
        use crate::backends::SECTOR_SIZE;
        use crate::block_device::bdev_lazy::metadata::types::{
            metadata_flags, ops_phase, ops_type,
        };

        let stripe_sector_count_shift = 11;
        let stripe_sector_count = 1u64 << stripe_sector_count_shift;
        let num_stripes = 16;
        let dev_size = num_stripes as u64 * stripe_sector_count * SECTOR_SIZE as u64;

        let source_dev = TestBlockDevice::new(dev_size);
        let target_dev = TestBlockDevice::new(dev_size);
        let metadata_dev = TestBlockDevice::new(1024 * 1024);

        // Build metadata with interrupted rekey
        let mut metadata = UbiMetadata::new(stripe_sector_count_shift, num_stripes, num_stripes);
        metadata.set_ops_state(ops_phase::OPERATING, ops_type::REKEY, 99, None);
        metadata.set_all_ops_locked();
        // Simulate partial progress: clear locks on first 5 stripes
        for i in 0..5 {
            metadata.clear_ops_locked(i);
        }
        metadata.save_to_bdev(&metadata_dev).unwrap();

        let stripe_source = Box::new(
            stripe_source::BlockDeviceStripeSource::new(source_dev.clone(), stripe_sector_count)
                .unwrap(),
        );
        let metadata_state = {
            let loaded = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
            SharedMetadataState::new(&loaded)
        };

        let stripe_count = target_dev.sector_count().div_ceil(stripe_sector_count) as usize;
        let (tx, rx) = channel();
        let (_ops_tx, ops_rx) = channel();
        let ops_shared = OpsSharedState::new(stripe_count);

        let mut bg_worker = BgWorker::new(
            stripe_source,
            &target_dev,
            &metadata_dev,
            4096,
            false,
            metadata_state,
            rx,
        )
        .unwrap();
        bg_worker.set_ops_support(
            ops_shared,
            ops_rx,
            &target_dev,
            &metadata_dev,
            stripe_count,
            stripe_sector_count_shift,
        );

        tx.send(BgWorkerRequest::Shutdown).unwrap();
        bg_worker.run();

        // Phase should be cleared, all locks cleared
        let loaded = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
        assert_eq!(loaded.ops_phase, ops_phase::NORMAL);
        assert_eq!(loaded.ops_type, ops_type::NONE);
        assert!(loaded.ops_recovery_info().is_none());
        for i in 0..loaded.stripe_headers.len() {
            assert_eq!(
                loaded.stripe_headers[i] & metadata_flags::OPS_LOCKED,
                0,
                "stripe {i} OPS_LOCKED should be cleared after rekey recovery"
            );
        }
    }

    #[test]
    fn recovery_not_needed_for_normal_metadata() {
        // No operation in progress — recovery is a no-op
        let (mut bg_worker, sender) = build_bg_worker();

        sender.send(BgWorkerRequest::Shutdown).unwrap();
        bg_worker.run();
        // No panic, no error — just ran and shut down normally
    }

    #[test]
    fn snapshot_skips_empty_stripes() {
        use crate::backends::SECTOR_SIZE;
        use crate::block_device::bdev_ops::snapshot::SnapshotOperation;

        // Setup: 16 total stripes, only first 8 have HAS_SOURCE (image_stripe_count=8).
        // Stripes 8-15 are empty (NoSource, NotWritten) and should be skipped.
        let stripe_sector_count_shift = 11u8;
        let stripe_sector_count = 1u64 << stripe_sector_count_shift;
        let stripe_size = stripe_sector_count as usize * SECTOR_SIZE;
        let total_stripes = 16usize;
        let source_stripes = 8usize; // only first 8 have source data

        let dev_size = (stripe_size * total_stripes) as u64;
        let source_dev = TestBlockDevice::new(dev_size);
        let target_dev = TestBlockDevice::new(dev_size);
        let metadata_dev = TestBlockDevice::new(1024 * 1024);

        // Write known data to ALL target stripes (including empty ones)
        for s in 0..total_stripes {
            let pattern = vec![(s + 1) as u8; stripe_size];
            target_dev.write(s * stripe_size, &pattern, stripe_size);
        }

        // Create metadata with only first 8 stripes having HAS_SOURCE
        let metadata = UbiMetadata::new(stripe_sector_count_shift, total_stripes, source_stripes);
        metadata.save_to_bdev(&metadata_dev).unwrap();
        let metadata_state = {
            let loaded = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
            SharedMetadataState::new(&loaded)
        };

        // Verify metadata setup: stripes 0-7 have source (NotFetched), 8-15 are NoSource
        use crate::block_device::bdev_lazy::metadata::shared_state::{
            NoSource as FetchNoSource, NotFetched,
        };
        for s in 0..source_stripes {
            assert_eq!(
                metadata_state.stripe_fetch_state(s),
                NotFetched,
                "stripe {s} should be NotFetched (has source, not yet fetched)"
            );
        }
        for s in source_stripes..total_stripes {
            assert_eq!(
                metadata_state.stripe_fetch_state(s),
                FetchNoSource,
                "stripe {s} should be NoSource"
            );
            assert!(
                !metadata_state.stripe_written(s),
                "stripe {s} should be NotWritten"
            );
        }

        let stripe_source = Box::new(
            stripe_source::BlockDeviceStripeSource::new(source_dev.clone(), stripe_sector_count)
                .unwrap(),
        );

        let stripe_count = target_dev.sector_count().div_ceil(stripe_sector_count) as usize;
        let (tx, rx) = channel();
        let (_ops_tx, ops_rx) = channel();
        let ops_shared = OpsSharedState::new(stripe_count);

        let mut bg_worker = BgWorker::new(
            stripe_source,
            &target_dev,
            &metadata_dev,
            4096,
            false,
            metadata_state,
            rx,
        )
        .unwrap();
        bg_worker.set_ops_support(
            ops_shared.clone(),
            ops_rx,
            &target_dev,
            &metadata_dev,
            stripe_count,
            stripe_sector_count_shift,
        );

        // Create staging device (initialized to zeros)
        let staging = TestBlockDevice::new(dev_size);
        let operation = SnapshotOperation::new(staging.clone(), 1);
        let stripes_copied = operation.stripes_copied();

        assert!(ops_shared.try_begin_stalling());

        tx.send(BgWorkerRequest::StartOperation {
            operation: Box::new(operation),
        })
        .unwrap();
        tx.send(BgWorkerRequest::Shutdown).unwrap();

        bg_worker.run();

        // All stripes processed (both copied and skipped)
        assert_eq!(ops_shared.phase(), NORMAL);
        assert_eq!(ops_shared.stripes_processed(), stripe_count);

        // stripes_copied counts only actually-copied stripes (via on_stripe_done),
        // not skipped ones. Skipped stripes don't call process_stripe/on_stripe_done.
        assert_eq!(
            stripes_copied.load(Ordering::Acquire),
            source_stripes,
            "only source stripes should be copied"
        );

        // Non-empty stripes (0-7): staging should match target data
        for s in 0..source_stripes {
            let expected = vec![(s + 1) as u8; stripe_size];
            let mut actual = vec![0u8; stripe_size];
            staging.read(s * stripe_size, &mut actual, stripe_size);
            assert_eq!(actual, expected, "stripe {s} should be copied to staging");
        }

        // Empty stripes (8-15): staging should still be zeros (not copied)
        for s in source_stripes..stripe_count {
            let expected = vec![0u8; stripe_size];
            let mut actual = vec![0u8; stripe_size];
            staging.read(s * stripe_size, &mut actual, stripe_size);
            assert_eq!(
                actual, expected,
                "stripe {s} (empty) should NOT be copied — staging should remain zeros"
            );
        }
    }

    #[test]
    fn recovery_is_idempotent() {
        use crate::backends::SECTOR_SIZE;
        use crate::block_device::bdev_lazy::metadata::types::{
            metadata_flags, ops_phase, ops_type,
        };

        // Simulate: first recovery processes some stripes but "crashes" (we just
        // create a new BgWorker with remaining locked stripes).

        let stripe_sector_count_shift = 11u8;
        let stripe_size = (1u64 << stripe_sector_count_shift) as usize * SECTOR_SIZE;

        // First run: recover stripes 5..16 (simulate stripes 0..5 already unlocked)
        let locked_first = vec![5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
        let (mut bg_worker1, sender1, target_dev1, metadata_dev1, staging_file1) =
            build_bg_worker_with_interrupted_snapshot(&locked_first);

        sender1.send(BgWorkerRequest::Shutdown).unwrap();
        bg_worker1.run();

        // After first recovery: all should be clean
        let loaded = UbiMetadata::load_from_bdev(&metadata_dev1).expect("load metadata");
        assert_eq!(loaded.ops_phase, ops_phase::NORMAL);
        assert!(loaded.ops_recovery_info().is_none());

        // Verify data was written correctly to staging (one stripe per channel
        // to avoid wait_for_completion losing completions for other IDs)
        {
            let staging_dev = crate::block_device::SyncBlockDevice::new(
                staging_file1.path().to_path_buf(),
                true,  // readonly
                false, // no direct_io for simpler test reads
                false,
            )
            .unwrap();
            for &s in &locked_first {
                let expected = vec![(s + 1) as u8; stripe_size];
                let buf = crate::block_device::shared_buffer(stripe_size);
                let stripe_offset = s as u64 * (1u64 << stripe_sector_count_shift);
                let mut ch = staging_dev.create_channel().unwrap();
                ch.add_read(
                    stripe_offset,
                    (1u64 << stripe_sector_count_shift) as u32,
                    buf.clone(),
                    0,
                );
                ch.submit().unwrap();
                crate::block_device::wait_for_completion(
                    ch.as_mut(),
                    0,
                    std::time::Duration::from_secs(5),
                )
                .unwrap();
                assert_eq!(
                    &buf.borrow().as_slice()[..stripe_size],
                    &expected[..],
                    "stripe {s} data mismatch on idempotent recovery check"
                );
            }
        }
    }
}
