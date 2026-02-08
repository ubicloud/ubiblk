use super::{
    metadata::shared_state::SharedMetadataState, metadata_flusher::MetadataFlusher,
    stripe_fetcher::StripeFetcher,
};

use crate::{
    block_device::{
        bdev_ops::{
            device::OpsRequest,
            operation::{OperationContext, StripeOperation},
            shared_state::{OpsSharedState, NORMAL, OPERATING},
        },
        BlockDevice, IoChannel,
    },
    stripe_source::StripeSource,
    Result,
};
use log::{error, info};
use std::{
    collections::VecDeque,
    sync::mpsc::{Receiver, TryRecvError},
};

pub enum BgWorkerRequest {
    Fetch { stripe_id: usize },
    SetWritten { stripe_id: usize },
    StartOperation { operation: Box<dyn StripeOperation> },
    CancelOperation,
    Shutdown,
}

struct ActiveOperation {
    operation: Box<dyn StripeOperation>,
    next_stripe: usize,
    priority_queue: VecDeque<usize>,
}

pub struct BgWorker {
    stripe_fetcher: StripeFetcher,
    metadata_flusher: MetadataFlusher,
    req_receiver: Receiver<BgWorkerRequest>,
    metadata_state: SharedMetadataState,
    done: bool,
    // Operation support
    ops_shared: Option<OpsSharedState>,
    ops_request_receiver: Option<Receiver<OpsRequest>>,
    active_operation: Option<ActiveOperation>,
    target_dev: Box<dyn BlockDevice>,
    ops_target_channel: Option<Box<dyn IoChannel>>,
    stripe_count: usize,
    stripe_sector_count_shift: u8,
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
        let stripe_sector_count_shift = metadata_state.stripe_sector_count_shift();
        let stripe_count = target_dev.sector_count().div_ceil(stripe_sector_count) as usize;
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
            ops_shared: None,
            ops_request_receiver: None,
            active_operation: None,
            target_dev: target_dev.clone(),
            ops_target_channel: None,
            stripe_count,
            stripe_sector_count_shift,
        })
    }

    /// Set up operation support. Call this after construction if the device
    /// stack includes an `OpsBlockDevice`.
    pub fn set_ops_support(
        &mut self,
        ops_shared: OpsSharedState,
        ops_request_receiver: Receiver<OpsRequest>,
    ) {
        self.ops_shared = Some(ops_shared);
        self.ops_request_receiver = Some(ops_request_receiver);
    }

    pub fn shared_state(&self) -> SharedMetadataState {
        self.metadata_state.clone()
    }

    fn operation_active(&self) -> bool {
        self.active_operation.is_some()
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
                self.begin_operation(operation);
            }
            BgWorkerRequest::CancelOperation => {
                self.cancel_operation();
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

    /// Receive priority processing requests from OpsIoChannels.
    fn receive_ops_requests(&mut self) {
        let receiver = match &self.ops_request_receiver {
            Some(r) => r,
            None => return,
        };
        let active = match &mut self.active_operation {
            Some(a) => a,
            None => return,
        };

        loop {
            match receiver.try_recv() {
                Ok(OpsRequest::PriorityProcess { stripe_id }) => {
                    active.priority_queue.push_back(stripe_id);
                }
                Err(TryRecvError::Disconnected) => break,
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
        while !self.done {
            let busy = self.stripe_fetcher.busy()
                || self.metadata_flusher.busy()
                || self.operation_active();
            let block = !busy;
            self.receive_requests(block);
            self.receive_ops_requests();
            self.update();
            self.update_operation();
        }
    }

    // --- Operation lifecycle ---

    fn begin_operation(&mut self, mut operation: Box<dyn StripeOperation>) {
        let ops_shared = match &self.ops_shared {
            Some(s) => s.clone(),
            None => {
                error!("StartOperation received but ops support not configured");
                return;
            }
        };

        let op_name = operation.name().to_string();
        info!("Beginning operation '{}': draining pipelines", op_name);

        // 1. Set gate_reads for this operation
        ops_shared.set_gate_reads(operation.gate_reads());

        // 2. Drain own in-flight fetches and metadata flushes
        while self.stripe_fetcher.busy() || self.metadata_flusher.busy() {
            self.update();
        }

        // 3. Wait for all frontend channels to drain
        loop {
            let drained = ops_shared.channels_drained();
            let total = ops_shared.num_channels();
            if drained >= total {
                break;
            }
            self.receive_requests(false);
            self.update();
        }

        info!(
            "Operation '{}': all channels drained, quiescent point reached",
            op_name
        );

        // === QUIESCENT POINT ===

        // 4. Create a target channel for operation use
        let target_channel = match self.target_dev.create_channel() {
            Ok(ch) => ch,
            Err(e) => {
                error!("Failed to create target channel for operation: {}", e);
                self.abort_operation(&mut *operation, &e.to_string(), &ops_shared);
                return;
            }
        };
        self.ops_target_channel = Some(target_channel);

        // 5. Operation-specific setup
        {
            let mut ctx = self.make_operation_context(&ops_shared);
            if let Err(e) = operation.begin(&mut ctx) {
                error!("Operation '{}' begin() failed: {}", op_name, e);
                self.ops_target_channel = None;
                self.abort_operation(&mut *operation, &e.to_string(), &ops_shared);
                return;
            }
        }

        // 6. Lock all stripes
        ops_shared.lock_all_stripes();

        // 7. Create active state
        self.active_operation = Some(ActiveOperation {
            operation,
            next_stripe: 0,
            priority_queue: VecDeque::new(),
        });
        ops_shared.reset_stripes_processed();

        // 8. Transition to Operating
        ops_shared.set_phase(OPERATING);

        // 9. Reset drain barrier for next operation
        ops_shared.reset_drained();

        info!("Operation '{}': entered Operating phase", op_name);
    }

    fn update_operation(&mut self) {
        let ops_shared = match &self.ops_shared {
            Some(s) => s.clone(),
            None => return,
        };

        if self.active_operation.is_none() {
            return;
        }

        if ops_shared.phase() != OPERATING {
            return;
        }

        // Priority stripes first (requested by frontend writes)
        while let Some(stripe_id) = self
            .active_operation
            .as_mut()
            .unwrap()
            .priority_queue
            .pop_front()
        {
            if ops_shared.stripe_locked(stripe_id) {
                self.process_and_unlock_stripe(stripe_id, &ops_shared);
            }
        }

        // Background: process next locked stripe
        let active = self.active_operation.as_mut().unwrap();
        while active.next_stripe < self.stripe_count {
            let s = active.next_stripe;
            active.next_stripe += 1;
            if ops_shared.stripe_locked(s) {
                self.process_and_unlock_stripe(s, &ops_shared);
                break; // one per iteration to stay responsive
            }
        }

        // Check if all done
        if ops_shared.stripes_processed() == self.stripe_count {
            self.complete_operation(&ops_shared);
        }
    }

    fn process_and_unlock_stripe(&mut self, stripe_id: usize, ops_shared: &OpsSharedState) {
        // Split borrows: borrow ops_target_channel and active_operation separately
        let target_channel = self
            .ops_target_channel
            .as_deref_mut()
            .expect("ops_target_channel must be set during active operation");
        let active = self.active_operation.as_mut().unwrap();
        let stripe_sector_count_shift = self.stripe_sector_count_shift;
        let stripe_count = self.stripe_count;

        // 1. Perform operation-specific work
        {
            let mut ctx = OperationContext {
                target_channel,
                stripe_sector_count_shift,
                stripe_count,
                shared: ops_shared,
            };
            if let Err(e) = active.operation.process_stripe(stripe_id, &mut ctx) {
                error!(
                    "Operation '{}' process_stripe({}) failed: {}",
                    active.operation.name(),
                    stripe_id,
                    e
                );
                let err_str = e.to_string();
                drop(ctx);
                self.abort_operation_active(&err_str, ops_shared);
                return;
            }
        }

        // Re-borrow after the previous scope ended
        let target_channel = self
            .ops_target_channel
            .as_deref_mut()
            .expect("ops_target_channel must be set during active operation");
        let active = self.active_operation.as_mut().unwrap();

        // 2. Post-process hook BEFORE unlock (critical for rekey dual-key safety)
        {
            let mut ctx = OperationContext {
                target_channel,
                stripe_sector_count_shift,
                stripe_count,
                shared: ops_shared,
            };
            if let Err(e) = active.operation.on_stripe_done(stripe_id, &mut ctx) {
                error!(
                    "Operation '{}' on_stripe_done({}) failed: {}",
                    active.operation.name(),
                    stripe_id,
                    e
                );
                let err_str = e.to_string();
                drop(ctx);
                self.abort_operation_active(&err_str, ops_shared);
                return;
            }
        }

        // 3. Unlock — Release ensures all prior writes are visible
        ops_shared.unlock_stripe(stripe_id);

        // 4. Increment progress
        ops_shared.increment_stripes_processed();
    }

    fn complete_operation(&mut self, ops_shared: &OpsSharedState) {
        let mut active = self.active_operation.take().unwrap();
        let op_name = active.operation.name().to_string();

        {
            let mut ctx = self.make_operation_context(ops_shared);
            if let Err(e) = active.operation.complete(&mut ctx) {
                error!("Operation '{}' complete() failed: {}", op_name, e);
            }
        }

        self.ops_target_channel = None;

        // Return to normal
        ops_shared.set_gate_reads(false);
        ops_shared.set_phase(NORMAL);

        info!("Operation '{}': completed successfully", op_name);
    }

    fn abort_operation(
        &mut self,
        operation: &mut dyn StripeOperation,
        error: &str,
        ops_shared: &OpsSharedState,
    ) {
        let op_name = operation.name().to_string();
        error!("Aborting operation '{}': {}", op_name, error);

        ops_shared.unlock_all_stripes();

        {
            let mut ctx = self.make_operation_context(ops_shared);
            operation.on_failure(error, &mut ctx);
        }

        self.ops_target_channel = None;
        ops_shared.set_gate_reads(false);
        ops_shared.reset_stripes_processed();
        ops_shared.reset_drained();
        ops_shared.set_phase(NORMAL);
    }

    fn abort_operation_active(&mut self, error: &str, ops_shared: &OpsSharedState) {
        let mut active = self.active_operation.take().unwrap();
        self.abort_operation(&mut *active.operation, error, ops_shared);
    }

    fn cancel_operation(&mut self) {
        let ops_shared = match &self.ops_shared {
            Some(s) => s.clone(),
            None => return,
        };

        let active = match &self.active_operation {
            Some(a) => a,
            None => {
                info!("CancelOperation received but no operation active");
                return;
            }
        };

        if !active.operation.supports_cancel() {
            error!(
                "Operation '{}' does not support cancellation",
                active.operation.name()
            );
            return;
        }

        let op_name = active.operation.name().to_string();
        info!("Cancelling operation '{}'", op_name);
        self.abort_operation_active("cancelled by user", &ops_shared);
    }

    fn make_operation_context<'a>(
        &'a mut self,
        ops_shared: &'a OpsSharedState,
    ) -> OperationContext<'a> {
        OperationContext {
            target_channel: self
                .ops_target_channel
                .as_deref_mut()
                .expect("ops_target_channel must be set before making operation context"),
            stripe_sector_count_shift: self.stripe_sector_count_shift,
            stripe_count: self.stripe_count,
            shared: ops_shared,
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
        std::sync::mpsc::Sender<super::OpsRequest>,
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
        bg_worker.set_ops_support(ops_shared.clone(), ops_rx);

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
        std::sync::mpsc::Sender<super::OpsRequest>,
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
        bg_worker.set_ops_support(ops_shared.clone(), ops_rx);

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
}
