use super::{
    metadata::shared_state::SharedMetadataState, metadata_flusher::MetadataFlusher,
    stripe_fetcher::StripeFetcher,
};

use crate::block_device::bdev_lazy::metadata::types::{ops_phase, ops_type, OpsRecoveryInfo};
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

use log::{error, info, warn};
use std::{
    collections::VecDeque,
    path::Path,
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
    metadata_dev: Box<dyn BlockDevice>,
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
            metadata_dev: metadata_dev.clone(),
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
        self.recover_interrupted_operation();

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

        // 6. PERSIST: Set ops state + OPS_LOCKED on all stripes in metadata,
        //    then write ALL metadata sectors to disk and flush.
        //    This must be durable BEFORE volatile state transitions.
        {
            let metadata = self.metadata_flusher.metadata_mut();
            metadata.set_ops_state(
                ops_phase::OPERATING,
                operation.ops_type(),
                operation.ops_id(),
                operation.ops_staging_path(),
            );
            metadata.set_all_ops_locked();
        }
        if let Err(e) = self
            .metadata_flusher
            .metadata_mut()
            .save_to_bdev(&*self.metadata_dev)
        {
            error!("Operation '{}' failed to persist metadata: {}", op_name, e);
            self.metadata_flusher.metadata_mut().clear_ops_state();
            self.ops_target_channel = None;
            self.abort_operation(&mut *operation, &e.to_string(), &ops_shared);
            return;
        }

        // 7. Lock all stripes (volatile)
        ops_shared.lock_all_stripes();

        // 8. Create active state
        self.active_operation = Some(ActiveOperation {
            operation,
            next_stripe: 0,
            priority_queue: VecDeque::new(),
        });
        ops_shared.reset_stripes_processed();

        // 9. Transition to Operating (volatile)
        ops_shared.set_phase(OPERATING);

        // 10. Reset drain barrier for next operation
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

        // 3. PERSIST: Queue durable clear of OPS_LOCKED bit. Wait for the
        //    metadata flusher to complete the write+flush before volatile unlock.
        //    This ensures durability-before-visibility: if we crash after the
        //    volatile unlock but before the next stripe, the cleared bit on disk
        //    means we won't re-process this stripe on recovery.
        self.metadata_flusher.clear_ops_locked(stripe_id);
        while self.metadata_flusher.busy() {
            self.metadata_flusher.update();
        }

        // 4. Unlock (volatile) — Release ensures all prior writes are visible
        ops_shared.unlock_stripe(stripe_id);

        // 5. Increment progress
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

        // PERSIST: Clear ops state on disk before volatile phase transition.
        self.persist_ops_clear(&op_name);

        // Return to normal (volatile)
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

        // PERSIST: Clear ops state on disk before volatile phase transition.
        self.persist_ops_clear(&op_name);

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

    /// Clear ops state in metadata and persist to disk. Called during
    /// complete_operation and abort_operation to ensure the on-disk state
    /// reflects that no operation is in progress before volatile state changes.
    fn persist_ops_clear(&mut self, op_name: &str) {
        let metadata = self.metadata_flusher.metadata_mut();
        metadata.clear_ops_state();
        // Also clear any remaining OPS_LOCKED bits (relevant for abort/cancel
        // where not all stripes were processed and cleared individually).
        for i in 0..metadata.stripe_headers.len() {
            metadata.clear_ops_locked(i);
        }
        if let Err(e) = self
            .metadata_flusher
            .metadata_mut()
            .save_to_bdev(&*self.metadata_dev)
        {
            // Log but don't fail — on next startup, recovery will see
            // ops_phase==OPERATING but the OPS_LOCKED bits may already be
            // partially cleared. Recovery checks for locked stripes and
            // will handle the remaining ones.
            error!(
                "Operation '{}': failed to persist ops clear to metadata: {}",
                op_name, e
            );
        }
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

    // --- Crash recovery ---

    /// Check for an interrupted operation on startup and resume or clear it.
    fn recover_interrupted_operation(&mut self) {
        let recovery_info = match self.metadata_flusher.metadata_mut().ops_recovery_info() {
            Some(info) => info,
            None => return,
        };

        info!(
            "Crash recovery: detected interrupted operation (type={}, id={}, locked_stripes={})",
            recovery_info.ops_type,
            recovery_info.ops_id,
            recovery_info.locked_stripes.len(),
        );

        if recovery_info.locked_stripes.is_empty() {
            info!("Crash recovery: no locked stripes, clearing operation state");
            self.persist_ops_clear("recovery");
            return;
        }

        match recovery_info.ops_type {
            ops_type::SNAPSHOT => self.recover_snapshot(&recovery_info),
            ops_type::REKEY => self.recover_rekey(&recovery_info),
            _ => {
                warn!(
                    "Crash recovery: unknown operation type {}, clearing state",
                    recovery_info.ops_type
                );
                self.persist_ops_clear("recovery-unknown");
            }
        }
    }

    fn recover_snapshot(&mut self, info: &OpsRecoveryInfo) {
        let staging_path = match &info.staging_path {
            Some(path) => path.clone(),
            None => {
                warn!(
                    "Crash recovery: snapshot {} has no staging path, clearing state",
                    info.ops_id
                );
                self.persist_ops_clear("recovery-snapshot-no-path");
                return;
            }
        };

        if !Path::new(&staging_path).exists() {
            warn!(
                "Crash recovery: staging file '{}' missing for snapshot {}, accepting data loss and clearing state",
                staging_path, info.ops_id
            );
            self.persist_ops_clear("recovery-snapshot-missing-staging");
            return;
        }

        info!(
            "Crash recovery: resuming snapshot {} — re-copying {} locked stripes to '{}'",
            info.ops_id,
            info.locked_stripes.len(),
            staging_path,
        );

        let staging_dev = match crate::block_device::SyncBlockDevice::new(
            staging_path.clone().into(),
            false,
            true,
            false,
        ) {
            Ok(dev) => dev,
            Err(e) => {
                error!(
                    "Crash recovery: failed to open staging file '{}': {}, clearing state",
                    staging_path, e
                );
                self.persist_ops_clear("recovery-snapshot-open-failed");
                return;
            }
        };

        let mut staging_channel = match staging_dev.create_channel() {
            Ok(ch) => ch,
            Err(e) => {
                error!(
                    "Crash recovery: failed to create staging channel: {}, clearing state",
                    e
                );
                self.persist_ops_clear("recovery-snapshot-channel-failed");
                return;
            }
        };

        let mut target_channel = match self.target_dev.create_channel() {
            Ok(ch) => ch,
            Err(e) => {
                error!(
                    "Crash recovery: failed to create target channel: {}, clearing state",
                    e
                );
                self.persist_ops_clear("recovery-snapshot-target-channel-failed");
                return;
            }
        };

        let stripe_size_sectors = 1u64 << self.stripe_sector_count_shift;
        let timeout = std::time::Duration::from_secs(30);
        let mut recovered = 0;

        for &stripe_id in &info.locked_stripes {
            let offset = (stripe_id as u64) * stripe_size_sectors;
            let sector_count = stripe_size_sectors as u32;
            let buf_size = sector_count as usize * crate::backends::SECTOR_SIZE;
            let buf = crate::block_device::shared_buffer(buf_size);

            let read_id = stripe_id * 3;
            target_channel.add_read(offset, sector_count, buf.clone(), read_id);
            if let Err(e) = target_channel.submit() {
                error!(
                    "Crash recovery: target read submit failed for stripe {}: {}",
                    stripe_id, e
                );
                break;
            }
            if let Err(e) =
                crate::block_device::wait_for_completion(target_channel.as_mut(), read_id, timeout)
            {
                error!(
                    "Crash recovery: target read failed for stripe {}: {}",
                    stripe_id, e
                );
                break;
            }

            let write_id = stripe_id * 3 + 1;
            staging_channel.add_write(offset, sector_count, buf, write_id);
            if let Err(e) = staging_channel.submit() {
                error!(
                    "Crash recovery: staging write submit failed for stripe {}: {}",
                    stripe_id, e
                );
                break;
            }
            if let Err(e) = crate::block_device::wait_for_completion(
                staging_channel.as_mut(),
                write_id,
                timeout,
            ) {
                error!(
                    "Crash recovery: staging write failed for stripe {}: {}",
                    stripe_id, e
                );
                break;
            }

            let flush_id = stripe_id * 3 + 2;
            staging_channel.add_flush(flush_id);
            if let Err(e) = staging_channel.submit() {
                error!(
                    "Crash recovery: staging flush submit failed for stripe {}: {}",
                    stripe_id, e
                );
                break;
            }
            if let Err(e) = crate::block_device::wait_for_completion(
                staging_channel.as_mut(),
                flush_id,
                timeout,
            ) {
                error!(
                    "Crash recovery: staging flush failed for stripe {}: {}",
                    stripe_id, e
                );
                break;
            }

            self.metadata_flusher.clear_ops_locked(stripe_id);
            while self.metadata_flusher.busy() {
                self.metadata_flusher.update();
            }

            recovered += 1;
        }

        if recovered == info.locked_stripes.len() {
            info!(
                "Crash recovery: snapshot {} complete — {} stripes recovered",
                info.ops_id, recovered
            );
        } else {
            error!(
                "Crash recovery: snapshot {} partially recovered ({}/{} stripes), clearing remaining locks",
                info.ops_id, recovered, info.locked_stripes.len()
            );
        }

        self.persist_ops_clear("recovery-snapshot");
    }

    fn recover_rekey(&mut self, info: &OpsRecoveryInfo) {
        warn!(
            "Crash recovery: interrupted rekey operation (id={}, {} locked stripes). \
             Rekey cannot be automatically resumed — key material is not persisted. \
             Clearing operation state; locked stripes retain old encryption key.",
            info.ops_id,
            info.locked_stripes.len(),
        );
        self.persist_ops_clear("recovery-rekey");
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

    fn build_bg_worker_with_ops_and_metadata_dev() -> (
        BgWorker,
        std::sync::mpsc::Sender<BgWorkerRequest>,
        OpsSharedState,
        std::sync::mpsc::Sender<super::OpsRequest>,
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
        bg_worker.set_ops_support(ops_shared.clone(), ops_rx);

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

        let (tx, rx) = channel();

        let bg_worker = BgWorker::new(
            stripe_source,
            &target_dev,
            &metadata_dev,
            4096,
            false,
            metadata_state,
            rx,
        )
        .unwrap();

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

        let (tx, rx) = channel();
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
