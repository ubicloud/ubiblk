use crate::block_device::bdev_lazy::metadata::shared_state::NoSource;
use crate::block_device::bdev_lazy::metadata::types::{ops_phase, ops_type, OpsRecoveryInfo};
use crate::block_device::{
    bdev_ops::{
        device::OpsRequest,
        operation::{OperationContext, StripeOperation},
        shared_state::{OpsSharedState, NORMAL, OPERATING},
    },
    BlockDevice, IoChannel, SharedMetadataState,
};

use super::metadata_flusher::MetadataFlusher;
use super::stripe_fetcher::StripeFetcher;

use log::{error, info, warn};
use std::{
    collections::VecDeque,
    path::Path,
    sync::mpsc::{Receiver, TryRecvError},
};

struct ActiveOperation {
    operation: Box<dyn StripeOperation>,
    next_stripe: usize,
    priority_queue: VecDeque<usize>,
}

/// Internal state machine for the drain-and-begin sequence.
enum DrainState {
    /// Draining own pipelines (step 2): wait for fetcher + flusher to be idle.
    DrainingPipelines { operation: Box<dyn StripeOperation> },
    /// Waiting for frontend channels to drain (step 3).
    WaitingForChannels { operation: Box<dyn StripeOperation> },
}

/// Coordinator for whole-device stripe operations (snapshot, rekey, etc.).
///
/// Analogous to `StripeFetcher` and `MetadataFlusher`: bgworker owns an
/// `OpsCoordinator` and delegates operation lifecycle to it, keeping bgworker.rs
/// as a thin coordinator with minimal added code.
///
/// The drain protocol uses a state machine so that bgworker's `run()` loop
/// stays responsive (no blocking drain loops inside the coordinator).
pub struct OpsCoordinator {
    ops_shared: OpsSharedState,
    ops_request_receiver: Receiver<OpsRequest>,
    active_operation: Option<ActiveOperation>,
    drain_state: Option<DrainState>,
    target_dev: Box<dyn BlockDevice>,
    metadata_dev: Box<dyn BlockDevice>,
    ops_target_channel: Option<Box<dyn IoChannel>>,
    stripe_count: usize,
    stripe_sector_count_shift: u8,
    metadata_state: SharedMetadataState,
}

impl OpsCoordinator {
    pub fn new(
        ops_shared: OpsSharedState,
        ops_request_receiver: Receiver<OpsRequest>,
        target_dev: Box<dyn BlockDevice>,
        metadata_dev: Box<dyn BlockDevice>,
        stripe_count: usize,
        stripe_sector_count_shift: u8,
        metadata_state: SharedMetadataState,
    ) -> Self {
        OpsCoordinator {
            ops_shared,
            ops_request_receiver,
            active_operation: None,
            drain_state: None,
            target_dev,
            metadata_dev,
            ops_target_channel: None,
            stripe_count,
            stripe_sector_count_shift,
            metadata_state,
        }
    }

    pub fn busy(&self) -> bool {
        self.active_operation.is_some() || self.drain_state.is_some()
    }

    /// Receive priority processing requests from OpsIoChannels.
    pub fn receive_ops_requests(&mut self) {
        let active = match &mut self.active_operation {
            Some(a) => a,
            None => return,
        };

        loop {
            match self.ops_request_receiver.try_recv() {
                Ok(OpsRequest::PriorityProcess { stripe_id }) => {
                    active.priority_queue.push_back(stripe_id);
                }
                Err(TryRecvError::Disconnected) => break,
                Err(TryRecvError::Empty) => break,
            }
        }
    }

    /// Begin draining pipelines for a new operation. The actual drain happens
    /// incrementally in `update()`, so bgworker's run loop stays responsive.
    pub fn start_operation(&mut self, operation: Box<dyn StripeOperation>) {
        let op_name = operation.name().to_string();
        info!("Beginning operation '{}': draining pipelines", op_name);

        // 1. Set gate_reads for this operation
        self.ops_shared.set_gate_reads(operation.gate_reads());

        // Enter drain state machine
        self.drain_state = Some(DrainState::DrainingPipelines { operation });
    }

    /// Drive the drain state machine and operation processing forward.
    /// Called each iteration of bgworker's run loop.
    pub fn update(
        &mut self,
        stripe_fetcher: &mut StripeFetcher,
        metadata_flusher: &mut MetadataFlusher,
    ) {
        // Drive drain state machine if active
        if self.drain_state.is_some() {
            self.update_drain(stripe_fetcher, metadata_flusher);
            return;
        }

        // Drive active operation if any
        if self.active_operation.is_some() {
            self.update_operation(metadata_flusher);
        }
    }

    fn update_drain(
        &mut self,
        stripe_fetcher: &mut StripeFetcher,
        metadata_flusher: &mut MetadataFlusher,
    ) {
        let drain = self.drain_state.take().unwrap();

        match drain {
            DrainState::DrainingPipelines { operation } => {
                if stripe_fetcher.busy() || metadata_flusher.busy() {
                    // Still draining, put state back
                    self.drain_state = Some(DrainState::DrainingPipelines { operation });
                } else {
                    // Pipelines drained, move to waiting for channels
                    self.drain_state = Some(DrainState::WaitingForChannels { operation });
                }
            }
            DrainState::WaitingForChannels { operation } => {
                let drained = self.ops_shared.channels_drained();
                let total = self.ops_shared.num_channels();
                if drained < total {
                    // Still waiting, put state back
                    self.drain_state = Some(DrainState::WaitingForChannels { operation });
                } else {
                    // All channels drained — complete the begin sequence
                    self.finish_begin(operation, metadata_flusher);
                }
            }
        }
    }

    /// Complete the begin sequence after drain is done. This is the non-blocking
    /// part that sets up the operation and transitions to Operating phase.
    fn finish_begin(
        &mut self,
        mut operation: Box<dyn StripeOperation>,
        metadata_flusher: &mut MetadataFlusher,
    ) {
        let op_name = operation.name().to_string();
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
                self.abort_operation(&mut *operation, &e.to_string(), metadata_flusher);
                return;
            }
        };
        self.ops_target_channel = Some(target_channel);

        // 5. Operation-specific setup
        {
            let mut op_ctx = self.make_operation_context();
            if let Err(e) = operation.begin(&mut op_ctx) {
                error!("Operation '{}' begin() failed: {}", op_name, e);
                self.ops_target_channel = None;
                self.abort_operation(&mut *operation, &e.to_string(), metadata_flusher);
                return;
            }
        }

        // 6. PERSIST: Set ops state + OPS_LOCKED on all stripes in metadata,
        //    then write ALL metadata sectors to disk and flush.
        //    This must be durable BEFORE volatile state transitions.
        {
            let metadata = metadata_flusher.metadata_mut();
            metadata.set_ops_state(
                ops_phase::OPERATING,
                operation.ops_type(),
                operation.ops_id(),
                operation.ops_staging_path(),
            );
            metadata.set_all_ops_locked();
        }
        if let Err(e) = metadata_flusher
            .metadata_mut()
            .save_to_bdev(&*self.metadata_dev)
        {
            error!("Operation '{}' failed to persist metadata: {}", op_name, e);
            metadata_flusher.metadata_mut().clear_ops_state();
            self.ops_target_channel = None;
            self.abort_operation(&mut *operation, &e.to_string(), metadata_flusher);
            return;
        }

        // 7. Lock all stripes (volatile)
        self.ops_shared.lock_all_stripes();

        // 8. Create active state
        self.active_operation = Some(ActiveOperation {
            operation,
            next_stripe: 0,
            priority_queue: VecDeque::new(),
        });
        self.ops_shared.reset_stripes_processed();

        // 9. Transition to Operating (volatile)
        self.ops_shared.set_phase(OPERATING);

        // 10. Reset drain barrier for next operation
        self.ops_shared.reset_drained();

        info!("Operation '{}': entered Operating phase", op_name);
    }

    /// Check if a stripe is empty (no source data and never written by guest).
    fn is_stripe_empty(&self, stripe_id: usize) -> bool {
        self.metadata_state.stripe_fetch_state(stripe_id) == NoSource
            && !self.metadata_state.stripe_written(stripe_id)
    }

    /// Skip a stripe: clear its OPS_LOCKED durably and unlock without processing.
    fn skip_and_unlock_stripe(&mut self, stripe_id: usize, metadata_flusher: &mut MetadataFlusher) {
        // Durably clear OPS_LOCKED, then volatile unlock — same as process_and_unlock
        // but without calling process_stripe/on_stripe_done.
        metadata_flusher.clear_ops_locked(stripe_id);
        while metadata_flusher.busy() {
            metadata_flusher.update();
        }
        self.ops_shared.unlock_stripe(stripe_id);
        self.ops_shared.increment_stripes_processed();
    }

    fn update_operation(&mut self, metadata_flusher: &mut MetadataFlusher) {
        if self.ops_shared.phase() != OPERATING {
            return;
        }

        let skip_empty = self
            .active_operation
            .as_ref()
            .unwrap()
            .operation
            .skip_empty_stripes();

        // Priority stripes first (requested by frontend writes)
        while let Some(stripe_id) = self
            .active_operation
            .as_mut()
            .unwrap()
            .priority_queue
            .pop_front()
        {
            if self.ops_shared.stripe_locked(stripe_id) {
                if skip_empty && self.is_stripe_empty(stripe_id) {
                    self.skip_and_unlock_stripe(stripe_id, metadata_flusher);
                } else {
                    self.process_and_unlock_stripe(stripe_id, metadata_flusher);
                }
            }
        }

        // Background: process next locked stripe.
        // We read/advance next_stripe in a scoped borrow, then call methods on self.
        loop {
            let s = {
                let active = self.active_operation.as_mut().unwrap();
                if active.next_stripe >= self.stripe_count {
                    break;
                }
                let s = active.next_stripe;
                active.next_stripe += 1;
                s
            };
            if self.ops_shared.stripe_locked(s) {
                if skip_empty && self.is_stripe_empty(s) {
                    // Skip is cheap (no I/O) — continue to next stripe
                    self.skip_and_unlock_stripe(s, metadata_flusher);
                    continue;
                }
                self.process_and_unlock_stripe(s, metadata_flusher);
                break; // one per iteration to stay responsive
            }
        }

        // Check if all done
        if self.ops_shared.stripes_processed() == self.stripe_count {
            self.complete_operation(metadata_flusher);
        }
    }

    fn process_and_unlock_stripe(
        &mut self,
        stripe_id: usize,
        metadata_flusher: &mut MetadataFlusher,
    ) {
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
                shared: &self.ops_shared,
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
                self.abort_operation_active(&err_str, metadata_flusher);
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
                shared: &self.ops_shared,
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
                self.abort_operation_active(&err_str, metadata_flusher);
                return;
            }
        }

        // 3. PERSIST: Queue durable clear of OPS_LOCKED bit. Wait for the
        //    metadata flusher to complete the write+flush before volatile unlock.
        //    This ensures durability-before-visibility: if we crash after the
        //    volatile unlock but before the next stripe, the cleared bit on disk
        //    means we won't re-process this stripe on recovery.
        metadata_flusher.clear_ops_locked(stripe_id);
        while metadata_flusher.busy() {
            metadata_flusher.update();
        }

        // 4. Unlock (volatile) — Release ensures all prior writes are visible
        self.ops_shared.unlock_stripe(stripe_id);

        // 5. Increment progress
        self.ops_shared.increment_stripes_processed();
    }

    fn complete_operation(&mut self, metadata_flusher: &mut MetadataFlusher) {
        let mut active = self.active_operation.take().unwrap();
        let op_name = active.operation.name().to_string();

        {
            let mut ctx = self.make_operation_context();
            if let Err(e) = active.operation.complete(&mut ctx) {
                error!("Operation '{}' complete() failed: {}", op_name, e);
            }
        }

        self.ops_target_channel = None;

        // PERSIST: Clear ops state on disk before volatile phase transition.
        self.persist_ops_clear(&op_name, metadata_flusher);

        // Return to normal (volatile)
        self.ops_shared.set_gate_reads(false);
        self.ops_shared.set_phase(NORMAL);

        info!("Operation '{}': completed successfully", op_name);
    }

    fn abort_operation(
        &mut self,
        operation: &mut dyn StripeOperation,
        error: &str,
        metadata_flusher: &mut MetadataFlusher,
    ) {
        let op_name = operation.name().to_string();
        error!("Aborting operation '{}': {}", op_name, error);

        self.ops_shared.unlock_all_stripes();

        {
            let mut ctx = self.make_operation_context();
            operation.on_failure(error, &mut ctx);
        }

        self.ops_target_channel = None;

        // PERSIST: Clear ops state on disk before volatile phase transition.
        self.persist_ops_clear(&op_name, metadata_flusher);

        self.ops_shared.set_gate_reads(false);
        self.ops_shared.reset_stripes_processed();
        self.ops_shared.reset_drained();
        self.ops_shared.set_phase(NORMAL);
    }

    fn abort_operation_active(&mut self, error: &str, metadata_flusher: &mut MetadataFlusher) {
        let mut active = self.active_operation.take().unwrap();
        self.abort_operation(&mut *active.operation, error, metadata_flusher);
    }

    pub fn cancel_operation(&mut self, metadata_flusher: &mut MetadataFlusher) {
        // Cancel during drain: no metadata has been persisted, no stripes locked,
        // no target channel created. Just discard the drain state and reset.
        if let Some(drain) = self.drain_state.take() {
            let operation = match drain {
                DrainState::DrainingPipelines { operation } => operation,
                DrainState::WaitingForChannels { operation } => operation,
            };
            let op_name = operation.name().to_string();
            if operation.supports_cancel() {
                info!("Cancelling operation '{}' during drain", op_name);
                self.ops_shared.set_gate_reads(false);
                self.ops_shared.reset_drained();
                self.ops_shared.set_phase(NORMAL);
            } else {
                error!("Operation '{}' does not support cancellation", op_name);
                // Put it back
                self.drain_state = Some(DrainState::DrainingPipelines { operation });
            }
            return;
        }

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
        self.abort_operation_active("cancelled by user", metadata_flusher);
    }

    /// Clear ops state in metadata and persist to disk. Called during
    /// complete_operation and abort_operation to ensure the on-disk state
    /// reflects that no operation is in progress before volatile state changes.
    fn persist_ops_clear(&self, op_name: &str, metadata_flusher: &mut MetadataFlusher) {
        let metadata = metadata_flusher.metadata_mut();
        metadata.clear_ops_state();
        // Also clear any remaining OPS_LOCKED bits (relevant for abort/cancel
        // where not all stripes were processed and cleared individually).
        for i in 0..metadata.stripe_headers.len() {
            metadata.clear_ops_locked(i);
        }
        if let Err(e) = metadata_flusher
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

    fn make_operation_context(&mut self) -> OperationContext<'_> {
        OperationContext {
            target_channel: self
                .ops_target_channel
                .as_deref_mut()
                .expect("ops_target_channel must be set before making operation context"),
            stripe_sector_count_shift: self.stripe_sector_count_shift,
            stripe_count: self.stripe_count,
            shared: &self.ops_shared,
        }
    }

    // --- Crash recovery ---

    /// Check for an interrupted operation on startup and resume or clear it.
    ///
    /// Called at the start of `run()` before the main loop. If metadata shows
    /// `ops_phase == OPERATING`, an operation was in progress when the process
    /// crashed. Recovery re-processes any stripes still marked with `OPS_LOCKED`
    /// then clears the operation state.
    ///
    /// Recovery is idempotent: if we crash during recovery itself, the same
    /// locked stripes will be detected and re-processed on the next startup.
    pub fn recover_interrupted_operation(&mut self, metadata_flusher: &mut MetadataFlusher) {
        let recovery_info = match metadata_flusher.metadata_mut().ops_recovery_info() {
            Some(info) => info,
            None => return, // No recovery needed
        };

        info!(
            "Crash recovery: detected interrupted operation (type={}, id={}, locked_stripes={})",
            recovery_info.ops_type,
            recovery_info.ops_id,
            recovery_info.locked_stripes.len(),
        );

        // Edge case: ops_phase=OPERATING but 0 locked stripes. This can happen
        // if the crash occurred during the completion write (all stripes were
        // individually unlocked but phase wasn't cleared yet). Just clear phase.
        if recovery_info.locked_stripes.is_empty() {
            info!("Crash recovery: no locked stripes, clearing operation state");
            self.persist_ops_clear("recovery", metadata_flusher);
            return;
        }

        match recovery_info.ops_type {
            ops_type::SNAPSHOT => self.recover_snapshot(&recovery_info, metadata_flusher),
            ops_type::REKEY => self.recover_rekey(&recovery_info, metadata_flusher),
            _ => {
                warn!(
                    "Crash recovery: unknown operation type {}, clearing state",
                    recovery_info.ops_type
                );
                self.persist_ops_clear("recovery-unknown", metadata_flusher);
            }
        }
    }

    /// Resume snapshot recovery: re-copy locked stripes from target to staging.
    fn recover_snapshot(&mut self, info: &OpsRecoveryInfo, metadata_flusher: &mut MetadataFlusher) {
        let staging_path = match &info.staging_path {
            Some(path) => path.clone(),
            None => {
                warn!(
                    "Crash recovery: snapshot {} has no staging path, clearing state",
                    info.ops_id
                );
                self.persist_ops_clear("recovery-snapshot-no-path", metadata_flusher);
                return;
            }
        };

        // Check if staging file exists
        if !Path::new(&staging_path).exists() {
            warn!(
                "Crash recovery: staging file '{}' missing for snapshot {}, accepting data loss and clearing state",
                staging_path, info.ops_id
            );
            self.persist_ops_clear("recovery-snapshot-missing-staging", metadata_flusher);
            return;
        }

        info!(
            "Crash recovery: resuming snapshot {} — re-copying {} locked stripes to '{}'",
            info.ops_id,
            info.locked_stripes.len(),
            staging_path,
        );

        // Open staging device using SyncBlockDevice (simpler for recovery)
        let staging_dev = match crate::block_device::SyncBlockDevice::new(
            staging_path.clone().into(),
            false, // not readonly
            true,  // direct_io
            false, // not write_through (we flush explicitly)
        ) {
            Ok(dev) => dev,
            Err(e) => {
                error!(
                    "Crash recovery: failed to open staging file '{}': {}, clearing state",
                    staging_path, e
                );
                self.persist_ops_clear("recovery-snapshot-open-failed", metadata_flusher);
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
                self.persist_ops_clear("recovery-snapshot-channel-failed", metadata_flusher);
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
                self.persist_ops_clear("recovery-snapshot-target-channel-failed", metadata_flusher);
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

            // Read stripe from target
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

            // Write stripe to staging
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

            // Flush staging
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

            // Durably clear OPS_LOCKED for this stripe before moving to next.
            // This makes recovery idempotent: if we crash here, only remaining
            // locked stripes will be re-processed.
            metadata_flusher.clear_ops_locked(stripe_id);
            while metadata_flusher.busy() {
                metadata_flusher.update();
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

        // Clear operation state on disk (sets phase=Normal, clears remaining locks)
        self.persist_ops_clear("recovery-snapshot", metadata_flusher);
    }

    /// Handle rekey recovery. Rekey cannot be automatically resumed because the
    /// key material is not stored in metadata (by design — keys should not be
    /// persisted to disk). Log a warning and clear state. The partially-rekeyed
    /// stripes will use the old key (since OPS_LOCKED stripes were never
    /// switched to the new key cipher routing).
    fn recover_rekey(&self, info: &OpsRecoveryInfo, metadata_flusher: &mut MetadataFlusher) {
        warn!(
            "Crash recovery: interrupted rekey operation (id={}, {} locked stripes). \
             Rekey cannot be automatically resumed — key material is not persisted. \
             Clearing operation state; locked stripes retain old encryption key.",
            info.ops_id,
            info.locked_stripes.len(),
        );
        self.persist_ops_clear("recovery-rekey", metadata_flusher);
    }
}
