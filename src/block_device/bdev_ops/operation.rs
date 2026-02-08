use crate::block_device::IoChannel;
use crate::Result;

use super::shared_state::OpsSharedState;

/// Context provided to `StripeOperation` callbacks by the bgworker.
pub struct OperationContext<'a> {
    /// Channel to read/write the target device (bgworker's fetch_target_channel).
    pub target_channel: &'a mut dyn IoChannel,
    /// Log2 of stripe size in sectors.
    pub stripe_sector_count_shift: u8,
    /// Total number of stripes.
    pub stripe_count: usize,
    /// Shared state for progress reporting.
    pub shared: &'a OpsSharedState,
}

/// Trait that parameterizes the `bdev_ops` framework for specific operations
/// (snapshot, rekey, scrub, etc.).
///
/// The bgworker receives a `Box<dyn StripeOperation>` and calls the trait methods
/// without knowing the concrete operation type.
pub trait StripeOperation: Send {
    /// Human-readable name for logging and RPC status (e.g., "snapshot", "rekey").
    fn name(&self) -> &str;

    /// Whether reads to locked stripes should be gated.
    /// `false` = snapshot (target unchanged), `true` = rekey (in-place re-encryption).
    fn gate_reads(&self) -> bool;

    /// Called once after drain completes, before phase transitions to Operating.
    /// Use for operation-specific setup (e.g., create staging channel, record keys).
    fn begin(&mut self, ctx: &mut OperationContext) -> Result<()>;

    /// Process one stripe: perform the operation-specific work.
    /// Called by bgworker while stripe is still locked.
    /// MUST complete all IO synchronously (blocking poll loop) before returning.
    fn process_stripe(&mut self, stripe_id: usize, ctx: &mut OperationContext) -> Result<()>;

    /// Called AFTER `process_stripe` succeeds but BEFORE the stripe lock is released.
    /// Critical for rekey: switch dual-key cipher to new key for this stripe.
    /// For snapshot: no-op.
    fn on_stripe_done(&mut self, stripe_id: usize, ctx: &mut OperationContext) -> Result<()>;

    /// Called after all stripes are processed and phase returns to Normal.
    /// Use for cleanup (e.g., close staging channel, update config).
    fn complete(&mut self, ctx: &mut OperationContext) -> Result<()>;

    /// Called if the operation fails at any point. Must release all resources.
    /// The framework releases all stripe locks before calling this.
    fn on_failure(&mut self, error: &str, ctx: &mut OperationContext);

    /// Whether this operation supports cancellation.
    /// Snapshot: `true` (discard staging, release locks).
    /// Rekey: `false` (partial rekey leaves mixed-key state).
    fn supports_cancel(&self) -> bool;
}
