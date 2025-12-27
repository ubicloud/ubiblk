use crate::{block_device::SharedBuffer, Result};

/// A source from which stripes can be fetched.
pub trait StripeSource {
    /// Request to fetch a stripe.
    fn request(&mut self, stripe_id: usize, buffer: SharedBuffer) -> Result<()>;
    /// Poll for completed stripe fetch requests.
    fn poll(&mut self) -> Vec<(usize, bool)>;
    /// Check if there are any pending requests.
    fn busy(&self) -> bool;
}

mod bdev;
pub use bdev::BlockDeviceStripeSource;
