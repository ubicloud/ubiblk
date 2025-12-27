use crate::{
    block_device::{NullBlockDevice, SharedBuffer},
    stripe_server::{connect_to_stripe_server, PskCredentials, StripeServerClient},
    vhost_backend::{build_block_device, Options},
    KeyEncryptionCipher, Result,
};

/// A source from which stripes can be fetched.
pub trait StripeSource {
    /// Request to fetch a stripe.
    fn request(&mut self, stripe_id: usize, buffer: SharedBuffer) -> Result<()>;
    /// Poll for completed stripe fetch requests.
    fn poll(&mut self) -> Vec<(usize, bool)>;
    /// Check if there are any pending requests.
    fn busy(&self) -> bool;
    /// Get the sector count of the stripe source.
    fn sector_count(&self) -> u64;
}

mod bdev;
mod remote;
pub use bdev::BlockDeviceStripeSource;
pub use remote::RemoteStripeSource;

pub struct StripeSourceBuilder {
    options: Options,
    kek: KeyEncryptionCipher,
    stripe_sector_count: u64,
}

impl StripeSourceBuilder {
    pub fn new(options: Options, kek: KeyEncryptionCipher, stripe_sector_count: u64) -> Self {
        Self {
            options,
            kek,
            stripe_sector_count,
        }
    }

    pub fn build(&self) -> Result<Box<dyn StripeSource>> {
        if let Some(remote_image) = &self.options.remote_image {
            let client = build_remote_client(&self.options, &self.kek, remote_image)?;
            let stripe_source =
                RemoteStripeSource::new(Box::new(client), self.stripe_sector_count)?;
            return Ok(Box::new(stripe_source));
        }

        let block_device = if let Some(image_path) = &self.options.image_path {
            build_block_device(image_path, &self.options, self.kek.clone(), true)?
        } else {
            NullBlockDevice::new()
        };

        let stripe_source = BlockDeviceStripeSource::new(block_device, self.stripe_sector_count)?;
        Ok(Box::new(stripe_source))
    }
}

fn build_remote_client(
    options: &Options,
    kek: &KeyEncryptionCipher,
    server_addr: &str,
) -> Result<StripeServerClient> {
    let psk = PskCredentials::from_options(options, kek)?;
    connect_to_stripe_server(server_addr, psk.as_ref())
}
