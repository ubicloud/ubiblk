use crate::block_device::{BlockDevice, IoChannel, SharedBuffer};
use crate::Result;

use super::*;

pub struct BlockDeviceStripeSource {
    channel: Box<dyn IoChannel>,
    stripe_sector_count: u64,
    source_sector_count: u64,
}

impl BlockDeviceStripeSource {
    pub fn new(device: Box<dyn BlockDevice>, stripe_sector_count: u64) -> Result<Self> {
        Ok(Self {
            channel: device.create_channel()?,
            stripe_sector_count,
            source_sector_count: device.sector_count(),
        })
    }
}

impl StripeSource for BlockDeviceStripeSource {
    fn request(&mut self, stripe_id: usize, buffer: SharedBuffer) -> Result<()> {
        let stripe_sector_offset = stripe_id as u64 * self.stripe_sector_count;
        if stripe_sector_offset >= self.source_sector_count {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: format!("Stripe {stripe_id} beyond end of source"),
            }));
        }

        let stripe_sector_count = self
            .stripe_sector_count
            .min(self.source_sector_count - stripe_sector_offset);

        self.channel.add_read(
            stripe_sector_offset,
            stripe_sector_count as u32,
            buffer,
            stripe_id,
        );

        self.channel.submit()
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        self.channel.poll()
    }

    fn busy(&self) -> bool {
        self.channel.busy()
    }

    fn sector_count(&self) -> u64 {
        self.source_sector_count
    }

    fn has_stripe(&self, stripe_id: usize) -> bool {
        let stripe_sector_offset = stripe_id as u64 * self.stripe_sector_count;
        stripe_sector_offset < self.source_sector_count
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block_device::{bdev_test::TestBlockDevice, shared_buffer};
    use crate::vhost_backend::SECTOR_SIZE;
    use crate::UbiblkError;

    #[test]
    fn test_request_beyond_end_errors() {
        let device = Box::new(TestBlockDevice::new(8 * SECTOR_SIZE as u64));
        let mut source = BlockDeviceStripeSource::new(device, 4).unwrap();
        let buffer = shared_buffer(SECTOR_SIZE);

        let err = source.request(2, buffer).unwrap_err();
        assert!(matches!(err, UbiblkError::InvalidParameter { .. }));
    }
}
