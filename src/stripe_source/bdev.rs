use crate::backends::SECTOR_SIZE;
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

        // Callers reuse buffers, so the part of the last stripe the source does
        // not have would otherwise be the previous stripe's bytes.
        {
            let mut buf = buffer.borrow_mut();
            let read_len = (stripe_sector_count as usize * SECTOR_SIZE).min(buf.len());
            buf.as_mut_slice()[read_len..].fill(0);
        }

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
    use crate::UbiblkError;

    #[test]
    fn a_stripe_the_source_only_partly_holds_reads_back_zero_padded() {
        let stripe_sectors = 4u64;
        let device = Box::new(TestBlockDevice::new(6 * SECTOR_SIZE as u64));
        device.write(
            4 * SECTOR_SIZE,
            &vec![0xBBu8; 2 * SECTOR_SIZE],
            2 * SECTOR_SIZE,
        );
        let mut source = BlockDeviceStripeSource::new(device, stripe_sectors).unwrap();

        let buffer = shared_buffer(stripe_sectors as usize * SECTOR_SIZE);
        buffer.borrow_mut().as_mut_slice().fill(0xAA);
        source.request(1, buffer.clone()).unwrap();
        assert_eq!(source.poll(), vec![(1, true)]);

        let mut expected = vec![0xBBu8; 2 * SECTOR_SIZE];
        expected.extend(vec![0u8; 2 * SECTOR_SIZE]);
        assert_eq!(buffer.borrow().as_slice(), expected.as_slice());
    }

    #[test]
    fn test_request_beyond_end_errors() {
        let device = Box::new(TestBlockDevice::new(8 * SECTOR_SIZE as u64));
        let mut source = BlockDeviceStripeSource::new(device, 4).unwrap();
        let buffer = shared_buffer(SECTOR_SIZE);

        let err = source.request(2, buffer).unwrap_err();
        assert!(matches!(err, UbiblkError::InvalidParameter { .. }));
    }
}
