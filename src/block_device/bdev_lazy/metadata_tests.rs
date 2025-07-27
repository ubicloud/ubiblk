#[cfg(test)]
mod tests {
    use crate::block_device::bdev_failing::FailingBlockDevice;
    use crate::block_device::bdev_lazy::init_metadata;
    use crate::block_device::bdev_lazy::metadata::{
        MetadataManager, StripeStatus, UbiMetadata, UBI_MAGIC, UBI_MAGIC_SIZE, UBI_MAX_STRIPES,
    };
    use crate::block_device::bdev_test::TestBlockDevice;
    use crate::block_device::{BlockDevice, IoChannel};
    use crate::Result;
    use crate::VhostUserBlockError;

    #[test]
    fn test_metadata_manager() -> Result<()> {
        let metadata_dev = TestBlockDevice::new(40 * 1024 * 1024);
        let stripe_sector_count_shift = 11u8;
        let stripe_sector_count = 1 << stripe_sector_count_shift;
        let source_sector_count = 29 * stripe_sector_count + 4;
        let stripe_count = (source_sector_count + stripe_sector_count - 1) / stripe_sector_count;

        let mut ch = metadata_dev.create_channel()?;
        let metadata = UbiMetadata::new(stripe_sector_count_shift);
        init_metadata(&metadata, &mut ch).unwrap();

        let mut manager = MetadataManager::new(&metadata_dev, source_sector_count)?;

        assert_eq!(manager.stripe_status(0), StripeStatus::NotFetched);
        assert_eq!(manager.stripe_source_sector_offset(0), 0);
        assert_eq!(manager.stripe_target_sector_offset(0), 0);

        let stripes_to_fetch = vec![0, 3, 7, 8];

        for stripe_id in stripes_to_fetch.iter() {
            assert_eq!(manager.stripe_status(*stripe_id), StripeStatus::NotFetched);

            manager.set_stripe_status(*stripe_id, StripeStatus::Queued);
            assert_eq!(manager.stripe_status(*stripe_id), StripeStatus::Queued);

            manager.set_stripe_status(*stripe_id, StripeStatus::Fetching);
            assert_eq!(manager.stripe_status(*stripe_id), StripeStatus::Fetching);

            manager.set_stripe_status(*stripe_id, StripeStatus::Fetched);
            assert_eq!(manager.stripe_status(*stripe_id), StripeStatus::Fetched);
        }

        let stripe_status_vec = manager.stripe_status_vec();
        assert_eq!(stripe_status_vec.stripe_count, stripe_count as u64);

        assert_eq!(metadata_dev.flushes(), 1);
        manager.start_flush().unwrap();
        assert_eq!(manager.poll_flush(), None);
        assert_eq!(manager.poll_flush(), Some(true));
        assert_eq!(metadata_dev.flushes(), 2);

        for i in 0..UBI_MAX_STRIPES {
            let offset = manager.metadata.stripe_headers_offset(i);
            let mut header_buf = [0u8; 1];
            metadata_dev.read(offset, &mut header_buf, 1);
            let expected_header = if stripes_to_fetch.contains(&i) {
                [1]
            } else {
                [0]
            };
            assert_eq!(header_buf, expected_header);
        }

        let mut magic_buf = [0u8; UBI_MAGIC_SIZE];
        metadata_dev.read(0, &mut magic_buf, UBI_MAGIC_SIZE);
        assert_eq!(magic_buf, *UBI_MAGIC);

        Ok(())
    }

    #[test]
    fn test_metadata_magic_mismatch() -> Result<()> {
        let metadata_dev = TestBlockDevice::new(40 * 1024 * 1024);
        let stripe_sector_count_shift = 11u8;
        let stripe_sector_count = 1 << stripe_sector_count_shift;
        let source_sector_count = 29 * stripe_sector_count + 4;

        let mut ch = metadata_dev.create_channel()?;
        let metadata = UbiMetadata::new(stripe_sector_count_shift);
        init_metadata(&metadata, &mut ch).unwrap();

        let bad_magic = [0u8; UBI_MAGIC_SIZE];
        metadata_dev.write(0, &bad_magic, UBI_MAGIC_SIZE);

        let result = MetadataManager::new(&metadata_dev, source_sector_count);
        assert!(matches!(
            result,
            Err(VhostUserBlockError::MetadataError { .. })
        ));
        Ok(())
    }

    #[test]
    fn test_poll_flush_failed_write() -> Result<()> {
        let metadata_dev = FailingBlockDevice::new(40 * 1024 * 1024);
        let stripe_sector_count_shift = 11u8;
        let stripe_sector_count = 1 << stripe_sector_count_shift;
        let source_sector_count = 29 * stripe_sector_count + 4;

        {
            let mut ch = metadata_dev.create_channel()?;
            let metadata = UbiMetadata::new(stripe_sector_count_shift);
            init_metadata(&metadata, &mut ch).unwrap();
        }

        let mut manager = MetadataManager::new(&metadata_dev, source_sector_count)?;

        metadata_dev.fail_next_write();

        manager.set_stripe_status(0, StripeStatus::Fetched);

        manager.start_flush().unwrap();
        assert_eq!(manager.poll_flush(), Some(false));

        Ok(())
    }

    #[test]
    fn test_poll_flush_failed_flush() -> Result<()> {
        let metadata_dev = FailingBlockDevice::new(40 * 1024 * 1024);
        let stripe_sector_count_shift = 11u8;
        let stripe_sector_count = 1 << stripe_sector_count_shift;
        let source_sector_count = 29 * stripe_sector_count + 4;

        {
            let mut ch = metadata_dev.create_channel()?;
            let metadata = UbiMetadata::new(stripe_sector_count_shift);
            init_metadata(&metadata, &mut ch).unwrap();
        }

        let mut manager = MetadataManager::new(&metadata_dev, source_sector_count)?;

        manager.set_stripe_status(0, StripeStatus::Fetched);
        metadata_dev.fail_next_flush();

        manager.start_flush().unwrap();
        assert_eq!(manager.poll_flush(), None);
        assert_eq!(manager.poll_flush(), Some(false));

        Ok(())
    }

    #[test]
    fn test_stripe_count_overflow() -> Result<()> {
        let metadata_dev = TestBlockDevice::new(40 * 1024 * 1024);
        let stripe_sector_count_shift = 0u8;
        let stripe_sector_count = 1u64 << stripe_sector_count_shift;
        let source_sector_count = (UBI_MAX_STRIPES as u64 + 1) * stripe_sector_count;

        let mut ch = metadata_dev.create_channel()?;
        let metadata = UbiMetadata::new(stripe_sector_count_shift);
        init_metadata(&metadata, &mut ch).unwrap();

        let result = MetadataManager::new(&metadata_dev, source_sector_count);
        assert!(matches!(
            result,
            Err(VhostUserBlockError::InvalidParameter { .. })
        ));
        Ok(())
    }
}
