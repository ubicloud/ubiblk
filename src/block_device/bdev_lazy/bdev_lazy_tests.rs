#[cfg(test)]
mod tests {
    use crate::block_device::SharedBuffer;
    use crate::block_device::{
        bdev_lazy::{
            stripe_fetcher::SharedStripeFetcher, LazyBlockDevice, StripeFetcher, UbiMetadata,
        },
        bdev_test::TestBlockDevice,
        BlockDevice, IoChannel,
    };
    use crate::utils::aligned_buffer::AlignedBuf;
    use crate::vhost_backend::SECTOR_SIZE;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::{Arc, Mutex};
    use std::thread::sleep;
    use std::time::Duration;
    use vmm_sys_util::eventfd::EventFd;

    /// Poll the channel and stripe fetcher until all operations complete.
    fn drive(fetcher: &SharedStripeFetcher, chan: &mut Box<dyn IoChannel>) -> Vec<(usize, bool)> {
        let mut results = Vec::new();
        loop {
            {
                let mut f = fetcher.lock().unwrap();
                f.update();
            }
            results.extend(chan.poll());
            if !chan.busy() {
                break;
            }
            sleep(Duration::from_millis(1));
        }
        {
            let mut f = fetcher.lock().unwrap();
            f.update();
        }
        results.extend(chan.poll());
        results
    }

    /// Ensure that reads trigger stripe fetches when copy-on-read is enabled
    /// and that queued writes are committed once the fetch completes.
    #[test]
    fn test_copy_on_read_true() {
        let stripe_shift = 12u8;
        let stripe_sectors = 1u64 << stripe_shift;
        let dev_size = stripe_sectors * SECTOR_SIZE as u64 * 4;

        let source_dev = TestBlockDevice::new(dev_size);
        let target_dev = TestBlockDevice::new(dev_size);
        let metadata_dev = TestBlockDevice::new(8 * 1024 * 1024);

        let target_mem = target_dev.mem.clone();
        let target_metrics = target_dev.metrics.clone();

        let data = b"copy_on_read_data";
        let mut tmp = vec![0u8; SECTOR_SIZE];
        tmp[..data.len()].copy_from_slice(data);
        source_dev.write(0, &tmp, SECTOR_SIZE);

        let mut ch = metadata_dev.create_channel().unwrap();
        UbiMetadata::new(stripe_shift).write(&mut ch).unwrap();

        let killfd = EventFd::new(0).unwrap();
        let fetcher = Arc::new(Mutex::new(
            StripeFetcher::new(&source_dev, &target_dev, &metadata_dev, killfd, 512).unwrap(),
        ));

        let lazy = LazyBlockDevice::new(Box::new(target_dev), None, fetcher.clone()).unwrap();
        let mut chan = lazy.create_channel().unwrap();

        let read_buf: SharedBuffer = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        chan.add_read(0, 1, read_buf.clone(), 1);
        chan.submit().unwrap();
        let results = drive(&fetcher, &mut chan);
        assert_eq!(results, vec![(1, true)]);
        assert_eq!(&read_buf.borrow().as_slice()[..data.len()], data);
        assert_eq!(&target_mem.read().unwrap()[0..data.len()], data);

        let write_data = b"queued_write";
        let write_buf: SharedBuffer = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        write_buf.borrow_mut().as_mut_slice()[..write_data.len()].copy_from_slice(write_data);
        chan.add_write(stripe_sectors, 1, write_buf.clone(), 2);
        chan.submit().unwrap();
        let results = drive(&fetcher, &mut chan);
        assert_eq!(results, vec![(2, true)]);
        let start = stripe_sectors as usize * SECTOR_SIZE;
        assert_eq!(
            &target_mem.read().unwrap()[start..start + write_data.len()],
            write_data
        );

        let flush_id = 3;
        chan.add_flush(flush_id);
        chan.submit().unwrap();
        let results = drive(&fetcher, &mut chan);
        assert_eq!(results, vec![(flush_id, true)]);
        assert_eq!(target_metrics.read().unwrap().flushes, 1);
    }

    /// Verify that reads are served from the image when copy-on-read is
    /// disabled and that writes and flushes still operate on the target device.
    #[test]
    fn test_copy_on_read_false() {
        let stripe_shift = 12u8;
        let stripe_sectors = 1u64 << stripe_shift;
        let dev_size = stripe_sectors * SECTOR_SIZE as u64 * 4;

        let image_dev = TestBlockDevice::new(dev_size);
        let target_dev = TestBlockDevice::new(dev_size);
        let metadata_dev = TestBlockDevice::new(8 * 1024 * 1024);

        let target_mem = target_dev.mem.clone();
        let target_metrics = target_dev.metrics.clone();
        let image_metrics = image_dev.metrics.clone();

        let data = b"image_read";
        let mut tmp = vec![0u8; SECTOR_SIZE];
        tmp[..data.len()].copy_from_slice(data);
        image_dev.write(0, &tmp, SECTOR_SIZE);

        let mut ch = metadata_dev.create_channel().unwrap();
        UbiMetadata::new(stripe_shift).write(&mut ch).unwrap();

        let killfd = EventFd::new(0).unwrap();
        let fetcher = Arc::new(Mutex::new(
            StripeFetcher::new(&image_dev, &target_dev, &metadata_dev, killfd, 512).unwrap(),
        ));

        let lazy = LazyBlockDevice::new(
            Box::new(target_dev),
            Some(Box::new(image_dev)),
            fetcher.clone(),
        )
        .unwrap();
        let mut chan = lazy.create_channel().unwrap();

        let read_buf: SharedBuffer = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        chan.add_read(0, 1, read_buf.clone(), 1);
        chan.submit().unwrap();
        let results = drive(&fetcher, &mut chan);
        assert_eq!(results, vec![(1, true)]);
        assert_eq!(&read_buf.borrow().as_slice()[..data.len()], data);
        assert_ne!(&target_mem.read().unwrap()[0..data.len()], data);
        assert_eq!(image_metrics.read().unwrap().reads, 1);
        assert_eq!(target_metrics.read().unwrap().reads, 0);

        let write_data = b"write_after_fetch";
        let write_buf: SharedBuffer = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        write_buf.borrow_mut().as_mut_slice()[..write_data.len()].copy_from_slice(write_data);
        chan.add_write(stripe_sectors, 1, write_buf.clone(), 2);
        chan.submit().unwrap();
        let results = drive(&fetcher, &mut chan);
        assert_eq!(results, vec![(2, true)]);
        let start = stripe_sectors as usize * SECTOR_SIZE;
        assert_eq!(
            &target_mem.read().unwrap()[start..start + write_data.len()],
            write_data
        );

        let flush_id = 3;
        chan.add_flush(flush_id);
        chan.submit().unwrap();
        let results = drive(&fetcher, &mut chan);
        assert_eq!(results, vec![(flush_id, true)]);
        assert_eq!(target_metrics.read().unwrap().flushes, 1);
    }

    /// Ensure that flush requests are completed only after metadata has been
    /// written and flushed.
    #[test]
    fn test_flush_waits_for_metadata_flush() {
        let stripe_shift = 12u8;
        let stripe_sectors = 1u64 << stripe_shift;
        let dev_size = stripe_sectors * SECTOR_SIZE as u64 * 4;

        let source_dev = TestBlockDevice::new(dev_size);
        let target_dev = TestBlockDevice::new(dev_size);
        let metadata_dev = TestBlockDevice::new(8 * 1024 * 1024);

        let target_metrics = target_dev.metrics.clone();

        let mut ch = metadata_dev.create_channel().unwrap();
        UbiMetadata::new(stripe_shift).write(&mut ch).unwrap();

        let killfd = EventFd::new(0).unwrap();
        let fetcher = Arc::new(Mutex::new(
            StripeFetcher::new(&source_dev, &target_dev, &metadata_dev, killfd, 512).unwrap(),
        ));

        let lazy = LazyBlockDevice::new(Box::new(target_dev), None, fetcher.clone()).unwrap();
        let mut chan = lazy.create_channel().unwrap();

        let flush_id = 42;
        chan.add_flush(flush_id);
        chan.submit().unwrap();

        // Without running the fetcher, the flush should remain pending.
        assert!(chan.poll().is_empty());
        assert!(chan.busy());
        assert_eq!(target_metrics.read().unwrap().flushes, 0);
        // Only the initial metadata write has been flushed so far.
        assert_eq!(metadata_dev.flushes(), 1);

        // Drive the fetcher and channel to completion.
        let results = drive(&fetcher, &mut chan);
        assert_eq!(results, vec![(flush_id, true)]);
        assert_eq!(target_metrics.read().unwrap().flushes, 1);
        assert_eq!(metadata_dev.flushes(), 2);
    }
}
