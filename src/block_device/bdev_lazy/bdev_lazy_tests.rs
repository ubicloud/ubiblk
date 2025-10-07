#[cfg(test)]
mod tests {
    use crate::block_device::SharedBuffer;
    use crate::block_device::{
        bdev_lazy::{init_metadata, BgWorker, LazyBlockDevice, SharedBgWorker, UbiMetadata},
        bdev_test::{TestBlockDevice, TestDeviceMetrics},
        BlockDevice, IoChannel,
    };
    use crate::utils::aligned_buffer::AlignedBuf;
    use crate::vhost_backend::SECTOR_SIZE;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::{Arc, Mutex, RwLock};
    use std::thread::sleep;
    use std::time::Duration;

    const STRIPE_SHIFT: u8 = 12;
    const STRIPE_COUNT: usize = 4;
    const STRIPE_SECTORS: u64 = 1u64 << STRIPE_SHIFT;
    const DEV_SIZE: u64 = STRIPE_SECTORS * SECTOR_SIZE as u64 * STRIPE_COUNT as u64;
    const METADATA_SIZE: u64 = 8 * 1024 * 1024;

    struct TestEnv {
        lazy: Box<LazyBlockDevice>,
        bgworker: SharedBgWorker,
        stripe_sectors: u64,
        target_mem: Arc<RwLock<Vec<u8>>>,
        target_metrics: Arc<RwLock<TestDeviceMetrics>>,
        image_metrics: Option<Arc<RwLock<TestDeviceMetrics>>>,
    }

    fn setup_env(with_image: bool, track_written: bool, data: &[u8]) -> TestEnv {
        let target_dev = TestBlockDevice::new(DEV_SIZE);
        let target_mem = target_dev.mem.clone();
        let target_metrics = target_dev.metrics.clone();

        let metadata_dev = TestBlockDevice::new(METADATA_SIZE);
        let mut ch = metadata_dev.create_channel().unwrap();
        let metadata = UbiMetadata::new(STRIPE_SHIFT, STRIPE_COUNT, STRIPE_COUNT);
        init_metadata(&metadata, &mut ch).unwrap();

        if with_image {
            let image_dev = TestBlockDevice::new(DEV_SIZE);
            if !data.is_empty() {
                let mut tmp = vec![0u8; SECTOR_SIZE];
                tmp[..data.len()].copy_from_slice(data);
                image_dev.write(0, &tmp, SECTOR_SIZE);
            }
            let image_metrics = image_dev.metrics.clone();
            let bgworker: SharedBgWorker = Arc::new(Mutex::new(
                BgWorker::new(&image_dev, &target_dev, &metadata_dev, 512).unwrap(),
            ));
            let (bgworker_ch, metadata_state) = {
                let guard = bgworker.lock().unwrap();
                (guard.req_sender(), guard.shared_state())
            };
            let lazy = LazyBlockDevice::new(
                Box::new(target_dev),
                Some(Box::new(image_dev)),
                bgworker_ch,
                metadata_state,
                track_written,
            )
            .unwrap();
            TestEnv {
                lazy,
                bgworker,
                stripe_sectors: STRIPE_SECTORS,
                target_mem,
                target_metrics,
                image_metrics: Some(image_metrics),
            }
        } else {
            let source_dev = TestBlockDevice::new(DEV_SIZE);
            if !data.is_empty() {
                let mut tmp = vec![0u8; SECTOR_SIZE];
                tmp[..data.len()].copy_from_slice(data);
                source_dev.write(0, &tmp, SECTOR_SIZE);
            }
            let bgworker: SharedBgWorker = Arc::new(Mutex::new(
                BgWorker::new(&source_dev, &target_dev, &metadata_dev, 512).unwrap(),
            ));
            let (bgworker_ch, metadata_state) = {
                let guard = bgworker.lock().unwrap();
                (guard.req_sender(), guard.shared_state())
            };
            let lazy = LazyBlockDevice::new(
                Box::new(target_dev),
                None,
                bgworker_ch,
                metadata_state,
                track_written,
            )
            .unwrap();
            TestEnv {
                lazy,
                bgworker,
                stripe_sectors: STRIPE_SECTORS,
                target_mem,
                target_metrics,
                image_metrics: None,
            }
        }
    }

    /// Poll the channel and the bgworker until all operations complete.
    fn drive(bgworker: &SharedBgWorker, chan: &mut Box<dyn IoChannel>) -> Vec<(usize, bool)> {
        let mut results = Vec::new();
        loop {
            {
                let mut f = bgworker.lock().unwrap();
                f.receive_requests(false);
                f.update();
            }
            results.extend(chan.poll());
            if !chan.busy() {
                break;
            }
            sleep(Duration::from_millis(1));
        }
        {
            let mut f = bgworker.lock().unwrap();
            f.receive_requests(false);
            f.update();
        }
        results.extend(chan.poll());
        results
    }

    /// Ensure that reads trigger stripe fetches when copy-on-read is enabled
    /// and that queued writes are committed once the fetch completes.
    #[test]
    fn test_copy_on_read_true() {
        let env = setup_env(false, false, b"copy_on_read_data");
        let mut chan = env.lazy.create_channel().unwrap();

        assert_eq!(env.target_metrics.read().unwrap().reads, 0);
        assert_eq!(env.target_metrics.read().unwrap().writes, 0);

        let read_buf: SharedBuffer = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        chan.add_read(0, 1, read_buf.clone(), 1);
        chan.submit().unwrap();
        let results = drive(&env.bgworker, &mut chan);
        assert_eq!(results, vec![(1, true)]);
        assert_eq!(
            &read_buf.borrow().as_slice()[.."copy_on_read_data".len()],
            b"copy_on_read_data"
        );
        assert_eq!(
            &env.target_mem.read().unwrap()[0.."copy_on_read_data".len()],
            b"copy_on_read_data"
        );

        assert_eq!(env.target_metrics.read().unwrap().reads, 1);
        assert_eq!(env.target_metrics.read().unwrap().writes, 1);

        let write_data = b"queued_write";
        let write_buf: SharedBuffer = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        write_buf.borrow_mut().as_mut_slice()[..write_data.len()].copy_from_slice(write_data);
        chan.add_write(env.stripe_sectors, 1, write_buf.clone(), 2);
        chan.submit().unwrap();
        let results = drive(&env.bgworker, &mut chan);
        assert_eq!(results, vec![(2, true)]);
        let start = env.stripe_sectors as usize * SECTOR_SIZE;
        assert_eq!(
            &env.target_mem.read().unwrap()[start..start + write_data.len()],
            write_data
        );

        let flush_id = 3;
        chan.add_flush(flush_id);
        chan.submit().unwrap();
        let results = drive(&env.bgworker, &mut chan);
        assert_eq!(results, vec![(flush_id, true)]);
    }

    /// Verify that reads are served from the image when copy-on-read is
    /// disabled and that writes and flushes still operate on the target device.
    #[test]
    fn test_copy_on_read_false() {
        let env = setup_env(true, false, b"image_read");
        let mut chan = env.lazy.create_channel().unwrap();

        assert_eq!(env.image_metrics.as_ref().unwrap().read().unwrap().reads, 0);
        assert_eq!(env.target_metrics.read().unwrap().reads, 0);
        assert_eq!(env.target_metrics.read().unwrap().writes, 0);

        let read_buf: SharedBuffer = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        chan.add_read(0, 1, read_buf.clone(), 1);
        chan.submit().unwrap();
        let results = drive(&env.bgworker, &mut chan);
        assert_eq!(results, vec![(1, true)]);
        assert_eq!(
            &read_buf.borrow().as_slice()[.."image_read".len()],
            b"image_read"
        );
        assert_ne!(
            &env.target_mem.read().unwrap()[0.."image_read".len()],
            b"image_read"
        );
        assert_eq!(env.image_metrics.as_ref().unwrap().read().unwrap().reads, 1);
        assert_eq!(env.target_metrics.read().unwrap().reads, 0);
        assert_eq!(env.target_metrics.read().unwrap().writes, 0);

        let write_data = b"write_after_fetch";
        let write_buf: SharedBuffer = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        write_buf.borrow_mut().as_mut_slice()[..write_data.len()].copy_from_slice(write_data);
        chan.add_write(env.stripe_sectors, 1, write_buf.clone(), 2);
        chan.submit().unwrap();
        let results = drive(&env.bgworker, &mut chan);
        assert_eq!(results, vec![(2, true)]);
        let start = env.stripe_sectors as usize * SECTOR_SIZE;
        assert_eq!(
            &env.target_mem.read().unwrap()[start..start + write_data.len()],
            write_data
        );

        let flush_id = 3;
        chan.add_flush(flush_id);
        chan.submit().unwrap();
        let results = drive(&env.bgworker, &mut chan);
        assert_eq!(results, vec![(flush_id, true)]);
    }

    /// Verify that on multi-stripe reads, we fetch stripes regardless of
    /// whether copy-on-read is enabled or not.
    #[test]
    fn test_copy_on_read_false_multistripe() {
        let env = setup_env(true, false, b"image_read");
        let mut chan = env.lazy.create_channel().unwrap();

        let read_buf: SharedBuffer = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE * 4)));
        chan.add_read(STRIPE_SECTORS - 2, 4, read_buf.clone(), 1);
        chan.submit().unwrap();
        let results = drive(&env.bgworker, &mut chan);
        assert_eq!(results, vec![(1, true)]);

        {
            let image_metrics = env.image_metrics.as_ref().unwrap().read().unwrap();
            let target_metrics = env.target_metrics.read().unwrap();
            assert_eq!(image_metrics.reads, 2);
            assert_eq!(image_metrics.writes, 0);
            assert_eq!(target_metrics.reads, 1);
            assert_eq!(target_metrics.writes, 2);
        }

        // 2nd read should be served from target device
        chan.add_read(STRIPE_SECTORS - 2, 4, read_buf.clone(), 2);
        chan.submit().unwrap();
        let results = drive(&env.bgworker, &mut chan);
        assert_eq!(results, vec![(2, true)]);

        {
            let image_metrics = env.image_metrics.as_ref().unwrap().read().unwrap();
            let target_metrics = env.target_metrics.read().unwrap();
            assert_eq!(image_metrics.reads, 2);
            assert_eq!(image_metrics.writes, 0);
            assert_eq!(target_metrics.reads, 2);
            assert_eq!(target_metrics.writes, 2);
        }
    }

    /// Verify that stripes are marked written when tracking is enabled.
    #[test]
    fn test_track_written_true() {
        let env = setup_env(false, true, b"");
        let mut chan = env.lazy.create_channel().unwrap();

        let write_data = b"write_with_tracking";
        let write_buf: SharedBuffer = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        write_buf.borrow_mut().as_mut_slice()[..write_data.len()].copy_from_slice(write_data);
        chan.add_write(env.stripe_sectors, 1, write_buf.clone(), 1);
        chan.submit().unwrap();
        let results = drive(&env.bgworker, &mut chan);
        assert_eq!(results, vec![(1, true)]);
        let start = env.stripe_sectors as usize * SECTOR_SIZE;
        assert_eq!(
            &env.target_mem.read().unwrap()[start..start + write_data.len()],
            write_data
        );

        let state = env.bgworker.lock().unwrap().shared_state();
        assert!(state.stripe_written(1));

        let flush_id = 2;
        chan.add_flush(flush_id);
        chan.submit().unwrap();
        let results = drive(&env.bgworker, &mut chan);
        assert_eq!(results, vec![(flush_id, true)]);
    }

    /// Verify tracking of written stripes when an image device is present.
    #[test]
    fn test_track_written_true_with_image() {
        let env = setup_env(true, true, b"image_data");
        let mut chan = env.lazy.create_channel().unwrap();

        let write_data = b"track_image_write";
        let write_buf: SharedBuffer = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        write_buf.borrow_mut().as_mut_slice()[..write_data.len()].copy_from_slice(write_data);
        chan.add_write(env.stripe_sectors, 1, write_buf.clone(), 1);
        chan.submit().unwrap();
        let results = drive(&env.bgworker, &mut chan);
        assert_eq!(results, vec![(1, true)]);
        let start = env.stripe_sectors as usize * SECTOR_SIZE;
        assert_eq!(
            &env.target_mem.read().unwrap()[start..start + write_data.len()],
            write_data
        );

        let state = env.bgworker.lock().unwrap().shared_state();
        assert!(state.stripe_written(1));

        let flush_id = 2;
        chan.add_flush(flush_id);
        chan.submit().unwrap();
        let results = drive(&env.bgworker, &mut chan);
        assert_eq!(results, vec![(flush_id, true)]);
    }
}
