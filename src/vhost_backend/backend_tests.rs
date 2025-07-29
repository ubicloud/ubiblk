#[cfg(test)]
mod tests {
    use crate::block_device::bdev_test::TestBlockDevice;
    use crate::utils::aligned_buffer::BUFFER_ALIGNMENT;
    use crate::utils::block::VirtioBlockConfig;
    use crate::vhost_backend::{
        init_metadata, start_block_backend, KeyEncryptionCipher, Options, UbiBlkBackend,
        SECTOR_SIZE,
    };
    use crate::VhostUserBlockError;
    use tempfile::NamedTempFile;
    use vhost::vhost_user::message::VhostUserProtocolFeatures;
    use vhost_user_backend::VhostUserBackend;
    use virtio_bindings::virtio_blk::VIRTIO_BLK_F_FLUSH;
    use vm_memory::{GuestMemoryAtomic, GuestMemoryMmap};
    use vmm_sys_util::epoll::EventSet;

    fn default_options(path: String) -> Options {
        Options {
            path,
            image_path: None,
            metadata_path: None,
            io_debug_path: None,
            socket: "sock".to_string(),
            num_queues: 1,
            queue_size: 32,
            seg_size_max: 65536,
            seg_count_max: 4,
            poll_queue_timeout_us: 1000,
            skip_sync: false,
            copy_on_read: false,
            direct_io: false,
            encryption_key: None,
            device_id: "ubiblk".to_string(),
        }
    }

    /// Building the backend with a queue size that is not a power of two should fail.
    #[test]
    fn invalid_queue_size() {
        let mut opts = default_options("test.img".to_string());
        opts.queue_size = 30;
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let result = UbiBlkBackend::new(&opts, mem, block_device, BUFFER_ALIGNMENT);
        assert!(matches!(
            result,
            Err(VhostUserBlockError::InvalidParameter { .. })
        ));
    }

    /// Ensure a backend can be created with valid parameters and exposes expected features.
    #[test]
    fn backend_features_and_protocol() {
        let opts = default_options("img".to_string());
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend = UbiBlkBackend::new(&opts, mem, block_device, BUFFER_ALIGNMENT).unwrap();
        assert_eq!(backend.num_queues(), 1);
        assert_eq!(backend.max_queue_size(), 32);

        let features = backend.features();
        assert!(features & (1 << VIRTIO_BLK_F_FLUSH) != 0);
        let protocol = backend.protocol_features();
        assert!(protocol.contains(VhostUserProtocolFeatures::CONFIG));
    }

    /// Updating event index should propagate to all worker threads.
    #[test]
    fn set_event_index() {
        let opts = default_options("img".to_string());
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend = UbiBlkBackend::new(&opts, mem, block_device, BUFFER_ALIGNMENT).unwrap();
        backend.set_event_idx(true);
        for thread in backend.threads().iter() {
            assert!(thread.lock().unwrap().event_idx);
        }
    }

    /// handle_event should reject unexpected event sets.
    #[test]
    fn handle_event_invalid_eventset() {
        let opts = default_options("img".to_string());
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend = UbiBlkBackend::new(&opts, mem, block_device, BUFFER_ALIGNMENT).unwrap();
        let err = backend.handle_event(0, EventSet::OUT, &[], 0).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::Other);
    }

    /// handle_event should reject device events other than 0.
    #[test]
    fn handle_event_invalid_device() {
        let opts = default_options("img".to_string());
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend = UbiBlkBackend::new(&opts, mem, block_device, BUFFER_ALIGNMENT).unwrap();
        let err = backend.handle_event(1, EventSet::IN, &[], 0).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::Other);
    }

    /// start_block_backend should return an error when image_path is specified without metadata_path.
    #[test]
    fn start_backend_missing_metadata() {
        let tmp = NamedTempFile::new().unwrap();
        tmp.as_file().set_len(SECTOR_SIZE as u64 * 8).unwrap();
        let mut opts = default_options(tmp.path().to_string_lossy().to_string());
        opts.image_path = Some("img2".to_string());
        let res = start_block_backend(&opts, KeyEncryptionCipher::default());
        assert!(res.is_err());
    }

    /// init_metadata should fail when metadata_path is missing.
    #[test]
    fn init_metadata_missing_path() {
        let opts = default_options("img".to_string());
        let res = init_metadata(&opts, KeyEncryptionCipher::default(), 4);
        assert!(res.is_err());
    }

    /// The features method should advertise common virtio features.
    #[test]
    fn features_advertise_bits() {
        let opts = default_options("img".to_string());
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend = UbiBlkBackend::new(&opts, mem, block_device, BUFFER_ALIGNMENT).unwrap();

        let features = backend.features();
        use virtio_bindings::virtio_config::VIRTIO_F_VERSION_1;
        use virtio_bindings::virtio_ring::VIRTIO_RING_F_EVENT_IDX;
        assert!(features & (1 << VIRTIO_F_VERSION_1) != 0);
        assert!(features & (1 << VIRTIO_RING_F_EVENT_IDX) != 0);
    }

    /// acked_features should accept arbitrary feature flags without panicking.
    #[test]
    fn acked_features_noop() {
        let opts = default_options("img".to_string());
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend = UbiBlkBackend::new(&opts, mem, block_device, BUFFER_ALIGNMENT).unwrap();

        backend.acked_features(1 << VIRTIO_BLK_F_FLUSH);
    }

    /// set_event_idx(false) should clear the flag on all worker threads.
    #[test]
    fn clear_event_index() {
        let opts = default_options("img".to_string());
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend = UbiBlkBackend::new(&opts, mem, block_device, BUFFER_ALIGNMENT).unwrap();
        backend.set_event_idx(true);
        backend.set_event_idx(false);
        for thread in backend.threads().iter() {
            assert!(!thread.lock().unwrap().event_idx);
        }
    }

    /// get_config should return a valid VirtioBlockConfig structure.
    #[test]
    fn get_config_returns_struct() {
        let opts = default_options("img".to_string());
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend = UbiBlkBackend::new(&opts, mem, block_device, BUFFER_ALIGNMENT).unwrap();

        let bytes = backend.get_config(0, std::mem::size_of::<VirtioBlockConfig>() as u32);
        assert_eq!(bytes.len(), std::mem::size_of::<VirtioBlockConfig>());
        let config: VirtioBlockConfig =
            unsafe { std::ptr::read_unaligned(bytes.as_ptr() as *const VirtioBlockConfig) };
        let capacity = config.capacity;
        let blk_size = config.blk_size;
        let queues = config.num_queues;
        assert_eq!(capacity, 8);
        assert_eq!(blk_size, SECTOR_SIZE as u32);
        assert_eq!(queues as usize, opts.num_queues);
    }

    /// queues_per_thread should reflect the number of queues configured.
    #[test]
    fn queues_per_thread_multiple() {
        let mut opts = default_options("img".to_string());
        opts.num_queues = 3;
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend = UbiBlkBackend::new(&opts, mem, block_device, BUFFER_ALIGNMENT).unwrap();

        assert_eq!(backend.queues_per_thread(), vec![1, 2, 4]);
    }

    /// update_memory is currently a no-op and should succeed.
    #[test]
    fn update_memory_nop() {
        let opts = default_options("img".to_string());
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let mem2 = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend = UbiBlkBackend::new(&opts, mem, block_device, BUFFER_ALIGNMENT).unwrap();

        assert!(backend.update_memory(mem2).is_ok());
    }
}
