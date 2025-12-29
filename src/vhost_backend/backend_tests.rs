#[cfg(test)]
mod tests {
    use crate::{
        block_device::bdev_test::TestBlockDevice,
        crypt::KeyEncryptionCipher,
        utils::{aligned_buffer::BUFFER_ALIGNMENT, block::VirtioBlockConfig},
        vhost_backend::{init_metadata, Options, UbiBlkBackend, SECTOR_SIZE},
        UbiblkError,
    };

    use vhost::vhost_user::message::VhostUserProtocolFeatures;
    use vhost_user_backend::VhostUserBackend;
    use virtio_bindings::virtio_blk::VIRTIO_BLK_F_FLUSH;
    use vm_memory::{ByteValued, GuestMemoryAtomic, GuestMemoryMmap};
    use vmm_sys_util::epoll::EventSet;

    fn default_options(path: String) -> Options {
        Options {
            path,
            image_path: None,
            remote_image: None,
            metadata_path: None,
            io_debug_path: None,
            rpc_socket_path: None,
            socket: "sock".to_string(),
            cpus: None,
            num_queues: 1,
            queue_size: 32,
            seg_size_max: 65536,
            seg_count_max: 4,
            poll_queue_timeout_us: 1000,
            copy_on_read: false,
            track_written: false,
            write_through: true,
            autofetch: false,
            encryption_key: None,
            psk_identity: None,
            psk_secret: None,
            device_id: "ubiblk".to_string(),
            io_engine: crate::vhost_backend::IoEngine::IoUring,
        }
    }

    /// Building the backend with a queue size that is not a power of two should fail.
    #[test]
    fn invalid_queue_size() {
        let mut opts = default_options("test.img".to_string());
        opts.queue_size = 30;
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let result = UbiBlkBackend::new(&opts, mem, block_device, BUFFER_ALIGNMENT, vec![]);
        assert!(matches!(result, Err(UbiblkError::InvalidParameter { .. })));
    }

    /// Ensure a backend can be created with valid parameters and exposes expected features.
    #[test]
    fn backend_features_and_protocol() {
        let opts = default_options("img".to_string());
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend =
            UbiBlkBackend::new(&opts, mem, block_device, BUFFER_ALIGNMENT, vec![]).unwrap();
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
        let backend =
            UbiBlkBackend::new(&opts, mem, block_device, BUFFER_ALIGNMENT, vec![]).unwrap();
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
        let backend =
            UbiBlkBackend::new(&opts, mem, block_device, BUFFER_ALIGNMENT, vec![]).unwrap();
        let err = backend.handle_event(0, EventSet::OUT, &[], 0).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::Other);
    }

    /// handle_event should reject device events other than 0.
    #[test]
    fn handle_event_invalid_device() {
        let opts = default_options("img".to_string());
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend =
            UbiBlkBackend::new(&opts, mem, block_device, BUFFER_ALIGNMENT, vec![]).unwrap();
        let err = backend.handle_event(1, EventSet::IN, &[], 0).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::Other);
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
        let backend =
            UbiBlkBackend::new(&opts, mem, block_device, BUFFER_ALIGNMENT, vec![]).unwrap();

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
        let backend =
            UbiBlkBackend::new(&opts, mem, block_device, BUFFER_ALIGNMENT, vec![]).unwrap();

        backend.acked_features(1 << VIRTIO_BLK_F_FLUSH);
    }

    /// set_event_idx(false) should clear the flag on all worker threads.
    #[test]
    fn clear_event_index() {
        let opts = default_options("img".to_string());
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend =
            UbiBlkBackend::new(&opts, mem, block_device, BUFFER_ALIGNMENT, vec![]).unwrap();
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
        let backend =
            UbiBlkBackend::new(&opts, mem, block_device, BUFFER_ALIGNMENT, vec![]).unwrap();

        let bytes = backend.get_config(0, std::mem::size_of::<VirtioBlockConfig>() as u32);
        assert_eq!(bytes.len(), std::mem::size_of::<VirtioBlockConfig>());
        let config: VirtioBlockConfig = *VirtioBlockConfig::from_slice(&bytes).unwrap();
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
        opts.cpus = None;
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend =
            UbiBlkBackend::new(&opts, mem, block_device, BUFFER_ALIGNMENT, vec![]).unwrap();

        assert_eq!(backend.queues_per_thread(), vec![1, 2, 4]);
    }

    #[test]
    fn cpus_mismatch() {
        let mut opts = default_options("img".to_string());
        opts.num_queues = 2;
        opts.cpus = Some(vec![0]);
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let res = UbiBlkBackend::new(&opts, mem, block_device, BUFFER_ALIGNMENT, vec![]);
        assert!(res.is_err());
    }

    /// update_memory is currently a no-op and should succeed.
    #[test]
    fn update_memory_nop() {
        let opts = default_options("img".to_string());
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let mem2 = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend =
            UbiBlkBackend::new(&opts, mem, block_device, BUFFER_ALIGNMENT, vec![]).unwrap();

        assert!(backend.update_memory(mem2).is_ok());
    }
}
