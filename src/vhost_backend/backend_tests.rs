#[cfg(test)]
mod tests {
    use crate::{
        block_device::bdev_test::TestBlockDevice,
        config::DeviceConfig,
        utils::{aligned_buffer::BUFFER_ALIGNMENT, block::VirtioBlockConfig},
        vhost_backend::{init_metadata, UbiBlkBackend, SECTOR_SIZE},
        UbiblkError,
    };

    use vhost::vhost_user::message::VhostUserProtocolFeatures;
    use vhost_user_backend::VhostUserBackend;
    use virtio_bindings::virtio_blk::VIRTIO_BLK_F_FLUSH;
    use vm_memory::{ByteValued, GuestMemoryAtomic, GuestMemoryMmap};
    use vmm_sys_util::epoll::EventSet;

    fn default_options(path: String) -> DeviceConfig {
        DeviceConfig {
            path,
            socket: "sock".to_string(),
            num_queues: 1,
            queue_size: 32,
            seg_size_max: 65536,
            seg_count_max: 4,
            write_through: true,
            device_id: "ubiblk".to_string(),
            io_engine: crate::config::IoEngine::IoUring,
            ..Default::default()
        }
    }

    /// Building the backend with a queue size that is not a power of two should fail.
    #[test]
    fn invalid_queue_size() {
        let mut config = default_options("test.img".to_string());
        config.queue_size = 30;
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let result = UbiBlkBackend::new(&config, mem, block_device, BUFFER_ALIGNMENT, vec![]);
        assert!(matches!(result, Err(UbiblkError::InvalidParameter { .. })));
    }

    /// Ensure a backend can be created with valid parameters and exposes expected features.
    #[test]
    fn backend_features_and_protocol() {
        let config = default_options("img".to_string());
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend =
            UbiBlkBackend::new(&config, mem, block_device, BUFFER_ALIGNMENT, vec![]).unwrap();
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
        let config = default_options("img".to_string());
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend =
            UbiBlkBackend::new(&config, mem, block_device, BUFFER_ALIGNMENT, vec![]).unwrap();
        backend.set_event_idx(true);
        for thread in backend.threads().iter() {
            assert!(thread.lock().unwrap().event_idx);
        }
    }

    /// handle_event should reject unexpected event sets.
    #[test]
    fn handle_event_invalid_eventset() {
        let config = default_options("img".to_string());
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend =
            UbiBlkBackend::new(&config, mem, block_device, BUFFER_ALIGNMENT, vec![]).unwrap();
        let err = backend.handle_event(0, EventSet::OUT, &[], 0).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::Other);
    }

    /// handle_event should reject device events other than 0.
    #[test]
    fn handle_event_invalid_device() {
        let config = default_options("img".to_string());
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend =
            UbiBlkBackend::new(&config, mem, block_device, BUFFER_ALIGNMENT, vec![]).unwrap();
        let err = backend.handle_event(1, EventSet::IN, &[], 0).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::Other);
    }

    /// init_metadata should fail when metadata_path is missing.
    #[test]
    fn init_metadata_missing_path() {
        let config = default_options("img".to_string());
        let res = init_metadata(&config, 4);
        assert!(res.is_err());
    }

    /// The features method should advertise common virtio features.
    #[test]
    fn features_advertise_bits() {
        let config = default_options("img".to_string());
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend =
            UbiBlkBackend::new(&config, mem, block_device, BUFFER_ALIGNMENT, vec![]).unwrap();

        let features = backend.features();
        use virtio_bindings::virtio_config::VIRTIO_F_VERSION_1;
        use virtio_bindings::virtio_ring::VIRTIO_RING_F_EVENT_IDX;
        assert!(features & (1 << VIRTIO_F_VERSION_1) != 0);
        assert!(features & (1 << VIRTIO_RING_F_EVENT_IDX) != 0);
    }

    /// acked_features should accept arbitrary feature flags without panicking.
    #[test]
    fn acked_features_noop() {
        let config = default_options("img".to_string());
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend =
            UbiBlkBackend::new(&config, mem, block_device, BUFFER_ALIGNMENT, vec![]).unwrap();

        backend.acked_features(1 << VIRTIO_BLK_F_FLUSH);
    }

    /// set_event_idx(false) should clear the flag on all worker threads.
    #[test]
    fn clear_event_index() {
        let config = default_options("img".to_string());
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend =
            UbiBlkBackend::new(&config, mem, block_device, BUFFER_ALIGNMENT, vec![]).unwrap();
        backend.set_event_idx(true);
        backend.set_event_idx(false);
        for thread in backend.threads().iter() {
            assert!(!thread.lock().unwrap().event_idx);
        }
    }

    /// get_config should return a valid VirtioBlockConfig structure.
    #[test]
    fn get_config_returns_struct() {
        let config = default_options("img".to_string());
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend =
            UbiBlkBackend::new(&config, mem, block_device, BUFFER_ALIGNMENT, vec![]).unwrap();

        let bytes = backend.get_config(0, std::mem::size_of::<VirtioBlockConfig>() as u32);
        assert_eq!(bytes.len(), std::mem::size_of::<VirtioBlockConfig>());
        let virtio_config: VirtioBlockConfig = *VirtioBlockConfig::from_slice(&bytes).unwrap();
        let capacity = virtio_config.capacity;
        let blk_size = virtio_config.blk_size;
        let queues = virtio_config.num_queues;
        assert_eq!(capacity, 8);
        assert_eq!(blk_size, SECTOR_SIZE as u32);
        assert_eq!(queues as usize, config.num_queues);
    }

    /// queues_per_thread should reflect the number of queues configured.
    #[test]
    fn queues_per_thread_multiple() {
        let mut config = default_options("img".to_string());
        config.num_queues = 3;
        config.cpus = None;
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend =
            UbiBlkBackend::new(&config, mem, block_device, BUFFER_ALIGNMENT, vec![]).unwrap();

        assert_eq!(backend.queues_per_thread(), vec![1, 2, 4]);
    }

    #[test]
    fn cpus_mismatch() {
        let mut config = default_options("img".to_string());
        config.num_queues = 2;
        config.cpus = Some(vec![0]);
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let res = UbiBlkBackend::new(&config, mem, block_device, BUFFER_ALIGNMENT, vec![]);
        assert!(res.is_err());
    }

    /// update_memory is currently a no-op and should succeed.
    #[test]
    fn update_memory_nop() {
        let config = default_options("img".to_string());
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let mem2 = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend =
            UbiBlkBackend::new(&config, mem, block_device, BUFFER_ALIGNMENT, vec![]).unwrap();

        assert!(backend.update_memory(mem2).is_ok());
    }
}
