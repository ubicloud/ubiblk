#[cfg(test)]
mod tests {
    use crate::block_device::bdev_test::TestBlockDevice;
    use crate::vhost_backend::{
        init_metadata, start_block_backend, CipherMethod, KeyEncryptionCipher, Options,
        UbiBlkBackend, SECTOR_SIZE,
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
        let result = UbiBlkBackend::new(&opts, mem, block_device);
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
        let backend = UbiBlkBackend::new(&opts, mem, block_device).unwrap();
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
        let backend = UbiBlkBackend::new(&opts, mem, block_device).unwrap();
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
        let backend = UbiBlkBackend::new(&opts, mem, block_device).unwrap();
        let err = backend.handle_event(0, EventSet::OUT, &[], 0).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::Other);
    }

    /// handle_event should reject device events other than 0.
    #[test]
    fn handle_event_invalid_device() {
        let opts = default_options("img".to_string());
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend = UbiBlkBackend::new(&opts, mem, block_device).unwrap();
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
        let res = start_block_backend(
            &opts,
            KeyEncryptionCipher {
                method: CipherMethod::None,
                key: None,
                init_vector: None,
                auth_data: None,
            },
        );
        assert!(res.is_err());
    }

    /// init_metadata should fail when metadata_path is missing.
    #[test]
    fn init_metadata_missing_path() {
        let opts = default_options("img".to_string());
        let res = init_metadata(
            &opts,
            KeyEncryptionCipher {
                method: CipherMethod::None,
                key: None,
                init_vector: None,
                auth_data: None,
            },
            4,
        );
        assert!(res.is_err());
    }
}
