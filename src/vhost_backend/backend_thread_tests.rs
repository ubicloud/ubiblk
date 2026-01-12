#[cfg(test)]
mod tests {
    use smallvec::smallvec;
    use vhost_user_backend::{bitmap::BitmapMmapRegion, VringRwLock, VringT};
    use virtio_bindings::bindings::virtio_ring::VRING_DESC_F_WRITE;
    use virtio_bindings::virtio_blk::{VIRTIO_BLK_ID_BYTES, VIRTIO_BLK_S_IOERR, VIRTIO_BLK_S_OK};
    use virtio_queue::{desc::split::Descriptor as SplitDescriptor, Queue, QueueOwnedT};
    use vm_memory::{
        Bytes, GuestAddress, GuestAddressSpace, GuestMemoryAtomic, GuestMemoryLoadGuard,
        GuestMemoryMmap,
    };

    use crate::{
        block_device::{bdev_test::TestBlockDevice, BlockDevice},
        utils::aligned_buffer::BUFFER_ALIGNMENT,
        vhost_backend::{
            backend_thread::UbiBlkBackendThread,
            io_tracking::{IoKind, IoTracker},
            request::{Request, RequestType},
            Options, SECTOR_SIZE,
        },
    };

    type GuestMemory = GuestMemoryMmap<BitmapMmapRegion>;
    type DescChain = virtio_queue::DescriptorChain<GuestMemoryLoadGuard<GuestMemory>>;

    fn setup_mem() -> (GuestMemoryAtomic<GuestMemory>, GuestMemory) {
        let mem = GuestMemory::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let gm = GuestMemoryAtomic::new(mem.clone());
        (gm, mem)
    }

    fn build_chain(mem: &GuestMemory, descs: &[SplitDescriptor]) -> DescChain {
        use virtio_queue::desc::RawDescriptor;
        use virtio_queue::mock::MockSplitQueue;

        let vq = MockSplitQueue::new(mem, 16);
        let raw_descs: Vec<RawDescriptor> =
            descs.iter().cloned().map(RawDescriptor::from).collect();
        vq.add_desc_chains(&raw_descs, 0).unwrap();
        let mut queue: Queue = vq.create_queue().unwrap();
        let atomic = GuestMemoryAtomic::new(mem.clone());
        let mut iter = queue.iter(atomic.memory()).unwrap();
        iter.next().unwrap()
    }

    fn setup_vring(mem: &GuestMemory) -> VringRwLock<GuestMemoryAtomic<GuestMemory>> {
        let vring =
            VringRwLock::new(GuestMemoryAtomic::new(mem.clone()), 16).expect("vring new failed");
        vring.set_queue_size(16);
        vring
            .set_queue_info(0x1000, 0x2000, 0x3000)
            .expect("set_queue_info failed");
        vring
    }

    fn default_options(path: &str) -> Options {
        Options {
            path: path.to_string(),
            socket: "sock".to_string(),
            num_queues: 1,
            queue_size: 2,
            seg_size_max: SECTOR_SIZE as u32,
            seg_count_max: 1,
            write_through: true,
            device_id: "ubiblk".to_string(),
            io_engine: crate::vhost_backend::IoEngine::IoUring,
            ..Default::default()
        }
    }

    fn create_thread() -> (UbiBlkBackendThread, GuestMemory) {
        let (gm, mem) = setup_mem();
        let opts = default_options("img");
        let device = TestBlockDevice::new(SECTOR_SIZE as u64 * 8);
        let io_channel = device.create_channel().unwrap();
        let thread =
            UbiBlkBackendThread::new(gm, io_channel, &opts, BUFFER_ALIGNMENT, IoTracker::new(64))
                .unwrap();
        (thread, mem)
    }

    #[test]
    fn request_len_sums_descriptors() {
        let (thread, _mem) = create_thread();
        let req = Request {
            request_type: RequestType::Out,
            sector: 0,
            data_descriptors: smallvec![
                (GuestAddress(0), 100u32),
                (GuestAddress(SECTOR_SIZE as u64), 200u32),
            ],
            status_addr: GuestAddress(0),
        };
        assert_eq!(thread.request_len(&req), 300);
    }

    #[test]
    fn put_request_slot_releases_slot() {
        let (mut thread, mem) = create_thread();
        let desc = SplitDescriptor::new(0x1000, 16, VRING_DESC_F_WRITE as u16, 0);
        let chain = build_chain(&mem, &[desc]);
        let req = Request {
            request_type: RequestType::In,
            sector: 0,
            data_descriptors: smallvec![(GuestAddress(0x2000), 64u32)],
            status_addr: GuestAddress(0),
        };
        let idx = thread.get_request_slot(64, &req, &chain);
        let idx_new = thread.get_request_slot(64, &req, &chain);
        assert_ne!(idx, idx_new);
        thread.put_request_slot(idx);
        let idx2 = thread.get_request_slot(64, &req, &chain);
        assert_eq!(idx, idx2);
    }

    #[test]
    fn get_request_slot_allocates_new_when_full() {
        let (mut thread, mem) = create_thread();
        let desc = SplitDescriptor::new(0x1000, 16, VRING_DESC_F_WRITE as u16, 0);
        let chain = build_chain(&mem, &[desc]);
        let req = Request {
            request_type: RequestType::In,
            sector: 1,
            data_descriptors: smallvec![(GuestAddress(0x2000), 128u32)],
            status_addr: GuestAddress(0),
        };
        // first slot
        let first = thread.get_request_slot(128, &req, &chain);
        assert_eq!(first, 0);
        // allocate second while first is still used
        let second = thread.get_request_slot(128, &req, &chain);
        assert_eq!(second, 1);
    }

    #[test]
    fn process_get_device_id_writes_serial() {
        let (mut thread, mem) = create_thread();
        let desc = SplitDescriptor::new(0x1000, 16, VRING_DESC_F_WRITE as u16, 0);
        let chain = build_chain(&mem, &[desc]);
        let data_addr = GuestAddress(0x4000);
        let status_addr = GuestAddress(0x5000);
        let request = Request {
            request_type: RequestType::GetDeviceId,
            sector: 0,
            data_descriptors: smallvec![(data_addr, VIRTIO_BLK_ID_BYTES)],
            status_addr,
        };
        let vring = setup_vring(&mem);
        let mut vring_guard = vring.get_mut();

        thread.process_get_device_id(&request, chain, &mut vring_guard);

        let status = mem.read_obj::<u8>(status_addr).unwrap();
        assert_eq!(status, VIRTIO_BLK_S_OK as u8);
        let mut buf = vec![0u8; VIRTIO_BLK_ID_BYTES as usize];
        mem.read(&mut buf, data_addr).unwrap();
        let device_id = "ubiblk".as_bytes();
        assert_eq!(&buf[..device_id.len()], device_id);
        assert!(buf[device_id.len()..].iter().all(|byte| *byte == 0));
    }

    #[test]
    fn process_get_device_id_rejects_short_buffer() {
        let (mut thread, mem) = create_thread();
        let desc = SplitDescriptor::new(0x1000, 16, VRING_DESC_F_WRITE as u16, 0);
        let chain = build_chain(&mem, &[desc]);
        let status_addr = GuestAddress(0x5000);
        let request = Request {
            request_type: RequestType::GetDeviceId,
            sector: 0,
            data_descriptors: smallvec![(GuestAddress(0x4000), 4u32)],
            status_addr,
        };
        let vring = setup_vring(&mem);
        let mut vring_guard = vring.get_mut();

        thread.process_get_device_id(&request, chain, &mut vring_guard);

        let status = mem.read_obj::<u8>(status_addr).unwrap();
        assert_eq!(status, VIRTIO_BLK_S_IOERR as u8);
    }

    #[test]
    fn process_flush_tracks_request() {
        let (mut thread, mem) = create_thread();
        let desc = SplitDescriptor::new(0x1000, 16, VRING_DESC_F_WRITE as u16, 0);
        let chain = build_chain(&mem, &[desc]);
        let request = Request {
            request_type: RequestType::Flush,
            sector: 0,
            data_descriptors: smallvec![],
            status_addr: GuestAddress(0x5000),
        };
        let vring = setup_vring(&mem);
        let mut vring_guard = vring.get_mut();

        thread.process_flush(&request, &chain, &mut vring_guard);

        let snapshot = thread.io_tracker_snapshot();
        assert_eq!(snapshot.len(), 1);
        assert!(matches!(snapshot[0].0, IoKind::Flush));
    }
}
