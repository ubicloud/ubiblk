#[cfg(test)]
mod tests {
    use nix::sched::{sched_getaffinity, sched_setaffinity};
    use nix::unistd::Pid;
    use smallvec::smallvec;
    use vhost_user_backend::{bitmap::BitmapMmapRegion, VringRwLock, VringT};
    use virtio_bindings::bindings::virtio_ring::{VRING_DESC_F_NEXT, VRING_DESC_F_WRITE};
    use virtio_bindings::virtio_blk::{
        VIRTIO_BLK_ID_BYTES, VIRTIO_BLK_S_IOERR, VIRTIO_BLK_S_OK, VIRTIO_BLK_T_IN, VIRTIO_BLK_T_OUT,
    };
    use virtio_queue::{
        desc::{split::Descriptor as SplitDescriptor, RawDescriptor},
        mock::MockSplitQueue,
        Queue, QueueOwnedT,
    };
    use vm_memory::{
        Address, Bytes, GuestAddress, GuestAddressSpace, GuestMemoryAtomic, GuestMemoryLoadGuard,
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

    fn setup_vring_with_queue(
        mem: &GuestMemory,
        queue_size: u16,
        queue: &MockSplitQueue<'_, GuestMemory>,
    ) -> VringRwLock<GuestMemoryAtomic<GuestMemory>> {
        let vring = VringRwLock::new(GuestMemoryAtomic::new(mem.clone()), queue_size)
            .expect("vring new failed");
        vring.set_queue_size(queue_size);
        vring
            .set_queue_info(
                queue.desc_table_addr().0,
                queue.avail_addr().0,
                queue.used_addr().0,
            )
            .expect("set_queue_info failed");
        vring.set_queue_ready(true);
        vring
    }

    struct QueueRequestAddrs {
        data: GuestAddress,
        status: GuestAddress,
    }

    fn setup_queue_request(
        mem: &GuestMemory,
        queue: &MockSplitQueue<'_, GuestMemory>,
        base_addr: u64,
        request_type: u32,
        sector: u64,
        data_len: u32,
        data_flags: u16,
    ) -> QueueRequestAddrs {
        let hdr = GuestAddress(base_addr);
        let data = GuestAddress(base_addr + 0x1000);
        let status = GuestAddress(base_addr + 0x2000);
        mem.write_obj::<u32>(request_type, hdr).unwrap();
        mem.write_obj::<u32>(0, hdr.unchecked_add(4)).unwrap();
        mem.write_obj::<u64>(sector, hdr.unchecked_add(8)).unwrap();

        let descs = [
            RawDescriptor::from(SplitDescriptor::new(hdr.0, 16, VRING_DESC_F_NEXT as u16, 1)),
            RawDescriptor::from(SplitDescriptor::new(
                data.0,
                data_len,
                data_flags | VRING_DESC_F_NEXT as u16,
                2,
            )),
            RawDescriptor::from(SplitDescriptor::new(
                status.0,
                1,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
        ];
        queue.add_desc_chains(&descs, 0).unwrap();

        QueueRequestAddrs { data, status }
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
        let (thread, mem, _device) = create_thread_with_device();
        (thread, mem)
    }

    fn create_thread_with_device() -> (UbiBlkBackendThread, GuestMemory, TestBlockDevice) {
        let (gm, mem) = setup_mem();
        let opts = default_options("img");
        let device = TestBlockDevice::new(SECTOR_SIZE as u64 * 8);
        let io_channel = device.create_channel().unwrap();
        let thread =
            UbiBlkBackendThread::new(gm, io_channel, &opts, BUFFER_ALIGNMENT, IoTracker::new(64))
                .unwrap();
        (thread, mem, device)
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

    #[test]
    fn process_queue_reads_into_guest() {
        let (mut thread, mem, device) = create_thread_with_device();
        let queue = MockSplitQueue::new(&mem, 16);
        let vring = setup_vring_with_queue(&mem, 16, &queue);
        let addrs = setup_queue_request(
            &mem,
            &queue,
            0x1000,
            VIRTIO_BLK_T_IN,
            0,
            SECTOR_SIZE as u32,
            VRING_DESC_F_WRITE as u16,
        );

        let pattern = vec![0x5a; SECTOR_SIZE];
        device.write(0, &pattern, pattern.len());

        let mut vring_guard = vring.get_mut();
        assert!(thread.process_queue(&mut vring_guard));

        let status_val = mem.read_obj::<u8>(addrs.status).unwrap();
        assert_eq!(status_val, VIRTIO_BLK_S_OK as u8);
        let mut buf = vec![0u8; SECTOR_SIZE];
        mem.read(&mut buf, addrs.data).unwrap();
        assert_eq!(buf, pattern);

        let metrics = device.metrics.read().unwrap();
        assert_eq!(metrics.reads, 1);
    }

    #[test]
    fn process_queue_writes_from_guest() {
        let (mut thread, mem, device) = create_thread_with_device();
        let queue = MockSplitQueue::new(&mem, 16);
        let vring = setup_vring_with_queue(&mem, 16, &queue);
        let addrs = setup_queue_request(
            &mem,
            &queue,
            0x1100,
            VIRTIO_BLK_T_OUT,
            0,
            SECTOR_SIZE as u32,
            0,
        );

        let pattern = vec![0xa5; SECTOR_SIZE];
        mem.write(&pattern, addrs.data).unwrap();

        let mut vring_guard = vring.get_mut();
        assert!(thread.process_queue(&mut vring_guard));

        let status_val = mem.read_obj::<u8>(addrs.status).unwrap();
        assert_eq!(status_val, VIRTIO_BLK_S_OK as u8);
        let mut out = vec![0u8; SECTOR_SIZE];
        device.read(0, &mut out, SECTOR_SIZE);
        assert_eq!(out, pattern);

        let metrics = device.metrics.read().unwrap();
        assert_eq!(metrics.writes, 1);
    }

    #[test]
    fn process_queue_rejects_unaligned_write() {
        let (mut thread, mem, device) = create_thread_with_device();
        let queue = MockSplitQueue::new(&mem, 16);
        let vring = setup_vring_with_queue(&mem, 16, &queue);
        let addrs = setup_queue_request(&mem, &queue, 0x1400, VIRTIO_BLK_T_OUT, 0, 1, 0);

        mem.write(&[0xff], addrs.data).unwrap();

        let mut vring_guard = vring.get_mut();
        assert!(thread.process_queue(&mut vring_guard));

        let status_val = mem.read_obj::<u8>(addrs.status).unwrap();
        assert_eq!(status_val, VIRTIO_BLK_S_IOERR as u8);
        let metrics = device.metrics.read().unwrap();
        assert_eq!(metrics.writes, 0);
    }

    #[test]
    fn process_queue_rejects_unaligned_read() {
        let (mut thread, mem, device) = create_thread_with_device();
        let queue = MockSplitQueue::new(&mem, 16);
        let vring = setup_vring_with_queue(&mem, 16, &queue);
        let addrs = setup_queue_request(
            &mem,
            &queue,
            0x1500,
            VIRTIO_BLK_T_IN,
            0,
            1,
            VRING_DESC_F_WRITE as u16,
        );

        let mut vring_guard = vring.get_mut();
        assert!(thread.process_queue(&mut vring_guard));

        let status_val = mem.read_obj::<u8>(addrs.status).unwrap();
        assert_eq!(status_val, VIRTIO_BLK_S_IOERR as u8);
        let metrics = device.metrics.read().unwrap();
        assert_eq!(metrics.reads, 0);
    }

    #[test]
    fn pin_cpu_returns_early_if_pin_attempted() {
        let (mut thread, _mem) = create_thread();
        thread.pin_attempted = true;
        let result = thread.pin_to_cpu(0);
        assert!(result.is_ok());
    }

    #[test]
    fn pin_cpu_fails_on_invalid_cpu() {
        let (mut thread, _mem) = create_thread();
        let result = thread.pin_to_cpu(9999); // assuming this CPU doesn't exist
        assert!(result.is_err());
    }

    #[test]
    fn pin_cpu_succeeds_on_valid_cpu() {
        let orig_affinity = sched_getaffinity(Pid::from_raw(0)).unwrap();

        let (mut thread, _mem) = create_thread();
        let result = thread.pin_to_cpu(0); // assuming CPU 0 exists
        assert!(result.is_ok());

        // restore original affinity
        sched_setaffinity(Pid::from_raw(0), &orig_affinity).unwrap();
    }
}
