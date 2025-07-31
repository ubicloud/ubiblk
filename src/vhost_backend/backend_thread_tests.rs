#[cfg(test)]
mod tests {
    use crate::block_device::bdev_test::TestBlockDevice;
    use crate::block_device::BlockDevice;
    use crate::utils::aligned_buffer::BUFFER_ALIGNMENT;
    use crate::vhost_backend::backend_thread::UbiBlkBackendThread;
    use crate::vhost_backend::request::{Request, RequestType};
    use crate::vhost_backend::{Options, SECTOR_SIZE};
    use smallvec::smallvec;
    use vhost_user_backend::bitmap::BitmapMmapRegion;
    use vhost_user_backend::VringT;
    use virtio_bindings::bindings::virtio_ring::VRING_DESC_F_NEXT;
    use virtio_bindings::bindings::virtio_ring::VRING_DESC_F_WRITE;
    use virtio_bindings::virtio_blk::{
        VIRTIO_BLK_S_OK, VIRTIO_BLK_T_FLUSH, VIRTIO_BLK_T_IN, VIRTIO_BLK_T_OUT,
    };
    use virtio_queue::desc::split::Descriptor as SplitDescriptor;
    use virtio_queue::{Queue, QueueOwnedT};
    use vm_memory::{
        Address, Bytes, GuestAddress, GuestAddressSpace, GuestMemoryAtomic, GuestMemoryLoadGuard,
        GuestMemoryMmap,
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

    fn default_options(path: &str) -> Options {
        Options {
            path: path.to_string(),
            image_path: None,
            metadata_path: None,
            io_debug_path: None,
            socket: "sock".to_string(),
            num_queues: 1,
            queue_size: 2,
            seg_size_max: 512,
            seg_count_max: 1,
            poll_queue_timeout_us: 1000,
            skip_sync: false,
            copy_on_read: false,
            direct_io: false,
            encryption_key: None,
            device_id: "ubiblk".to_string(),
        }
    }

    fn create_thread() -> (UbiBlkBackendThread, GuestMemory) {
        let (gm, mem) = setup_mem();
        let opts = default_options("img");
        let device = TestBlockDevice::new(SECTOR_SIZE as u64 * 8);
        let io_channel = device.create_channel().unwrap();
        let thread = UbiBlkBackendThread::new(gm, io_channel, &opts, BUFFER_ALIGNMENT).unwrap();
        (thread, mem)
    }

    fn create_thread_with_device(
        opts: Options,
    ) -> (
        UbiBlkBackendThread,
        GuestMemoryAtomic<GuestMemory>,
        GuestMemory,
        TestBlockDevice,
    ) {
        let (gm, mem) = setup_mem();
        let device = TestBlockDevice::new(SECTOR_SIZE as u64 * 8);
        let io_channel = device.create_channel().unwrap();
        let thread =
            UbiBlkBackendThread::new(gm.clone(), io_channel, &opts, BUFFER_ALIGNMENT).unwrap();
        (thread, gm, mem, device)
    }

    fn create_vring<'a>(
        gm: GuestMemoryAtomic<GuestMemory>,
        vq: &virtio_queue::mock::MockSplitQueue<'a, GuestMemory>,
        len: u16,
    ) -> vhost_user_backend::VringRwLock<GuestMemoryAtomic<GuestMemory>> {
        let vring = vhost_user_backend::VringRwLock::new(gm, len).unwrap();
        vring
            .set_queue_info(vq.desc_table_addr().0, vq.avail_addr().0, vq.used_addr().0)
            .unwrap();
        vring.set_queue_size(len);
        vring.set_queue_ready(true);
        vring.set_queue_next_avail(0);
        vring.set_queue_next_used(0);
        vring
    }

    #[test]
    fn request_len_sums_descriptors() {
        let (thread, _mem) = create_thread();
        let req = Request {
            request_type: RequestType::Out,
            sector: 0,
            data_descriptors: smallvec![(GuestAddress(0), 100u32), (GuestAddress(512), 200u32),],
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
    fn process_write_writes_data() {
        let opts = default_options("img");
        let (mut thread, gm, mem, device) = create_thread_with_device(opts);

        let hdr = GuestAddress(0x1000);
        let data = GuestAddress(0x2000);
        let status = GuestAddress(0x3000);

        mem.write_obj::<u32>(VIRTIO_BLK_T_OUT, hdr).unwrap();
        mem.write_obj::<u32>(0, hdr.unchecked_add(4)).unwrap();
        mem.write_obj::<u64>(0, hdr.unchecked_add(8)).unwrap();

        let pattern = [0xAAu8; SECTOR_SIZE];
        mem.write_slice(&pattern, data).unwrap();

        use virtio_queue::desc::RawDescriptor;
        use virtio_queue::mock::MockSplitQueue;

        let vq = MockSplitQueue::new(&mem, 16);
        let descs = [
            SplitDescriptor::new(hdr.0, 16, VRING_DESC_F_NEXT as u16, 1),
            SplitDescriptor::new(data.0, SECTOR_SIZE as u32, VRING_DESC_F_NEXT as u16, 2),
            SplitDescriptor::new(status.0, 1, VRING_DESC_F_WRITE as u16, 0),
        ];
        let raw_descs: Vec<RawDescriptor> =
            descs.iter().cloned().map(RawDescriptor::from).collect();
        vq.add_desc_chains(&raw_descs, 0).unwrap();

        let vring_lock = create_vring(gm, &vq, 16);
        {
            let mut vring = vring_lock.get_mut();
            thread.process_queue(&mut vring);
        }

        let mut out = vec![0u8; SECTOR_SIZE];
        device.read(0, &mut out, SECTOR_SIZE);
        assert_eq!(out.as_slice(), &pattern);
        assert_eq!(mem.read_obj::<u8>(status).unwrap(), VIRTIO_BLK_S_OK as u8);
        assert_eq!(device.metrics.read().unwrap().writes, 1);
    }

    #[test]
    fn process_read_reads_data() {
        let opts = default_options("img");
        let (mut thread, gm, mem, device) = create_thread_with_device(opts);

        let hdr = GuestAddress(0x1000);
        let data = GuestAddress(0x2000);
        let status = GuestAddress(0x3000);

        mem.write_obj::<u32>(VIRTIO_BLK_T_IN, hdr).unwrap();
        mem.write_obj::<u32>(0, hdr.unchecked_add(4)).unwrap();
        mem.write_obj::<u64>(0, hdr.unchecked_add(8)).unwrap();

        let pattern = [0x55u8; SECTOR_SIZE];
        device.write(0, &pattern, SECTOR_SIZE);

        use virtio_queue::desc::RawDescriptor;
        use virtio_queue::mock::MockSplitQueue;

        let vq = MockSplitQueue::new(&mem, 16);
        let descs = [
            SplitDescriptor::new(hdr.0, 16, VRING_DESC_F_NEXT as u16, 1),
            SplitDescriptor::new(
                data.0,
                SECTOR_SIZE as u32,
                VRING_DESC_F_WRITE as u16 | VRING_DESC_F_NEXT as u16,
                2,
            ),
            SplitDescriptor::new(status.0, 1, VRING_DESC_F_WRITE as u16, 0),
        ];
        let raw_descs: Vec<RawDescriptor> =
            descs.iter().cloned().map(RawDescriptor::from).collect();
        vq.add_desc_chains(&raw_descs, 0).unwrap();

        let vring_lock = create_vring(gm, &vq, 16);
        {
            let mut vring = vring_lock.get_mut();
            thread.process_queue(&mut vring);
        }

        let mut buf = vec![0u8; SECTOR_SIZE];
        mem.read_slice(&mut buf, data).unwrap();
        assert_eq!(buf.as_slice(), &pattern);
        assert_eq!(mem.read_obj::<u8>(status).unwrap(), VIRTIO_BLK_S_OK as u8);
        assert_eq!(device.metrics.read().unwrap().reads, 1);
    }

    #[test]
    fn process_flush_flushes_device() {
        let mut opts = default_options("img");
        opts.skip_sync = false;
        let (mut thread, gm, mem, device) = create_thread_with_device(opts);

        let hdr = GuestAddress(0x1000);
        let status = GuestAddress(0x3000);

        mem.write_obj::<u32>(VIRTIO_BLK_T_FLUSH, hdr).unwrap();
        mem.write_obj::<u32>(0, hdr.unchecked_add(4)).unwrap();
        mem.write_obj::<u64>(0, hdr.unchecked_add(8)).unwrap();

        use virtio_queue::desc::RawDescriptor;
        use virtio_queue::mock::MockSplitQueue;

        let vq = MockSplitQueue::new(&mem, 16);
        let descs = [
            SplitDescriptor::new(hdr.0, 16, VRING_DESC_F_NEXT as u16, 1),
            SplitDescriptor::new(status.0, 1, VRING_DESC_F_WRITE as u16, 0),
        ];
        let raw_descs: Vec<RawDescriptor> =
            descs.iter().cloned().map(RawDescriptor::from).collect();
        vq.add_desc_chains(&raw_descs, 0).unwrap();

        let vring_lock = create_vring(gm, &vq, 16);
        {
            let mut vring = vring_lock.get_mut();
            thread.process_queue(&mut vring);
        }

        assert_eq!(mem.read_obj::<u8>(status).unwrap(), VIRTIO_BLK_S_OK as u8);
        assert_eq!(device.metrics.read().unwrap().flushes, 1);
    }
}
