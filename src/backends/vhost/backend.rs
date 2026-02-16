use std::{ops::Deref, sync::Mutex, time::Instant};

use crate::{
    backends::{common::io_tracking::IoTracker, SECTOR_SIZE},
    block_device::BlockDevice,
    config::v2,
    utils::block::{features_to_str, VirtioBlockConfig},
    Result,
};

use super::backend_thread::UbiBlkBackendThread;
use log::{debug, error, info, warn};
use vhost::vhost_user::message::*;
use vhost_user_backend::{bitmap::BitmapMmapRegion, VhostUserBackend, VringRwLock, VringT};
use virtio_bindings::{
    virtio_blk::*,
    virtio_config::VIRTIO_F_VERSION_1,
    virtio_ring::{VIRTIO_RING_F_EVENT_IDX, VIRTIO_RING_F_INDIRECT_DESC},
};
use virtio_queue::QueueT;
use vm_memory::{ByteValued, GuestAddressSpace, GuestMemoryAtomic};
use vmm_sys_util::{epoll::EventSet, eventfd::EventFd};

type GuestMemoryMmap = vm_memory::GuestMemoryMmap<BitmapMmapRegion>;

pub struct UbiBlkBackend {
    threads: Vec<Mutex<UbiBlkBackendThread>>,
    config: VirtioBlockConfig,
    queues_per_thread: Vec<u64>,
    mem: GuestMemoryAtomic<GuestMemoryMmap>,
    backend_config: v2::Config,
}

impl UbiBlkBackend {
    #[cfg(test)]
    fn threads(&self) -> &Vec<Mutex<UbiBlkBackendThread>> {
        &self.threads
    }

    pub fn new(
        config: &v2::Config,
        mem: GuestMemoryAtomic<GuestMemoryMmap>,
        block_device: Box<dyn BlockDevice>,
        alignment: usize,
        io_trackers: Vec<IoTracker>,
    ) -> Result<Self> {
        let writeback = if config.tuning.write_through { 0 } else { 1 };

        let nsectors = block_device.sector_count();
        let virtio_config = VirtioBlockConfig {
            capacity: nsectors,           /* The capacity (in SECTOR_SIZE-byte sectors). */
            blk_size: SECTOR_SIZE as u32, /* block size of device (if VIRTIO_BLK_F_BLK_SIZE) */
            size_max: config.tuning.seg_size_max, /* The maximum segment size (if VIRTIO_BLK_F_SIZE_MAX) */
            seg_max: config.tuning.seg_count_max, /* The maximum number of segments (if VIRTIO_BLK_F_SEG_MAX) */
            min_io_size: 1, /* minimum I/O size without performance penalty in logical blocks. */
            opt_io_size: 1, /* optimal sustained I/O size in logical blocks. */
            num_queues: config.tuning.num_queues as u16,
            writeback,
            ..Default::default()
        };

        info!("virtio_config: {virtio_config:?}");

        let threads = (0..config.tuning.num_queues)
            .map(|idx| {
                let io_channel = block_device.create_channel()?;
                let io_tracker = io_trackers
                    .get(idx)
                    .cloned()
                    .unwrap_or_else(|| IoTracker::new(config.tuning.queue_size));
                UbiBlkBackendThread::new(mem.clone(), io_channel, config, alignment, io_tracker)
                    .map(Mutex::new)
            })
            .collect::<Result<Vec<_>>>()?;

        let queues_per_thread = (0..config.tuning.num_queues).map(|i| 1 << i).collect();

        debug!("queues_per_thread: {queues_per_thread:?}");

        Ok(UbiBlkBackend {
            threads,
            config: virtio_config,
            queues_per_thread,
            mem,
            backend_config: config.clone(),
        })
    }

    fn maybe_pin_cpu(&self, thread: &mut UbiBlkBackendThread, thread_index: usize) -> Result<bool> {
        if let Some(ref cpus) = self.backend_config.tuning.cpus {
            thread.pin_to_cpu(cpus[thread_index])
        } else {
            Ok(false)
        }
    }
}

// This impl is mostly based on CloudHypervisor's vhost_user_block/src/lib.rs,
// which has the following copyright notice:
//
// > Copyright 2019 Red Hat, Inc. All Rights Reserved.
// >
// > Portions Copyright 2019 Intel Corporation. All Rights Reserved.
// >
// > Portions Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// >
// > Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// >
// > SPDX-License-Identifier: (Apache-2.0 AND BSD-3-Clause)
//
// You can find CloudHypervisor's code at
// https://github.com/cloud-hypervisor/cloud-hypervisor
//
// and the full text of the licenses in the LICENSES directory.
impl VhostUserBackend for UbiBlkBackend {
    type Bitmap = BitmapMmapRegion;
    type Vring = VringRwLock<GuestMemoryAtomic<GuestMemoryMmap>>;

    fn num_queues(&self) -> usize {
        self.config.num_queues as usize
    }

    fn max_queue_size(&self) -> usize {
        self.backend_config.tuning.queue_size
    }

    fn features(&self) -> u64 {
        (1 << VIRTIO_BLK_F_SEG_MAX)
            | (1 << VIRTIO_BLK_F_BLK_SIZE)
            | (1 << VIRTIO_BLK_F_SIZE_MAX)
            | (1 << VIRTIO_BLK_F_FLUSH)
            | (1 << VIRTIO_BLK_F_TOPOLOGY)
            | (1 << VIRTIO_BLK_F_MQ)
            | (1 << VIRTIO_BLK_F_CONFIG_WCE)
            | (1 << VIRTIO_RING_F_EVENT_IDX) // https://docs.oasis-open.org/virtio/virtio/v1.0/cs04/virtio-v1.0-cs04.html#x1-370007
            | (1 << VIRTIO_F_VERSION_1)
            | (1 << VIRTIO_RING_F_INDIRECT_DESC) // https://docs.oasis-open.org/virtio/virtio/v1.0/cs04/virtio-v1.0-cs04.html#x1-330003
            | VhostUserVirtioFeatures::PROTOCOL_FEATURES.bits()
    }

    fn acked_features(&self, features: u64) {
        let log = format!(
            "acked_features: 0x{:x} {}",
            features,
            features_to_str(features)
        );
        info!("{log}");
    }

    fn protocol_features(&self) -> VhostUserProtocolFeatures {
        VhostUserProtocolFeatures::CONFIG
            | VhostUserProtocolFeatures::MQ
            | VhostUserProtocolFeatures::CONFIGURE_MEM_SLOTS
    }

    // For a description of how event_idx works, see
    // - https://github.com/rust-vmm/vm-virtio/blob/4c9aa12859d72b408cf2db78426645778e8226ea/virtio-queue/src/queue.rs#L512-L520
    // - https://docs.oasis-open.org/virtio/virtio/v1.0/cs04/virtio-v1.0-cs04.html#x1-370007
    // Also from specs, virtq_avail is defined as the following. Note the used_event field.
    // struct virtq_avail {
    //   le16 flags;
    //   le16 idx;
    //   le16 ring[ /* Queue Size */ ];
    //   le16 used_event; /* Only if VIRTIO_F_EVENT_IDX */
    // };
    fn set_event_idx(&self, enabled: bool) {
        info!("set_event_idx: {enabled}");
        for thread in self.threads.iter() {
            if let Ok(mut t) = thread.lock() {
                t.event_idx = enabled;
            } else {
                error!("Failed to lock worker thread for set_event_idx");
            }
        }
    }

    // Reading event_loop.rs, device_event < vrings.len() is the vring index and
    // device_event == vrings.len() is the exit event fd. For more details, see
    // VringEpollHandler::handle_event() and
    // VringEpollHandler::register_listener().
    fn handle_event(
        &self,
        device_event: u16,
        evset: EventSet,
        vrings: &[VringRwLock<GuestMemoryAtomic<GuestMemoryMmap>>],
        thread_id: usize,
    ) -> std::result::Result<(), std::io::Error> {
        if evset != EventSet::IN {
            return Err(std::io::Error::other(format!(
                "Invalid event set: {evset:?}"
            )));
        }

        let mut thread = self.threads[thread_id]
            .lock()
            .map_err(|_| std::io::Error::other("Thread lock poisoned"))?;

        if let Err(e) = self.maybe_pin_cpu(&mut thread, thread_id) {
            error!("Failed to pin thread {} to CPU: {e}", thread_id);
        }

        match device_event {
            0 => {
                let mut vring = vrings[0].get_mut();

                // Actively poll the queue until poll_queue_timeout_us has passed
                // without seeing a new request.
                let mut now = Instant::now();
                loop {
                    if thread.process_queue(&mut vring) {
                        now = Instant::now();
                    } else if now.elapsed().as_micros()
                        > self.backend_config.tuning.poll_timeout_us as u128
                    {
                        break;
                    }
                }

                if thread.event_idx {
                    // vm-virtio's Queue implementation only checks avail_index
                    // once, so to properly support EVENT_IDX we need to keep
                    // calling process_queue() until it stops finding new
                    // requests on the queue.
                    loop {
                        vring
                            .get_queue_mut()
                            .enable_notification(self.mem.memory().deref())
                            .map_err(|e| {
                                std::io::Error::other(format!("enable_notification failed: {e:?}"))
                            })?;
                        if !thread.process_queue(&mut vring) {
                            break;
                        }
                    }
                } else {
                    // Without EVENT_IDX, a single call is enough.
                    thread.process_queue(&mut vring);
                }

                Ok(())
            }
            _ => Err(std::io::Error::other(format!(
                "Invalid device event: {device_event}"
            ))),
        }
    }

    fn get_config(&self, _offset: u32, size: u32) -> Vec<u8> {
        // 1. QEMU (tag v8.2.2):
        //    a. sets offset to 0 at vhost_user_get_config
        //       (hw/virtio/vhost-user.c:2414)
        //    b. calculates size dynamically based on available features in
        //       virtio_get_config_size (hw/virtio/virtio.c:2956). This can be
        //       less than the full config struct size.
        // 2. Cloud-Hypervisor (tag v46.0):
        //    a. sets offset to VHOST_USER_CONFIG_OFFSET (0x100), which is the
        //       starting position of the device configuration space in virtio
        //       devices (virtio-devices/src/vhost_user/blk.rs:147)
        //    b. always sets size to the full config struct size
        //       (virtio-devices/src/vhost_user/blk.rs:142)
        // 3. vhost-user spec's requirement for VHOST_USER_GET_CONFIG:
        //    > vhost-user back-end’s payload size MUST match the front-end’s
        //    > request
        // Based on above, we ignore the offset and return the first "size"
        // bytes of the config struct, which works for both QEMU and
        // Cloud-Hypervisor.
        let config_bytes = self.config.as_slice();
        let requested_size = size as usize;
        if size as usize > config_bytes.len() {
            warn!(
                "get_config requested size {size} exceeds config struct size {}, padding with zeros",
                config_bytes.len()
            );
        }
        let mut buf = vec![0u8; requested_size];
        let copy_len = std::cmp::min(requested_size, config_bytes.len());
        buf[..copy_len].copy_from_slice(&config_bytes[..copy_len]);
        buf
    }

    fn exit_event(&self, thread_index: usize) -> Option<EventFd> {
        self.threads[thread_index]
            .lock()
            .ok()
            .and_then(|t| t.kill_evt.try_clone().ok())
    }

    fn queues_per_thread(&self) -> Vec<u64> {
        self.queues_per_thread.clone()
    }

    fn update_memory(
        &self,
        _mem: GuestMemoryAtomic<GuestMemoryMmap>,
    ) -> std::result::Result<(), std::io::Error> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::os::fd::AsRawFd;

    use super::*;
    use crate::config::v2::{self, DeviceSection};
    use crate::{
        backends::init_metadata, block_device::bdev_test::TestBlockDevice,
        utils::aligned_buffer::BUFFER_ALIGNMENT,
    };
    use virtio_bindings::bindings::virtio_ring::{VRING_DESC_F_NEXT, VRING_DESC_F_WRITE};
    use virtio_bindings::virtio_blk::{VIRTIO_BLK_ID_BYTES, VIRTIO_BLK_S_OK, VIRTIO_BLK_T_GET_ID};
    use virtio_queue::desc::{split::Descriptor as SplitDescriptor, RawDescriptor};
    use virtio_queue::mock::MockSplitQueue;
    use vm_memory::{Address, Bytes, GuestAddress};

    const DEFAULT_NUM_QUEUES: usize = 1;
    fn default_config(path: String) -> v2::Config {
        v2::Config {
            device: DeviceSection {
                data_path: path.into(),
                vhost_socket: Some("/tmp/vhost.sock".into()),
                rpc_socket: Some("/tmp/rpc.sock".into()),
                device_id: "ubiblk-test".to_string(),
                track_written: false,
                metadata_path: None,
            },
            stripe_source: None,
            secrets: std::collections::HashMap::new(),
            tuning: v2::tuning::TuningSection::default(),
            encryption: None,
            danger_zone: v2::DangerZone {
                enabled: true,
                allow_unencrypted_disk: true,
                allow_inline_plaintext_secrets: true,
                allow_secret_over_regular_file: true,
                allow_unencrypted_connection: true,
                allow_env_secrets: false,
            },
        }
    }

    fn build_backend(config: &v2::Config) -> Result<UbiBlkBackend> {
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        UbiBlkBackend::new(config, mem, block_device, BUFFER_ALIGNMENT, vec![])
    }

    fn default_backend() -> UbiBlkBackend {
        let config = default_config("img".to_string());
        build_backend(&config).unwrap()
    }

    fn setup_mem() -> (GuestMemoryAtomic<GuestMemoryMmap>, GuestMemoryMmap) {
        let mem = GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let gm = GuestMemoryAtomic::new(mem.clone());
        (gm, mem)
    }

    /// Ensure a backend can be created with valid parameters and exposes expected features.
    #[test]
    fn backend_features_and_protocol() {
        let backend = default_backend();
        assert_eq!(backend.num_queues(), 1);
        assert_eq!(backend.max_queue_size(), 64);

        let features = backend.features();
        assert!(features & (1 << VIRTIO_BLK_F_FLUSH) != 0);
        let protocol = backend.protocol_features();
        assert!(protocol.contains(VhostUserProtocolFeatures::CONFIG));
    }

    /// Updating event index should propagate to all worker threads.
    #[test]
    fn set_event_index() {
        let backend = default_backend();
        backend.set_event_idx(true);
        for thread in backend.threads().iter() {
            assert!(thread.lock().unwrap().event_idx);
        }
    }

    /// handle_event should reject unexpected event sets.
    #[test]
    fn handle_event_invalid_eventset() {
        let backend = default_backend();
        let err = backend.handle_event(0, EventSet::OUT, &[], 0).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::Other);
    }

    /// handle_event should reject device events other than 0.
    #[test]
    fn handle_event_invalid_device() {
        let backend = default_backend();
        let err = backend.handle_event(1, EventSet::IN, &[], 0).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::Other);
    }

    /// handle_event should process a valid queue request.
    #[test]
    fn handle_event_processes_get_id() {
        let (gm, mem) = setup_mem();
        let mut config = default_config("img".to_string());
        config.tuning.queue_size = 8;
        config.device.device_id = "ubiblk-test".to_string();
        let block_device = Box::new(TestBlockDevice::new(SECTOR_SIZE as u64 * 8));
        let backend =
            UbiBlkBackend::new(&config, gm, block_device, BUFFER_ALIGNMENT, vec![]).unwrap();

        let queue = MockSplitQueue::new(&mem, config.tuning.queue_size as u16);
        let header_addr = GuestAddress(0x1000);
        let data_addr = GuestAddress(0x2000);
        let status_addr = GuestAddress(0x3000);
        mem.write_obj::<u32>(VIRTIO_BLK_T_GET_ID, header_addr)
            .unwrap();
        mem.write_obj::<u32>(0, header_addr.unchecked_add(4))
            .unwrap();
        mem.write_obj::<u64>(0, header_addr.unchecked_add(8))
            .unwrap();

        let descs = [
            RawDescriptor::from(SplitDescriptor::new(
                header_addr.0,
                16,
                VRING_DESC_F_NEXT as u16,
                1,
            )),
            RawDescriptor::from(SplitDescriptor::new(
                data_addr.0,
                VIRTIO_BLK_ID_BYTES,
                (VRING_DESC_F_WRITE | VRING_DESC_F_NEXT) as u16,
                2,
            )),
            RawDescriptor::from(SplitDescriptor::new(
                status_addr.0,
                1,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
        ];
        queue.add_desc_chains(&descs, 0).unwrap();

        let vring = VringRwLock::new(
            GuestMemoryAtomic::new(mem.clone()),
            config.tuning.queue_size as u16,
        )
        .expect("vring new failed");
        vring.set_queue_size(config.tuning.queue_size as u16);
        vring
            .set_queue_info(
                queue.desc_table_addr().0,
                queue.avail_addr().0,
                queue.used_addr().0,
            )
            .expect("set_queue_info failed");
        vring.set_queue_ready(true);

        backend
            .handle_event(0, EventSet::IN, &[vring], 0)
            .expect("handle_event failed");

        let status = mem.read_obj::<u8>(status_addr).unwrap();
        assert_eq!(status, VIRTIO_BLK_S_OK as u8);

        let mut buf = [0u8; VIRTIO_BLK_ID_BYTES as usize];
        mem.read_slice(&mut buf, data_addr).unwrap();
        assert_eq!(
            &buf[..config.device.device_id.len()],
            config.device.device_id.as_bytes()
        );
    }

    /// init_metadata should fail when metadata_path is missing.
    #[test]
    fn init_metadata_missing_path() {
        let config = default_config("img".to_string());
        let res = init_metadata(&config, 4);
        assert!(res.is_err());
    }

    /// The features method should advertise common virtio features.
    #[test]
    fn features_advertise_bits() {
        let backend = default_backend();

        let features = backend.features();
        use virtio_bindings::virtio_config::VIRTIO_F_VERSION_1;
        use virtio_bindings::virtio_ring::VIRTIO_RING_F_EVENT_IDX;
        assert!(features & (1 << VIRTIO_F_VERSION_1) != 0);
        assert!(features & (1 << VIRTIO_RING_F_EVENT_IDX) != 0);
    }

    /// acked_features should accept arbitrary feature flags without panicking.
    #[test]
    fn acked_features_noop() {
        let backend = default_backend();
        backend.acked_features(1 << VIRTIO_BLK_F_FLUSH);
    }

    /// set_event_idx(false) should clear the flag on all worker threads.
    #[test]
    fn clear_event_index() {
        let backend = default_backend();
        backend.set_event_idx(true);
        backend.set_event_idx(false);
        for thread in backend.threads().iter() {
            assert!(!thread.lock().unwrap().event_idx);
        }
    }

    /// get_config should return a valid VirtioBlockConfig structure.
    #[test]
    fn get_config_returns_struct() {
        let backend = default_backend();

        let bytes = backend.get_config(0, std::mem::size_of::<VirtioBlockConfig>() as u32);
        assert_eq!(bytes.len(), std::mem::size_of::<VirtioBlockConfig>());
        let virtio_config: VirtioBlockConfig = *VirtioBlockConfig::from_slice(&bytes).unwrap();
        let capacity = virtio_config.capacity;
        let blk_size = virtio_config.blk_size;
        let queues = virtio_config.num_queues;
        assert_eq!(capacity, 8);
        assert_eq!(blk_size, SECTOR_SIZE as u32);
        assert_eq!(queues as usize, DEFAULT_NUM_QUEUES);
    }

    /// queues_per_thread should reflect the number of queues configured.
    #[test]
    fn queues_per_thread_multiple() {
        let mut config = default_config("img".to_string());
        config.tuning.num_queues = 3;
        config.tuning.cpus = None;
        let backend = build_backend(&config).unwrap();

        assert_eq!(backend.queues_per_thread(), vec![1, 2, 4]);
    }

    /// update_memory is currently a no-op and should succeed.
    #[test]
    fn update_memory_nop() {
        let backend = default_backend();
        let mem2: GuestMemoryAtomic<vm_memory::GuestMemoryMmap<BitmapMmapRegion>> =
            GuestMemoryAtomic::new(GuestMemoryMmap::new());
        assert!(backend.update_memory(mem2).is_ok());
    }

    /// exit_event should return a clone of the worker thread's kill event fd.
    #[test]
    fn exit_event_clone() {
        let backend = default_backend();
        let evt1 = backend.exit_event(0).unwrap();
        let evt2 = backend.exit_event(0).unwrap();
        assert_ne!(evt1.as_raw_fd(), evt2.as_raw_fd());
    }

    /// maybe_pin_cpu should return Ok(false) when no CPUs are configured.
    #[test]
    fn maybe_pin_cpu_no_cpus() {
        let backend = default_backend();
        let mut thread = backend.threads()[0].lock().unwrap();
        let res = backend.maybe_pin_cpu(&mut thread, 0).unwrap();
        assert!(!res);
    }

    /// maybe_pin_cpu should return Ok(true) when pinning is successful.
    #[test]
    fn maybe_pin_cpu_success() {
        let mut config = default_config("img".to_string());
        config.tuning.cpus = Some(vec![0]);
        let backend = build_backend(&config).unwrap();
        let mut thread = backend.threads()[0].lock().unwrap();
        let res = backend.maybe_pin_cpu(&mut thread, 0).unwrap();
        assert!(res);
    }

    /// maybe_pin_cpu should return Err when pinning fails.
    #[test]
    fn maybe_pin_cpu_failure() {
        let mut config = default_config("img".to_string());
        // Assuming CPU 9999 does not exist on the system.
        config.tuning.cpus = Some(vec![9999]);
        let backend = build_backend(&config).unwrap();
        let mut thread = backend.threads()[0].lock().unwrap();
        let res = backend.maybe_pin_cpu(&mut thread, 0);
        assert!(res.is_err());
    }

    #[test]
    fn test_get_config() {
        let backend = default_backend();

        // Test with offset 0 and full size
        let bytes = backend.get_config(0, std::mem::size_of::<VirtioBlockConfig>() as u32);
        assert_eq!(bytes.len(), std::mem::size_of::<VirtioBlockConfig>());

        // Test with non-zero offset (should be ignored) and full size
        let bytes = backend.get_config(0x100, std::mem::size_of::<VirtioBlockConfig>() as u32);
        assert_eq!(bytes.len(), std::mem::size_of::<VirtioBlockConfig>());

        // Test with offset 0 and smaller size
        let bytes = backend.get_config(0, 16);
        assert_eq!(bytes.len(), 16);

        // Test with non-zero offset and smaller size
        let bytes = backend.get_config(0x100, 16);
        assert_eq!(bytes.len(), 16);

        // Test with size larger than config struct
        let bytes = backend.get_config(0, (std::mem::size_of::<VirtioBlockConfig>() + 16) as u32);
        assert_eq!(bytes.len(), std::mem::size_of::<VirtioBlockConfig>() + 16);
        assert!(bytes[std::mem::size_of::<VirtioBlockConfig>()..]
            .iter()
            .all(|&b| b == 0));
    }
}
