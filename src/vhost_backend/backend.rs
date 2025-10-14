use std::{ops::Deref, path::PathBuf, sync::Mutex, time::Instant};

use crate::{
    block_device::{self, BlockDevice, UringBlockDevice},
    vhost_backend::SECTOR_SIZE,
};
use crate::{
    utils::block::{features_to_str, VirtioBlockConfig},
    VhostUserBlockError,
};

use super::{backend_thread::UbiBlkBackendThread, KeyEncryptionCipher, Options};
use crate::block_device::{init_metadata as init_metadata_file, UbiMetadata};
use crate::Result;
use log::{debug, error, info};
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

pub(super) type GuestMemoryMmap = vm_memory::GuestMemoryMmap<BitmapMmapRegion>;

pub struct UbiBlkBackend {
    threads: Vec<Mutex<UbiBlkBackendThread>>,
    config: VirtioBlockConfig,
    queues_per_thread: Vec<u64>,
    mem: GuestMemoryAtomic<GuestMemoryMmap>,
    options: Options,
}

#[cfg(test)]
impl UbiBlkBackend {
    pub fn threads(&self) -> &Vec<Mutex<UbiBlkBackendThread>> {
        &self.threads
    }
}

impl UbiBlkBackend {
    fn validate_options(options: &Options) -> Result<()> {
        if options.queue_size == 0 || !options.queue_size.is_power_of_two() {
            return Err(VhostUserBlockError::InvalidParameter {
                description: format!(
                    "queue_size {} is not a non-zero power of two",
                    options.queue_size
                ),
            });
        }

        if let Some(ref cpus) = options.cpus {
            if cpus.len() != options.num_queues {
                return Err(VhostUserBlockError::InvalidParameter {
                    description: "cpus length must equal num_queues".to_string(),
                });
            }
        }

        Ok(())
    }

    pub fn new(
        options: &Options,
        mem: GuestMemoryAtomic<GuestMemoryMmap>,
        block_device: Box<dyn BlockDevice>,
        alignment: usize,
    ) -> Result<Self> {
        Self::validate_options(options)?;

        let writeback = if options.write_through { 0 } else { 1 };

        let nsectors = block_device.sector_count();
        let virtio_config = VirtioBlockConfig {
            capacity: nsectors,             /* The capacity (in SECTOR_SIZE-byte sectors). */
            blk_size: SECTOR_SIZE as u32,   /* block size of device (if VIRTIO_BLK_F_BLK_SIZE) */
            size_max: options.seg_size_max, /* The maximum segment size (if VIRTIO_BLK_F_SIZE_MAX) */
            seg_max: options.seg_count_max, /* The maximum number of segments (if VIRTIO_BLK_F_SEG_MAX) */
            min_io_size: 1, /* minimum I/O size without performance penalty in logical blocks. */
            opt_io_size: 1, /* optimal sustained I/O size in logical blocks. */
            num_queues: options.num_queues as u16,
            writeback,
            ..Default::default()
        };

        info!("virtio_config: {virtio_config:?}");

        let threads = (0..options.num_queues)
            .map(|_| {
                let io_channel = block_device.create_channel()?;
                UbiBlkBackendThread::new(mem.clone(), io_channel, options, alignment)
                    .map(Mutex::new)
            })
            .collect::<Result<Vec<_>>>()?;

        let queues_per_thread = (0..options.num_queues).map(|i| 1 << i).collect();

        debug!("queues_per_thread: {queues_per_thread:?}");

        Ok(UbiBlkBackend {
            threads,
            config: virtio_config,
            queues_per_thread,
            mem,
            options: options.clone(),
        })
    }

    pub(super) fn worker_threads(&self) -> &[Mutex<UbiBlkBackendThread>] {
        &self.threads
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
impl VhostUserBackend for UbiBlkBackend {
    type Bitmap = BitmapMmapRegion;
    type Vring = VringRwLock<GuestMemoryAtomic<GuestMemoryMmap>>;

    fn num_queues(&self) -> usize {
        self.config.num_queues as usize
    }

    fn max_queue_size(&self) -> usize {
        self.options.queue_size
    }

    fn features(&self) -> u64 {
        let avail_features = (1 << VIRTIO_BLK_F_SEG_MAX)
            | (1 << VIRTIO_BLK_F_BLK_SIZE)
            | (1 << VIRTIO_BLK_F_SIZE_MAX)
            | (1 << VIRTIO_BLK_F_FLUSH)
            | (1 << VIRTIO_BLK_F_TOPOLOGY)
            | (1 << VIRTIO_BLK_F_MQ)
            | (1 << VIRTIO_BLK_F_CONFIG_WCE)
            | (1 << VIRTIO_RING_F_EVENT_IDX) // https://docs.oasis-open.org/virtio/virtio/v1.0/cs04/virtio-v1.0-cs04.html#x1-370007
            | (1 << VIRTIO_F_VERSION_1)
            | (1 << VIRTIO_RING_F_INDIRECT_DESC) // https://docs.oasis-open.org/virtio/virtio/v1.0/cs04/virtio-v1.0-cs04.html#x1-330003
            | VhostUserVirtioFeatures::PROTOCOL_FEATURES.bits();

        info!(
            "avail_features: {}",
            features_to_str(avail_features).trim_end()
        );
        avail_features
    }

    fn acked_features(&self, features: u64) {
        info!(
            "acked_features: 0x{:x} {}",
            features,
            features_to_str(features).trim_end()
        );
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

        if let Some(cpus) = &self.options.cpus {
            thread.pin_to_cpu(cpus[thread_id]);
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
                    } else if now.elapsed().as_micros() > self.options.poll_queue_timeout_us {
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

    fn get_config(&self, _offset: u32, _size: u32) -> Vec<u8> {
        self.config.as_slice().to_vec()
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

pub(super) fn build_block_device(
    path: &str,
    options: &Options,
    kek: KeyEncryptionCipher,
) -> Result<Box<dyn BlockDevice>> {
    let mut block_device: Box<dyn BlockDevice> = block_device::UringBlockDevice::new(
        PathBuf::from(&path),
        options.queue_size,
        false,
        true,
        options.write_through,
    )
    .map_err(|e| {
        error!("Failed to create block device at {path}: {e:?}");
        e
    })?;

    if let Some((key1, key2)) = &options.encryption_key {
        block_device =
            block_device::CryptBlockDevice::new(block_device, key1.clone(), key2.clone(), kek)?;
    }

    Ok(block_device)
}

pub fn init_metadata(
    config: &Options,
    kek: KeyEncryptionCipher,
    stripe_sector_count_shift: u8,
) -> std::result::Result<(), Box<dyn std::error::Error>> {
    let metadata_path =
        config
            .metadata_path
            .as_ref()
            .ok_or_else(|| VhostUserBlockError::InvalidParameter {
                description: "metadata_path is none".to_string(),
            })?;
    let base_bdev = build_block_device(&config.path, config, kek.clone())?;
    let stripe_sector_count = 1u64 << stripe_sector_count_shift;
    let base_stripe_count = base_bdev.sector_count().div_ceil(stripe_sector_count) as usize;

    let image_stripe_count = if let Some(ref image_path) = config.image_path {
        let readonly = true;
        let image_bdev = UringBlockDevice::new(
            PathBuf::from(image_path),
            64,
            readonly,
            true,
            config.write_through,
        )?;
        image_bdev.sector_count().div_ceil(stripe_sector_count) as usize
    } else {
        0
    };

    let metadata_bdev = build_block_device(metadata_path, config, kek.clone())?;
    let mut ch = metadata_bdev.create_channel()?;
    let metadata = UbiMetadata::new(
        stripe_sector_count_shift,
        base_stripe_count,
        image_stripe_count,
    );
    init_metadata_file(&metadata, &mut ch)?;
    Ok(())
}
