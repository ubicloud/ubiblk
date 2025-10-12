use std::{
    ops::Deref,
    path::PathBuf,
    sync::{
        mpsc::{channel, Receiver, Sender},
        Arc, Mutex,
    },
    time::Instant,
};

use crate::{
    block_device::{
        self, BgWorker, BgWorkerRequest, BlockDevice, SharedMetadataState, UringBlockDevice,
    },
    vhost_backend::SECTOR_SIZE,
};
use crate::{
    utils::block::{features_to_str, VirtioBlockConfig},
    VhostUserBlockError,
};

use super::{backend_thread::UbiBlkBackendThread, KeyEncryptionCipher, Options};
use crate::block_device::{init_metadata as init_metadata_file, load_metadata, UbiMetadata};
use crate::utils::aligned_buffer::BUFFER_ALIGNMENT;
use crate::Result;
use log::{debug, error, info};
use nix::sys::statfs::statfs;
use std::path::Path;
use vhost::vhost_user::message::*;
use vhost_user_backend::{
    bitmap::BitmapMmapRegion, VhostUserBackend, VhostUserDaemon, VringRwLock, VringT,
};
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

fn build_block_device(
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

struct BgWorkerConfig {
    source_dev: Box<dyn BlockDevice>,
    target_dev: Box<dyn BlockDevice>,
    metadata_dev: Box<dyn BlockDevice>,
    alignment: usize,
    status_path: Option<PathBuf>,
    autofetch: bool,
    shared_state: SharedMetadataState,
    receiver: Receiver<BgWorkerRequest>,
}

struct BackendEnv {
    bdev: Box<dyn BlockDevice>,
    bgworker_config: Option<BgWorkerConfig>,
    bgworker_ch: Option<Sender<BgWorkerRequest>>,
    bgworker_thread: Option<std::thread::JoinHandle<()>>,
    alignment: usize,
    options: Options,
}

impl BackendEnv {
    fn build(options: &Options, kek: KeyEncryptionCipher) -> Result<Self> {
        if options.image_path.is_some() && options.metadata_path.is_none() {
            return Err(VhostUserBlockError::InvalidParameter {
                description: "metadata_path is required when image_path is provided".to_string(),
            });
        }
        let base_block_device = build_block_device(&options.path, options, kek.clone())?;

        let stat = statfs(Path::new(&options.path)).map_err(|e| {
            VhostUserBlockError::InvalidParameter {
                description: format!("Failed to statfs {}: {e}", &options.path),
            }
        })?;

        let alignment = std::cmp::max(BUFFER_ALIGNMENT, stat.block_size() as usize);

        let (block_device, bgworker_config, bgworker_ch) =
            if let Some(metadata_path) = options.metadata_path.as_ref() {
                let metadata_dev = build_block_device(metadata_path, options, kek.clone())?;
                let mut metadata_channel = metadata_dev.create_channel()?;
                let metadata = load_metadata(&mut metadata_channel, metadata_dev.sector_count())?;
                let shared_state = SharedMetadataState::new(&metadata);

                let source_bdev: Box<dyn BlockDevice> = if let Some(ref path) = options.image_path {
                    let readonly = true;
                    UringBlockDevice::new(
                        PathBuf::from(path),
                        64,
                        readonly,
                        true,
                        options.write_through,
                    )?
                } else {
                    block_device::NullBlockDevice::new()
                };
                let source_clone = source_bdev.clone();
                let maybe_image_bdev: Option<Box<dyn BlockDevice>> = if options.copy_on_read {
                    None
                } else {
                    Some(source_bdev)
                };
                let target_clone = base_block_device.clone();
                let (bgworker_tx, bgworker_rx) = channel();
                let block_device: Box<dyn BlockDevice> = block_device::LazyBlockDevice::new(
                    base_block_device,
                    maybe_image_bdev,
                    bgworker_tx.clone(),
                    shared_state.clone(),
                    options.track_written,
                )?;
                let bgworker_config = BgWorkerConfig {
                    source_dev: source_clone,
                    target_dev: target_clone,
                    metadata_dev,
                    alignment,
                    status_path: options.status_path.as_ref().map(PathBuf::from),
                    autofetch: options.autofetch,
                    shared_state,
                    receiver: bgworker_rx,
                };
                (block_device, Some(bgworker_config), Some(bgworker_tx))
            } else {
                (base_block_device, None, None)
            };

        Ok(BackendEnv {
            bdev: block_device,
            bgworker_config,
            bgworker_ch,
            alignment,
            options: options.clone(),
            bgworker_thread: None,
        })
    }

    fn run_bgworker_thread(&mut self) -> Result<()> {
        if let Some(config) = self.bgworker_config.take() {
            self.bgworker_thread = Some(
                std::thread::Builder::new()
                    .name("bgworker".to_string())
                    .spawn(move || {
                        let BgWorkerConfig {
                            source_dev,
                            target_dev,
                            metadata_dev,
                            alignment,
                            status_path,
                            autofetch,
                            shared_state,
                            receiver,
                        } = config;

                        match BgWorker::new(
                            &*source_dev,
                            &*target_dev,
                            &*metadata_dev,
                            alignment,
                            status_path,
                            autofetch,
                            shared_state,
                            receiver,
                        ) {
                            Ok(mut worker) => worker.run(),
                            Err(e) => error!("Failed to construct bgworker: {e}"),
                        }
                    })
                    .map_err(|e| {
                        error!("Failed to spawn bgworker thread: {e}");
                        VhostUserBlockError::Other {
                            description: format!("Failed to spawn bgworker thread: {e}"),
                        }
                    })?,
            );
        }

        Ok(())
    }

    #[allow(dead_code)]
    fn stop_bgworker_thread(&mut self) {
        if let Some(ch) = self.bgworker_ch.take() {
            if let Err(e) = ch.send(BgWorkerRequest::Shutdown) {
                error!("Failed to send shutdown request to bgworker: {e}");
            }
        }

        if let Some(handle) = self.bgworker_thread.take() {
            if let Err(e) = handle.join() {
                error!("Failed to join bgworker thread: {e:?}");
            }
        }
    }

    fn serve(&self) -> Result<()> {
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());

        info!("Creating backend ...");

        let backend = Arc::new(UbiBlkBackend::new(
            &self.options,
            mem.clone(),
            self.bdev.clone(),
            self.alignment,
        )?);

        info!("Backend is created!");

        let name = "ubiblk-backend";
        let mut daemon =
            VhostUserDaemon::new(name.to_string(), backend.clone(), mem).map_err(|e| {
                error!("Failed to create VhostUserDaemon: {e:?}");
                VhostUserBlockError::Other {
                    description: e.to_string(),
                }
            })?;

        info!("Daemon is created!");

        if let Err(e) = daemon.serve(&self.options.socket) {
            return Err(VhostUserBlockError::Other {
                description: e.to_string(),
            });
        }

        info!("Finished serving socket!");

        for thread in backend.threads.iter() {
            match thread.lock() {
                Ok(t) => {
                    if let Err(e) = t.kill_evt.write(1) {
                        error!("Error shutting down worker thread: {e:?}");
                    }
                }
                Err(_) => error!("Failed to lock worker thread for shutdown"),
            }
        }

        info!("Finished shutting down worker threads!");

        Ok(())
    }
}

pub fn block_backend_loop(config: &Options, kek: KeyEncryptionCipher) -> Result<()> {
    info!("Starting vhost-user-blk backend with options: {config:?}");

    info!("Process ID: {}", std::process::id());

    let mut backend_env = BackendEnv::build(config, kek.clone())?;
    backend_env.run_bgworker_thread()?;

    loop {
        backend_env.serve()?;
    }
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
