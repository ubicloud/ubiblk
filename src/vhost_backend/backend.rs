use std::{
    ops::Deref,
    path::PathBuf,
    sync::{Arc, Mutex},
    time::Instant,
};

use crate::utils::block::{print_features, VirtioBlockConfig};
use crate::{
    block_device::{self, BlockDevice, StripeFetcher, SyncBlockDevice},
    vhost_backend::SECTOR_SIZE,
};

use super::backend_thread::UbiBlkBackendThread;
use crate::{Error, Result};
use log::{debug, error, info};
use serde::{Deserialize, Serialize};
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

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Options {
    pub path: String,
    pub image_path: Option<String>,
    pub socket: String,
    pub num_queues: usize,
    pub queue_size: usize,
    pub seg_size_max: u32,
    pub seg_count_max: u32,
    pub poll_queue_timeout_us: u128,
    pub encryption_key: Option<(String, String)>,
}

struct UbiBlkBackend {
    threads: Vec<Mutex<UbiBlkBackendThread>>,
    config: VirtioBlockConfig,
    queues_per_thread: Vec<u64>,
    mem: GuestMemoryAtomic<GuestMemoryMmap>,
    options: Options,
}

impl<'a> UbiBlkBackend {
    fn new(
        options: &Options,
        mem: GuestMemoryAtomic<GuestMemoryMmap>,
        block_device: Box<dyn BlockDevice>,
    ) -> Result<Self> {
        let nsectors = block_device.sector_count();
        let virtio_config = VirtioBlockConfig {
            capacity: nsectors,             /* The capacity (in SECTOR_SIZE-byte sectors). */
            blk_size: SECTOR_SIZE as u32,   /* block size of device (if VIRTIO_BLK_F_BLK_SIZE) */
            size_max: options.seg_size_max, /* The maximum segment size (if VIRTIO_BLK_F_SIZE_MAX) */
            seg_max: options.seg_count_max, /* The maximum number of segments (if VIRTIO_BLK_F_SEG_MAX) */
            min_io_size: 1, /* minimum I/O size without performance penalty in logical blocks. */
            opt_io_size: 1, /* optimal sustained I/O size in logical blocks. */
            num_queues: options.num_queues as u16,
            writeback: 1, /* writeback mode (if VIRTIO_BLK_F_CONFIG_WCE) */
            ..Default::default()
        };

        info!("virtio_config: {:?}", virtio_config);

        let mut queues_per_thread = Vec::new();
        let mut threads: Vec<Mutex<UbiBlkBackendThread>> = Vec::new();
        for i in 0..options.num_queues {
            let io_channel = block_device.create_channel().map_err(|e| {
                error!("Failed to create channel: {:?}", e);
                Error::IoChannelCreation
            })?;
            let thread: Mutex<UbiBlkBackendThread> =
                Mutex::new(UbiBlkBackendThread::new(mem.clone(), io_channel, options)?);
            threads.push(thread);
            queues_per_thread.push(0b1 << i);
        }

        debug!("queues_per_thread: {:?}", queues_per_thread);

        Ok(UbiBlkBackend {
            threads,
            config: virtio_config,
            queues_per_thread,
            mem,
            options: options.clone(),
        })
    }
}

impl<'a> VhostUserBackend for UbiBlkBackend {
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

        print!("avail_features: ");
        print_features(avail_features);
        avail_features
    }

    fn acked_features(&self, features: u64) {
        info!("acked_features: 0x{:x}", features);
        print_features(features);
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
        info!("set_event_idx: {}", enabled);
        for thread in self.threads.iter() {
            thread.lock().unwrap().event_idx = enabled;
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
            return Err(std::io::Error::new(
                std::io::ErrorKind::Other,
                format!("Invalid event set: {:?}", evset),
            ));
        }

        let mut thread = self.threads[thread_id].lock().unwrap();
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
                            .unwrap();
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
            _ => Err(std::io::Error::new(
                std::io::ErrorKind::Other,
                format!("Invalid device event: {}", device_event),
            )),
        }
    }

    fn get_config(&self, _offset: u32, _size: u32) -> Vec<u8> {
        self.config.as_slice().to_vec()
    }

    fn exit_event(&self, thread_index: usize) -> Option<EventFd> {
        Some(
            self.threads[thread_index]
                .lock()
                .unwrap()
                .kill_evt
                .try_clone()
                .unwrap(),
        )
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

fn build_block_device(options: &Options) -> Result<Box<dyn BlockDevice>> {
    let mut block_device: Box<dyn BlockDevice> =
        block_device::UringBlockDevice::new(PathBuf::from(&options.path), options.queue_size)
            .map_err(|e| {
                error!("Failed to create block device: {:?}", e);
                Box::new(e)
            })
            .unwrap();

    if let Some((key1, key2)) = &options.encryption_key {
        block_device = block_device::CryptBlockDevice::new(block_device, &key1, &key2)?;
    }

    Ok(block_device)
}

fn start_block_backend(options: &Options) -> std::result::Result<(), Box<dyn std::error::Error>> {
    let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());

    let base_block_device = build_block_device(options)?;

    let stripe_fetcher_killfd = EventFd::new(libc::EFD_NONBLOCK)?;
    let maybe_stripe_fetcher = match options.image_path {
        Some(ref path) => {
            let image_bdev = SyncBlockDevice::new(PathBuf::from(path))?;
            let stripe_fetcher = StripeFetcher::new(
                &*image_bdev,
                &*base_block_device,
                stripe_fetcher_killfd.try_clone()?,
            )?;
            Some(Arc::new(Mutex::new(stripe_fetcher)))
        }
        None => None,
    };

    let block_device = match maybe_stripe_fetcher.as_ref() {
        Some(stripe_fetcher) => {
            block_device::LazyBlockDevice::new(base_block_device, stripe_fetcher.clone())?
        }
        None => base_block_device,
    };

    let backend = Arc::new(
        UbiBlkBackend::new(&options, mem.clone(), block_device).map_err(|e| {
            error!("Failed to create UbiBlkBackend: {:?}", e);
            Box::new(e)
        })?,
    );

    info!("Backend is created!");

    let stripe_featcher_thread = match maybe_stripe_fetcher.as_ref() {
        Some(stripe_fetcher) => {
            let stripe_fetcher_clone = stripe_fetcher.clone();
            let handle = std::thread::Builder::new()
                .name("stripe-fetcher".to_string())
                .spawn(move || {
                    stripe_fetcher_clone.lock().unwrap().run();
                })?;
            Some(handle)
        }
        None => None,
    };

    let name = "ubiblk-backend";
    let mut daemon = VhostUserDaemon::new(name.to_string(), backend.clone(), mem).map_err(|e| {
        Box::new(std::io::Error::new(
            std::io::ErrorKind::Other,
            format!("VhostUserDaemon::new error: {:?}", e),
        ))
    })?;

    info!("Daemon is created!");

    if let Err(e) = daemon.serve(&options.socket) {
        return Err(Box::new(std::io::Error::new(
            std::io::ErrorKind::Other,
            format!("VhostUserDaemon::wait error: {:?}", e),
        )));
    };

    info!("Finished serving socket!");

    for thread in backend.threads.iter() {
        if let Err(e) = thread.lock().unwrap().kill_evt.write(1) {
            error!("Error shutting down worker thread: {:?}", e)
        }
    }

    info!("Finished shutting down worker threads!");

    if let Some(handle) = stripe_featcher_thread {
        info!("Shutting down stripe fetcher thread ...");
        if let Err(e) = stripe_fetcher_killfd.write(1) {
            error!("Error shutting down stripe fetcher thread: {:?}", e);
        }
        info!("Waiting for stripe fetcher thread to join ...");
        handle.join().unwrap();
        info!("Stripe fetcher thread joined");
    } else {
        info!("No stripe fetcher thread to join");
    }

    info!("Daemon is finished!");

    Ok(())
}

pub fn block_backend_loop(config: &Options) {
    env_logger::init();

    info!("Starting vhost-user-blk backend with options: {:?}", config);

    info!("Process ID: {}", std::process::id());

    loop {
        match start_block_backend(config) {
            Err(e) => {
                error!("An error occurred: {:?}", e);
                break;
            }
            Ok(_) => {
                info!("Disconnected from the socket, restarting ...");
                continue;
            }
        }
    }
}
