use std::{
    cmp,
    path::{Path, PathBuf},
    sync::{
        mpsc::{channel, Receiver, Sender},
        Arc,
    },
};

use log::{error, info};
use nix::sys::statfs::statfs;
use vhost_user_backend::VhostUserDaemon;
use vm_memory::GuestMemoryAtomic;

use super::{backend::UbiBlkBackend, KeyEncryptionCipher, Options};
use crate::{
    block_device::{
        self, init_metadata as init_metadata_file, load_metadata, BgWorker, BgWorkerRequest,
        BlockDevice, SharedMetadataState, UbiMetadata, UringBlockDevice,
    },
    utils::aligned_buffer::BUFFER_ALIGNMENT,
    Result, VhostUserBlockError,
};

type GuestMemoryMmap = vm_memory::GuestMemoryMmap<vhost_user_backend::bitmap::BitmapMmapRegion>;
type SourceDevices = (Box<dyn BlockDevice>, Option<Box<dyn BlockDevice>>);

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
        Self::validate_metadata_requirements(options)?;

        let base_device = build_block_device(&options.path, options, kek.clone())?;
        let alignment = Self::determine_alignment(&options.path)?;

        let BgWorkerSetup {
            block_device,
            config,
            channel,
        } = Self::build_devices(base_device, options, kek, alignment)?;

        Ok(BackendEnv {
            bdev: block_device,
            bgworker_config: config,
            bgworker_ch: channel,
            bgworker_thread: None,
            alignment,
            options: options.clone(),
        })
    }

    fn validate_metadata_requirements(options: &Options) -> Result<()> {
        if (options.image_path.is_some() || options.remote_image_address.is_some())
            && options.metadata_path.is_none()
        {
            return Err(VhostUserBlockError::InvalidParameter {
                description: "metadata_path is required when image_path is provided".to_string(),
            });
        }

        Ok(())
    }

    fn determine_alignment(path: &str) -> Result<usize> {
        let stat = statfs(Path::new(path)).map_err(|e| VhostUserBlockError::InvalidParameter {
            description: format!("Failed to statfs {path}: {e}"),
        })?;

        Ok(cmp::max(BUFFER_ALIGNMENT, stat.block_size() as usize))
    }

    fn build_devices(
        base_device: Box<dyn BlockDevice>,
        options: &Options,
        kek: KeyEncryptionCipher,
        alignment: usize,
    ) -> Result<BgWorkerSetup> {
        if let Some(metadata_path) = options.metadata_path.as_ref() {
            Self::build_lazy_device(base_device, options, kek, alignment, metadata_path)
        } else {
            Ok(BgWorkerSetup {
                block_device: base_device,
                config: None,
                channel: None,
            })
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn build_lazy_device(
        base_device: Box<dyn BlockDevice>,
        options: &Options,
        kek: KeyEncryptionCipher,
        alignment: usize,
        metadata_path: &str,
    ) -> Result<BgWorkerSetup> {
        let metadata_dev = build_block_device(metadata_path, options, kek.clone())?;
        let mut metadata_channel = metadata_dev.create_channel()?;
        let metadata = load_metadata(&mut metadata_channel, metadata_dev.sector_count())?;
        let shared_state = SharedMetadataState::new(&metadata);

        let (source_clone, maybe_image_bdev) = Self::create_source_devices(options)?;
        let target_clone = base_device.clone();
        let (bgworker_tx, bgworker_rx) = channel();

        let block_device = block_device::LazyBlockDevice::new(
            base_device,
            maybe_image_bdev,
            bgworker_tx.clone(),
            shared_state.clone(),
            options.track_written,
        )?;

        let config = BgWorkerConfig {
            source_dev: source_clone,
            target_dev: target_clone,
            metadata_dev,
            alignment,
            status_path: options.status_path.as_ref().map(PathBuf::from),
            autofetch: options.autofetch,
            shared_state,
            receiver: bgworker_rx,
        };

        Ok(BgWorkerSetup {
            block_device,
            config: Some(config),
            channel: Some(bgworker_tx),
        })
    }

    fn create_source_devices(options: &Options) -> Result<SourceDevices> {
        let source: Box<dyn BlockDevice> = if let Some(ref address) = options.remote_image_address {
            block_device::RemoteBlockDevice::new(address.clone())?
        } else if let Some(ref path) = options.image_path {
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

        let clone_for_worker = source.clone();
        let maybe_image = if options.copy_on_read {
            None
        } else {
            Some(source)
        };

        Ok((clone_for_worker, maybe_image))
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

        let mut daemon = VhostUserDaemon::new("ubiblk-backend".to_string(), backend.clone(), mem)
            .map_err(|e| {
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

        for thread in backend.threads().iter() {
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

struct BgWorkerSetup {
    block_device: Box<dyn BlockDevice>,
    config: Option<BgWorkerConfig>,
    channel: Option<Sender<BgWorkerRequest>>,
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

fn build_block_device(
    path: &str,
    options: &Options,
    kek: KeyEncryptionCipher,
) -> Result<Box<dyn BlockDevice>> {
    let mut block_device: Box<dyn BlockDevice> = block_device::UringBlockDevice::new(
        PathBuf::from(path),
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
