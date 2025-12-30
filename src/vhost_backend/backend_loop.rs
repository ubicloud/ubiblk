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

use super::{backend::UbiBlkBackend, rpc, IoEngine, Options};
use crate::{
    block_device::{
        self, init_metadata as init_metadata_file, load_metadata, BgWorker, BgWorkerRequest,
        BlockDevice, SharedMetadataState, StatusReporter, UbiMetadata, UringBlockDevice,
    },
    crypt::KeyEncryptionCipher,
    stripe_source::StripeSourceBuilder,
    utils::aligned_buffer::BUFFER_ALIGNMENT,
    vhost_backend::io_tracking::IoTracker,
    Result, UbiblkError,
};

type GuestMemoryMmap = vm_memory::GuestMemoryMmap<vhost_user_backend::bitmap::BitmapMmapRegion>;
type SourceDevices = (Box<dyn BlockDevice>, Option<Box<dyn BlockDevice>>);

struct BgWorkerConfig {
    target_dev: Box<dyn BlockDevice>,
    stripe_source_builder: Box<StripeSourceBuilder>,
    metadata_dev: Box<dyn BlockDevice>,
    alignment: usize,
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
    status_reporter: Option<StatusReporter>,
    io_trackers: Vec<IoTracker>,
}

impl BackendEnv {
    fn build(options: &Options, kek: KeyEncryptionCipher) -> Result<Self> {
        Self::validate_metadata_requirements(options)?;

        let base_device = build_block_device(&options.path, options, kek.clone(), false)?;
        let alignment = Self::determine_alignment(&options.path)?;

        let BgWorkerSetup {
            block_device,
            config,
            channel,
            status_reporter,
        } = Self::build_devices(base_device, options, kek, alignment)?;

        let io_trackers = (0..options.num_queues)
            .map(|_| IoTracker::new(options.queue_size))
            .collect();

        Ok(BackendEnv {
            bdev: block_device,
            bgworker_config: config,
            bgworker_ch: channel,
            bgworker_thread: None,
            alignment,
            options: options.clone(),
            status_reporter,
            io_trackers,
        })
    }

    fn validate_metadata_requirements(options: &Options) -> Result<()> {
        if options.image_path.is_some() && options.metadata_path.is_none() {
            return Err(UbiblkError::InvalidParameter {
                description: "metadata_path is required when image_path is provided".to_string(),
            });
        }

        Ok(())
    }

    fn determine_alignment(path: &str) -> Result<usize> {
        let stat = statfs(Path::new(path)).map_err(|e| UbiblkError::InvalidParameter {
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
                status_reporter: None,
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
        let metadata_dev = build_block_device(metadata_path, options, kek.clone(), false)?;
        let mut metadata_channel = metadata_dev.create_channel()?;
        let metadata = load_metadata(&mut metadata_channel, metadata_dev.sector_count())?;
        let shared_state = SharedMetadataState::new(&metadata);

        let (_, maybe_image_bdev) = Self::create_source_devices(options)?;
        let target_clone = base_device.clone();
        let target_sector_count = target_clone.sector_count();
        let (bgworker_tx, bgworker_rx) = channel();

        let block_device = block_device::LazyBlockDevice::new(
            base_device,
            maybe_image_bdev,
            bgworker_tx.clone(),
            shared_state.clone(),
            options.track_written,
        )?;

        let stripe_source_builder = Box::new(StripeSourceBuilder::new(
            options.clone(),
            kek,
            shared_state.stripe_sector_count(),
        ));

        let config = BgWorkerConfig {
            target_dev: target_clone,
            stripe_source_builder,
            metadata_dev,
            alignment,
            autofetch: options.autofetch,
            shared_state: shared_state.clone(),
            receiver: bgworker_rx,
        };

        let status_reporter = StatusReporter::new(shared_state.clone(), target_sector_count);

        Ok(BgWorkerSetup {
            block_device,
            config: Some(config),
            channel: Some(bgworker_tx),
            status_reporter: Some(status_reporter),
        })
    }

    fn create_source_devices(options: &Options) -> Result<SourceDevices> {
        let source: Box<dyn BlockDevice> = if let Some(ref path) = options.image_path {
            let readonly = true;
            create_io_engine_device(
                options.io_engine.clone(),
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
                            target_dev,
                            stripe_source_builder,
                            metadata_dev,
                            alignment,
                            autofetch,
                            shared_state,
                            receiver,
                        } = config;

                        let stripe_source = match stripe_source_builder.build() {
                            Ok(source) => source,
                            Err(e) => {
                                error!("Failed to build stripe source: {e}");
                                return;
                            }
                        };

                        match BgWorker::new(
                            stripe_source,
                            &*target_dev,
                            &*metadata_dev,
                            alignment,
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
                        UbiblkError::ThreadCreation { source: e }
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

    fn status_reporter(&self) -> Option<StatusReporter> {
        self.status_reporter.clone()
    }

    fn serve(&self) -> Result<()> {
        let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());

        info!("Creating backend ...");

        let backend = Arc::new(UbiBlkBackend::new(
            &self.options,
            mem.clone(),
            self.bdev.clone(),
            self.alignment,
            self.io_trackers.clone(),
        )?);

        info!("Backend is created!");

        let mut daemon = VhostUserDaemon::new("ubiblk-backend".to_string(), backend.clone(), mem)
            .map_err(|e| UbiblkError::VhostUserBackendError { reason: e })?;

        info!("Daemon is created!");

        daemon
            .serve(&self.options.socket)
            .map_err(|e| UbiblkError::VhostUserBackendError { reason: e })?;

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
    status_reporter: Option<StatusReporter>,
}

pub fn block_backend_loop(config: &Options, kek: KeyEncryptionCipher) -> Result<()> {
    info!("Starting vhost-user-blk backend with options: {config:?}");
    info!("Process ID: {}", std::process::id());

    let mut backend_env = BackendEnv::build(config, kek.clone())?;
    backend_env.run_bgworker_thread()?;

    let _rpc_handle = if let Some(path) = config.rpc_socket_path.as_ref() {
        let status_reporter = backend_env.status_reporter();
        let io_trackers = backend_env.io_trackers.clone();
        Some(rpc::start_rpc_server(path, status_reporter, io_trackers)?)
    } else {
        None
    };

    loop {
        backend_env.serve()?;
    }

    // TODO: Graceful shutdown handling
}

pub fn init_metadata(
    config: &Options,
    kek: KeyEncryptionCipher,
    stripe_sector_count_shift: u8,
) -> Result<()> {
    let metadata_path =
        config
            .metadata_path
            .as_ref()
            .ok_or_else(|| UbiblkError::InvalidParameter {
                description: "metadata_path is none".to_string(),
            })?;

    let base_bdev = build_block_device(&config.path, config, kek.clone(), false)?;
    let stripe_sector_count = 1u64 << stripe_sector_count_shift;
    let base_stripe_count = base_bdev.sector_count().div_ceil(stripe_sector_count) as usize;

    let metadata = if let Some(ref remote_image) = config.remote_image {
        // For remote images, connect to server and get its metadata
        let psk =
            crate::stripe_server::PskCredentials::from_options(config, &kek).map_err(|e| {
                UbiblkError::InvalidParameter {
                    description: format!(
                        "Failed to create PSK credentials for remote image {}: {}",
                        remote_image, e
                    ),
                }
            })?;
        let client = crate::stripe_server::connect_to_stripe_server(remote_image, psk.as_ref())
            .map_err(|e| UbiblkError::InvalidParameter {
                description: format!(
                    "Failed to connect to remote stripe server at {} during metadata initialization: {}",
                    remote_image, e
                ),
            })?;
        let remote_metadata =
            client
                .metadata
                .as_ref()
                .ok_or_else(|| UbiblkError::MetadataError {
                    description: format!(
                        "Failed to fetch metadata from remote server at {}",
                        remote_image
                    ),
                })?;

        // Verify stripe sizes match
        if remote_metadata.stripe_sector_count_shift != stripe_sector_count_shift {
            return Err(UbiblkError::InvalidParameter {
                description: format!(
                    "Remote stripe sector count shift ({}) does not match local ({})",
                    remote_metadata.stripe_sector_count_shift, stripe_sector_count_shift
                ),
            });
        }

        UbiMetadata::new_from_remote(
            stripe_sector_count_shift,
            base_stripe_count,
            remote_metadata,
        )
    } else if let Some(ref image_path) = config.image_path {
        // For local images, calculate stripe count from file size
        let readonly = true;
        let image_bdev: Box<dyn BlockDevice> = create_io_engine_device(
            config.io_engine.clone(),
            PathBuf::from(image_path),
            64,
            readonly,
            true,
            config.write_through,
        )?;
        let image_stripe_count = image_bdev.sector_count().div_ceil(stripe_sector_count) as usize;
        UbiMetadata::new(
            stripe_sector_count_shift,
            base_stripe_count,
            image_stripe_count,
        )
    } else {
        // No image source
        UbiMetadata::new(stripe_sector_count_shift, base_stripe_count, 0)
    };

    let metadata_bdev = build_block_device(metadata_path, config, kek.clone(), false)?;
    let mut ch = metadata_bdev.create_channel()?;
    init_metadata_file(&metadata, &mut ch, metadata_bdev.sector_count())?;
    Ok(())
}

fn create_io_engine_device(
    engine: IoEngine,
    path: PathBuf,
    queue_size: usize,
    readonly: bool,
    direct_io: bool,
    write_through: bool,
) -> Result<Box<dyn BlockDevice>> {
    match engine {
        IoEngine::IoUring => {
            let dev = UringBlockDevice::new(
                path.to_path_buf(),
                queue_size,
                readonly,
                direct_io,
                write_through,
            )?;
            Ok(dev as Box<dyn BlockDevice>)
        }
        IoEngine::Sync => {
            let dev = block_device::SyncBlockDevice::new(
                path.to_path_buf(),
                readonly,
                direct_io,
                write_through,
            )?;
            Ok(dev as Box<dyn BlockDevice>)
        }
    }
}

pub fn build_block_device(
    path: &str,
    options: &Options,
    kek: KeyEncryptionCipher,
    readonly: bool,
) -> Result<Box<dyn BlockDevice>> {
    let mut block_device: Box<dyn BlockDevice> = create_io_engine_device(
        options.io_engine.clone(),
        PathBuf::from(path),
        options.queue_size,
        readonly,
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
