use std::{
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

use super::{
    backend::{build_block_device, GuestMemoryMmap, UbiBlkBackend},
    KeyEncryptionCipher, Options,
};
use crate::{
    block_device::{
        self, load_metadata, BgWorker, BgWorkerRequest, BlockDevice, SharedMetadataState,
        UringBlockDevice,
    },
    utils::aligned_buffer::BUFFER_ALIGNMENT,
    Result, VhostUserBlockError,
};

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

        for thread in backend.worker_threads().iter() {
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
