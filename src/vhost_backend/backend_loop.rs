use std::{
    cmp, fs,
    os::unix::fs::PermissionsExt,
    path::{Path, PathBuf},
    sync::{
        mpsc::{channel, Receiver, Sender},
        Arc,
    },
};

use log::{error, info};
use nix::sys::statfs::statfs;
use vhost::vhost_user::{Error as VhostUserError, Listener};
use vhost_user_backend::{Error as VhostUserBackendError, VhostUserDaemon};
use vm_memory::GuestMemoryAtomic;

use super::{backend::UbiBlkBackend, rpc};
use crate::{
    block_device::{
        self, BgWorker, BgWorkerRequest, BlockDevice, SharedMetadataState, StatusReporter,
        SyncBlockDevice, UbiMetadata, UringBlockDevice,
    },
    config::{DeviceConfig, IoEngine},
    stripe_source::StripeSourceBuilder,
    utils::{aligned_buffer::BUFFER_ALIGNMENT, umask_guard::UmaskGuard},
    vhost_backend::io_tracking::IoTracker,
    Result,
};

type GuestMemoryMmap = vm_memory::GuestMemoryMmap<vhost_user_backend::bitmap::BitmapMmapRegion>;

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
    bgworker_sender: Option<Sender<BgWorkerRequest>>,
    bgworker_thread: Option<std::thread::JoinHandle<()>>,
    alignment: usize,
    config: DeviceConfig,
    status_reporter: Option<StatusReporter>,
    io_trackers: Vec<IoTracker>,
}

impl BackendEnv {
    fn build(config: &DeviceConfig) -> Result<Self> {
        let alignment = Self::determine_alignment(&config.path)?;

        let disk_device = build_block_device(&config.path, config, false)?;
        let metadata_device = config
            .metadata_path
            .as_ref()
            .map(|path| build_block_device(path, config, false))
            .transpose()?;

        match metadata_device {
            None => Ok(BackendEnv {
                bdev: disk_device,
                bgworker_config: None,
                bgworker_sender: None,
                bgworker_thread: None,
                alignment,
                config: config.clone(),
                status_reporter: None,
                io_trackers: Self::build_io_trackers(config),
            }),
            Some(metadata_dev) => {
                Self::build_with_bgworker(disk_device, metadata_dev, config, alignment)
            }
        }
    }

    fn build_with_bgworker(
        disk_device: Box<dyn BlockDevice>,
        metadata_device: Box<dyn BlockDevice>,
        config: &DeviceConfig,
        alignment: usize,
    ) -> Result<Self> {
        let metadata = UbiMetadata::load_from_bdev(metadata_device.as_ref())?;
        let shared_state = SharedMetadataState::new(&metadata);
        let status_reporter = StatusReporter::new(shared_state.clone(), disk_device.sector_count());

        let (bgworker_sender, bgworker_receiver) = channel();

        let bdev_lazy = Self::build_bdev_lazy(
            disk_device.clone(),
            config,
            bgworker_sender.clone(),
            shared_state.clone(),
        )?;

        let stripe_source_builder = Box::new(StripeSourceBuilder::new(
            config.clone(),
            shared_state.stripe_sector_count(),
            metadata.has_fetched_all_stripes(),
        ));

        let bgworker_config = BgWorkerConfig {
            target_dev: disk_device,
            stripe_source_builder,
            metadata_dev: metadata_device,
            alignment,
            autofetch: config.autofetch,
            shared_state,
            receiver: bgworker_receiver,
        };

        Ok(BackendEnv {
            bdev: bdev_lazy,
            bgworker_config: Some(bgworker_config),
            bgworker_sender: Some(bgworker_sender),
            bgworker_thread: None,
            alignment,
            config: config.clone(),
            status_reporter: Some(status_reporter),
            io_trackers: Self::build_io_trackers(config),
        })
    }

    fn determine_alignment(path: &str) -> Result<usize> {
        let stat = statfs(Path::new(path)).map_err(|e| {
            crate::ubiblk_error!(InvalidParameter {
                description: format!("Failed to statfs {path}: {e}"),
            })
        })?;

        Ok(cmp::max(BUFFER_ALIGNMENT, stat.block_size() as usize))
    }

    fn build_bdev_lazy(
        disk_device: Box<dyn BlockDevice>,
        config: &DeviceConfig,
        bgworker_sender: Sender<BgWorkerRequest>,
        shared_state: SharedMetadataState,
    ) -> Result<Box<dyn BlockDevice>> {
        let raw_image_device = if config.copy_on_read {
            None
        } else {
            build_raw_image_device(config)?
        };

        let lazy_bdev = block_device::LazyBlockDevice::new(
            disk_device,
            raw_image_device,
            bgworker_sender,
            shared_state,
            config.track_written,
        )?;

        Ok(lazy_bdev)
    }

    fn build_io_trackers(config: &DeviceConfig) -> Vec<IoTracker> {
        (0..config.num_queues)
            .map(|_| IoTracker::new(config.queue_size))
            .collect()
    }

    fn run_bgworker_thread(&mut self) -> Result<()> {
        if let Some(config) = self.bgworker_config.take() {
            self.bgworker_thread = Some(Self::spawn_bgworker_thread(config)?);
        }

        Ok(())
    }

    fn spawn_bgworker_thread(config: BgWorkerConfig) -> Result<std::thread::JoinHandle<()>> {
        std::thread::Builder::new()
            .name("bgworker".to_string())
            .spawn(move || Self::run_bgworker(config))
            .map_err(|e| {
                error!("Failed to spawn bgworker thread: {e}");
                crate::ubiblk_error!(ThreadCreation { source: e })
            })
    }

    fn run_bgworker(config: BgWorkerConfig) {
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
    }

    #[allow(dead_code)]
    fn stop_bgworker_thread(&mut self) {
        if let Some(ch) = self.bgworker_sender.take() {
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
            &self.config,
            mem.clone(),
            self.bdev.clone(),
            self.alignment,
            self.io_trackers.clone(),
        )?);

        info!("Backend is created!");

        let mut daemon = VhostUserDaemon::new("ubiblk-backend".to_string(), backend.clone(), mem)?;

        info!("Daemon is created!");

        let listener = {
            let _um = UmaskGuard::set(0o117); // ensures 0660 max on creation
            Listener::new(&self.config.socket, true)?
        };

        // Allow only owner and group to read/write the socket
        fs::set_permissions(&self.config.socket, fs::Permissions::from_mode(0o660))?;

        daemon.start(listener)?;
        let result = daemon.wait();

        for handler in daemon.get_epoll_handlers() {
            handler.send_exit_event();
        }

        match result {
            Ok(()) => {}
            Err(VhostUserBackendError::HandleRequest(VhostUserError::Disconnected))
            | Err(VhostUserBackendError::HandleRequest(VhostUserError::PartialMessage)) => {}
            Err(e) => {
                return Err(e.into());
            }
        }

        info!("Finished serving socket!");
        Self::shutdown_worker_threads(&backend);

        Ok(())
    }

    fn shutdown_worker_threads(backend: &UbiBlkBackend) {
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
    }
}

pub fn block_backend_loop(config: &DeviceConfig) -> Result<()> {
    info!(
        "Starting vhost-user-blk backend. Process ID: {}",
        std::process::id()
    );

    let mut backend_env = BackendEnv::build(config)?;
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

pub fn init_metadata(config: &DeviceConfig, stripe_sector_count_shift: u8) -> Result<()> {
    let metadata_path = config.metadata_path.as_ref().ok_or_else(|| {
        crate::ubiblk_error!(InvalidParameter {
            description: "metadata_path is none".to_string(),
        })
    })?;

    let base_bdev = build_block_device(&config.path, config, false)?;
    let stripe_sector_count = 1u64 << stripe_sector_count_shift;
    let base_stripe_count = base_bdev.stripe_count(stripe_sector_count);

    let metadata = if !config.has_stripe_source() {
        // No image source
        UbiMetadata::new(stripe_sector_count_shift, base_stripe_count, 0)
    } else {
        let stripe_source =
            StripeSourceBuilder::new(config.clone(), stripe_sector_count, false).build()?;
        UbiMetadata::new_from_stripe_source(
            stripe_sector_count_shift,
            base_stripe_count,
            stripe_source.as_ref(),
        )
    };

    let metadata_bdev = build_block_device(metadata_path, config, false)?;
    metadata.save_to_bdev(metadata_bdev.as_ref())?;
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
        IoEngine::IoUring => Ok(UringBlockDevice::new(
            path,
            queue_size,
            readonly,
            direct_io,
            write_through,
        )?),
        IoEngine::Sync => Ok(SyncBlockDevice::new(
            path,
            readonly,
            direct_io,
            write_through,
        )?),
    }
}

pub fn build_raw_image_device(config: &DeviceConfig) -> Result<Option<Box<dyn BlockDevice>>> {
    if let Some(path) = config.raw_image_path() {
        let readonly = true;
        Ok(Some(create_io_engine_device(
            config.io_engine.clone(),
            path,
            64,
            readonly,
            true,
            config.write_through,
        )?))
    } else {
        Ok(None)
    }
}

pub fn build_block_device(
    path: &str,
    config: &DeviceConfig,
    readonly: bool,
) -> Result<Box<dyn BlockDevice>> {
    let mut block_device: Box<dyn BlockDevice> = create_io_engine_device(
        config.io_engine.clone(),
        PathBuf::from(path),
        config.queue_size,
        readonly,
        true,
        config.write_through,
    )?;

    if let Some((key1, key2)) = &config.encryption_key {
        block_device =
            block_device::CryptBlockDevice::new(block_device, key1.clone(), key2.clone())?;
    }

    Ok(block_device)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::{RawStripeSourceConfig, StripeSourceConfig};

    #[test]
    fn build_backend_env_no_metadata() {
        let disk_file = tempfile::NamedTempFile::new().unwrap();
        disk_file.as_file().set_len(10 * 1024 * 1024).unwrap();

        let config = DeviceConfig {
            path: disk_file.path().to_str().unwrap().to_string(),
            socket: "/tmp/ubiblk-test.sock".to_string(),
            queue_size: 128,
            ..Default::default()
        };

        let result = BackendEnv::build(&config);
        assert!(result.is_ok());
    }

    #[test]
    fn build_backend_env_with_invalid_path() {
        let config = DeviceConfig {
            path: "/non/existent/path".to_string(),
            socket: "/tmp/ubiblk-test.sock".to_string(),
            queue_size: 128,
            ..Default::default()
        };

        let result = BackendEnv::build(&config);
        assert!(result.is_err());
    }

    #[test]
    fn build_backend_with_base_image() {
        let disk_file = tempfile::NamedTempFile::new().unwrap();
        disk_file.as_file().set_len(10 * 1024 * 1024).unwrap();

        let image_file = tempfile::NamedTempFile::new().unwrap();
        image_file.as_file().set_len(5 * 1024 * 1024).unwrap();

        let metadata_path = tempfile::NamedTempFile::new().unwrap();
        metadata_path.as_file().set_len(1024 * 1024).unwrap();

        let config = DeviceConfig {
            path: disk_file.path().to_str().unwrap().to_string(),
            stripe_source: Some(StripeSourceConfig::Raw {
                config: RawStripeSourceConfig {
                    path: image_file.path().to_path_buf(),
                },
            }),
            metadata_path: Some(metadata_path.path().to_str().unwrap().to_string()),
            socket: "/tmp/ubiblk-test.sock".to_string(),
            queue_size: 128,
            ..Default::default()
        };

        init_metadata(&config, 11).unwrap();

        let result = BackendEnv::build(&config);
        assert!(result.is_ok());
    }
}
