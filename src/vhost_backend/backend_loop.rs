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

use super::{backend::UbiBlkBackend, rpc};
use crate::{
    block_device::{
        self, BgWorker, BgWorkerRequest, BlockDevice, SharedMetadataState, StatusReporter,
        UbiMetadata, UringBlockDevice,
    },
    config::{DeviceConfig, IoEngine},
    stripe_source::StripeSourceBuilder,
    utils::aligned_buffer::BUFFER_ALIGNMENT,
    vhost_backend::io_tracking::IoTracker,
    Result, UbiblkError,
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
    bgworker_ch: Option<Sender<BgWorkerRequest>>,
    bgworker_thread: Option<std::thread::JoinHandle<()>>,
    alignment: usize,
    options: DeviceConfig,
    status_reporter: Option<StatusReporter>,
    io_trackers: Vec<IoTracker>,
}

impl BackendEnv {
    fn build(options: &DeviceConfig) -> Result<Self> {
        let base_device = build_block_device(&options.path, options, false)?;
        let alignment = Self::determine_alignment(&options.path)?;

        let BgWorkerSetup {
            block_device,
            config,
            channel,
            status_reporter,
        } = Self::build_devices(base_device, options, alignment)?;

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

    fn determine_alignment(path: &str) -> Result<usize> {
        let stat = statfs(Path::new(path)).map_err(|e| UbiblkError::InvalidParameter {
            description: format!("Failed to statfs {path}: {e}"),
        })?;

        Ok(cmp::max(BUFFER_ALIGNMENT, stat.block_size() as usize))
    }

    fn build_devices(
        base_device: Box<dyn BlockDevice>,
        options: &DeviceConfig,
        alignment: usize,
    ) -> Result<BgWorkerSetup> {
        if let Some(metadata_path) = options.metadata_path.as_ref() {
            Self::build_lazy_device(base_device, options, alignment, metadata_path)
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
        options: &DeviceConfig,
        alignment: usize,
        metadata_path: &str,
    ) -> Result<BgWorkerSetup> {
        let metadata_dev = build_block_device(metadata_path, options, false)?;
        let metadata = UbiMetadata::load_from_bdev(metadata_dev.as_ref())?;
        let shared_state = SharedMetadataState::new(&metadata);

        let maybe_image_bdev = if options.copy_on_read {
            None
        } else {
            Some(build_source_device(options)?)
        };

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
    let metadata_path =
        config
            .metadata_path
            .as_ref()
            .ok_or_else(|| UbiblkError::InvalidParameter {
                description: "metadata_path is none".to_string(),
            })?;

    let base_bdev = build_block_device(&config.path, config, false)?;
    let stripe_sector_count = 1u64 << stripe_sector_count_shift;
    let base_stripe_count = base_bdev.stripe_count(stripe_sector_count);

    let metadata = if !config.has_stripe_source() {
        // No image source
        UbiMetadata::new(stripe_sector_count_shift, base_stripe_count, 0)
    } else {
        let stripe_source =
            StripeSourceBuilder::new(config.clone(), stripe_sector_count).build()?;
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

pub fn build_source_device(options: &DeviceConfig) -> Result<Box<dyn BlockDevice>> {
    let source: Box<dyn BlockDevice> = if let Some(path) = options.raw_image_path() {
        let readonly = true;
        create_io_engine_device(
            options.io_engine.clone(),
            path,
            64,
            readonly,
            true,
            options.write_through,
        )?
    } else {
        block_device::NullBlockDevice::new()
    };
    Ok(source)
}

pub fn build_block_device(
    path: &str,
    options: &DeviceConfig,
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

        let options = DeviceConfig {
            path: disk_file.path().to_str().unwrap().to_string(),
            socket: "/tmp/ubiblk-test.sock".to_string(),
            queue_size: 128,
            ..Default::default()
        };

        let result = BackendEnv::build(&options);
        assert!(result.is_ok());
    }

    #[test]
    fn build_backend_env_with_invalid_path() {
        let options = DeviceConfig {
            path: "/non/existent/path".to_string(),
            socket: "/tmp/ubiblk-test.sock".to_string(),
            queue_size: 128,
            ..Default::default()
        };

        let result = BackendEnv::build(&options);
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

        let options = DeviceConfig {
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

        init_metadata(&options, 11).unwrap();

        let result = BackendEnv::build(&options);
        assert!(result.is_ok());
    }
}
