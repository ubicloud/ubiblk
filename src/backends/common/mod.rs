use std::{
    cmp,
    fs::{File, OpenOptions},
    os::unix::fs::{OpenOptionsExt, PermissionsExt},
    path::{Path, PathBuf},
    sync::mpsc::{channel, Receiver, Sender},
};

use log::{error, info};
use nix::fcntl::OFlag;
use nix::sys::statfs::statfs;
use ubiblk_macros::error_context;

use crate::{
    block_device::{
        self, BgWorker, BgWorkerRequest, BlockDevice, SharedMetadataState, StatusReporter,
        SyncBlockDevice, UbiMetadata, UringBlockDevice,
    },
    config::v2,
    stripe_source::StripeSourceBuilder,
    utils::aligned_buffer::BUFFER_ALIGNMENT,
    Result, ResultExt,
};

pub mod io_tracking;
pub mod rpc;

pub const SECTOR_SIZE: usize = 512;

struct BgWorkerConfig {
    target_dev: Box<dyn BlockDevice>,
    stripe_source_builder: Box<StripeSourceBuilder>,
    metadata_dev: Box<dyn BlockDevice>,
    alignment: usize,
    autofetch: bool,
    shared_state: SharedMetadataState,
    receiver: Receiver<BgWorkerRequest>,
}

pub struct BackendEnv {
    bdev: Box<dyn BlockDevice>,
    bgworker_config: Option<BgWorkerConfig>,
    bgworker_sender: Option<Sender<BgWorkerRequest>>,
    bgworker_thread: Option<std::thread::JoinHandle<()>>,
    alignment: usize,
    config: v2::Config,
    status_reporter: Option<StatusReporter>,
    io_trackers: Vec<io_tracking::IoTracker>,
}

impl BackendEnv {
    #[error_context("Failed to build backend environment")]
    pub fn build(config: &v2::Config) -> Result<Self> {
        let alignment = Self::determine_alignment(&config.device.data_path)?;

        let disk_device = build_block_device(&config.device.data_path, config, false)
            .context("Failed to build disk device")?;
        let metadata_device = config
            .device
            .metadata_path
            .as_ref()
            .map(|path| {
                build_block_device(path, config, false).context("Failed to build metadata device")
            })
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

    #[error_context("Failed to run bgworker thread")]
    pub fn run_bgworker_thread(&mut self) -> Result<()> {
        if let Some(config) = self.bgworker_config.take() {
            let (startup_sender, startup_receiver) = channel();
            self.bgworker_thread = Some(Self::spawn_bgworker_thread(config, startup_sender)?);

            let startup_status = startup_receiver.recv().map_err(|e| {
                crate::ubiblk_error!(ChannelError {
                    reason: format!("Failed to receive bgworker startup status: {e}"),
                })
            })?;
            startup_status?;
        }

        Ok(())
    }

    pub fn stop_bgworker_thread(&mut self) {
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

    pub fn status_reporter(&self) -> Option<StatusReporter> {
        self.status_reporter.clone()
    }

    pub fn io_trackers(&self) -> &Vec<io_tracking::IoTracker> {
        &self.io_trackers
    }

    pub fn config(&self) -> &v2::Config {
        &self.config
    }

    pub fn alignment(&self) -> usize {
        self.alignment
    }

    pub fn bdev(&self) -> Box<dyn BlockDevice> {
        self.bdev.clone()
    }

    fn build_with_bgworker(
        disk_device: Box<dyn BlockDevice>,
        metadata_device: Box<dyn BlockDevice>,
        config: &v2::Config,
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
            autofetch: config
                .stripe_source
                .as_ref()
                .is_some_and(|stripe_source| stripe_source.autofetch()),
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

    #[error_context("Failed to determine filesystem alignment for path: {:?}", path)]
    fn determine_alignment(path: &Path) -> Result<usize> {
        let stat = statfs(path).map_err(|e| {
            crate::ubiblk_error!(InvalidParameter {
                description: format!("Failed to statfs {}: {e}", path.display()),
            })
        })?;

        Ok(cmp::max(BUFFER_ALIGNMENT, stat.block_size() as usize))
    }

    #[error_context("Failed to build lazy block device")]
    fn build_bdev_lazy(
        disk_device: Box<dyn BlockDevice>,
        config: &v2::Config,
        bgworker_sender: Sender<BgWorkerRequest>,
        shared_state: SharedMetadataState,
    ) -> Result<Box<dyn BlockDevice>> {
        let raw_image_device = if config
            .stripe_source
            .as_ref()
            .is_none_or(|stripe_source| stripe_source.copy_on_read())
        {
            None
        } else {
            build_raw_image_device(config)?
        };

        let lazy_bdev = block_device::LazyBlockDevice::new(
            disk_device,
            raw_image_device,
            bgworker_sender,
            shared_state,
            config.device.track_written,
        )?;

        Ok(lazy_bdev)
    }

    fn build_io_trackers(config: &v2::Config) -> Vec<io_tracking::IoTracker> {
        (0..config.tuning.num_queues)
            .map(|_| io_tracking::IoTracker::new(config.tuning.queue_size))
            .collect()
    }

    fn spawn_bgworker_thread(
        config: BgWorkerConfig,
        startup_sender: Sender<Result<()>>,
    ) -> Result<std::thread::JoinHandle<()>> {
        std::thread::Builder::new()
            .name("bgworker".to_string())
            .spawn(move || match Self::build_bgworker(config) {
                Ok(mut worker) => {
                    if let Err(send_err) = startup_sender.send(Ok(())) {
                        error!("Failed to send bgworker startup success: {send_err}");
                    } else {
                        info!("Bgworker thread started successfully");
                        worker.run();
                    }
                }
                Err(e) => {
                    let startup_result = Err(e).context("Failed to build bgworker");
                    if let Err(send_err) = startup_sender.send(startup_result) {
                        error!("Failed to send bgworker startup error to main thread: {send_err}. Original error: {:?}", send_err.0);
                    }
                }
            })
            .map_err(|e| {
                error!("Failed to spawn bgworker thread: {e}");
                crate::ubiblk_error!(ThreadCreation { source: e })
            })
    }

    fn build_bgworker(config: BgWorkerConfig) -> Result<BgWorker> {
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
                return Err(e);
            }
        };

        BgWorker::new(
            stripe_source,
            &*target_dev,
            &*metadata_dev,
            alignment,
            autofetch,
            shared_state,
            receiver,
        )
    }
}

impl Drop for BackendEnv {
    fn drop(&mut self) {
        self.stop_bgworker_thread();
    }
}

pub fn run_backend_loop<F>(
    config: &v2::Config,
    backend_name: &str,
    loop_forever: bool,
    mut serve: F,
) -> Result<()>
where
    F: FnMut(&BackendEnv) -> Result<()>,
{
    info!(
        "Starting {backend_name} backend. Process ID: {}",
        std::process::id()
    );

    let mut backend_env = BackendEnv::build(config)?;
    backend_env.run_bgworker_thread()?;

    let _rpc_handle = if let Some(path) = config.device.rpc_socket.as_ref() {
        let status_reporter = backend_env.status_reporter();
        let io_trackers = backend_env.io_trackers().clone();
        Some(rpc::start_rpc_server(path, status_reporter, io_trackers)?)
    } else {
        None
    };

    if loop_forever {
        loop {
            serve(&backend_env)?;
        }
    } else {
        serve(&backend_env)?;
    }

    Ok(())
}

pub fn init_metadata(config: &v2::Config, stripe_sector_count_shift: u8) -> Result<()> {
    let metadata_path = config.device.metadata_path.as_ref().ok_or_else(|| {
        crate::ubiblk_error!(InvalidParameter {
            description: "metadata_path is none".to_string(),
        })
    })?;

    let disk_bdev = build_block_device(&config.device.data_path, config, false)
        .context("Failed to build disk block device")?;
    let stripe_sector_count = 1u64 << stripe_sector_count_shift;
    let base_stripe_count = disk_bdev.stripe_count(stripe_sector_count);

    let metadata = if config.stripe_source.is_none() {
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

    ensure_metadata_file(metadata_path, metadata.metadata_size())?;

    let metadata_bdev = build_block_device(metadata_path, config, false)
        .context("Failed to build metadata block device")?;
    metadata.save_to_bdev(metadata_bdev.as_ref())?;
    Ok(())
}

#[error_context("Failed to ensure metadata file exists with secure permissions")]
fn ensure_metadata_file(path: &Path, minimum_size: usize) -> Result<()> {
    let mut created = false;
    let file = match OpenOptions::new()
        .read(true)
        .write(true)
        .create_new(true)
        .custom_flags(OFlag::O_NOFOLLOW.bits())
        .mode(0o600)
        .open(path)
    {
        Ok(file) => {
            created = true;
            file
        }
        Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => OpenOptions::new()
            .read(true)
            .write(true)
            .custom_flags(OFlag::O_NOFOLLOW.bits())
            .open(path)
            .context(format!("Failed to open metadata file {}", path.display()))?,
        Err(e) => return Err(crate::ubiblk_error!(IoError { source: e })),
    };

    let stat_result = file
        .metadata()
        .context(format!("Failed to stat metadata file {}", path.display()))?;
    if !stat_result.file_type().is_file() {
        return Err(crate::ubiblk_error!(InvalidParameter {
            description: format!("Metadata path {} is not a regular file", path.display()),
        }));
    }

    let mut permissions = stat_result.permissions();
    if permissions.mode() & 0o7777 != 0o600 {
        permissions.set_mode(0o600);
        file.set_permissions(permissions).context(format!(
            "Failed to set metadata file permissions on {}",
            path.display()
        ))?;
    }

    let minimum_size_u64 = minimum_size as u64;
    if stat_result.len() < minimum_size_u64 {
        file.set_len(minimum_size_u64).context(format!(
            "Failed to resize metadata file {} to {} bytes",
            path.display(),
            minimum_size
        ))?;
    }

    file.sync_all()
        .context(format!("Failed to sync metadata file {}", path.display()))?;

    if created {
        let parent = path.parent().ok_or_else(|| {
            crate::ubiblk_error!(InvalidParameter {
                description: format!("Metadata file path {} has no parent", path.display()),
            })
        })?;

        File::open(parent)
            .context(format!(
                "Failed to open metadata parent dir {}",
                parent.display()
            ))?
            .sync_all()
            .context(format!(
                "Failed to sync metadata parent dir {}",
                parent.display()
            ))?;
    }

    Ok(())
}

#[error_context("Failed to create I/O engine device")]
fn create_io_engine_device(
    engine: v2::tuning::IoEngine,
    path: PathBuf,
    queue_size: usize,
    readonly: bool,
    direct_io: bool,
    write_through: bool,
) -> Result<Box<dyn BlockDevice>> {
    match engine {
        v2::tuning::IoEngine::IoUring => Ok(UringBlockDevice::new(
            path.to_path_buf(),
            queue_size,
            readonly,
            direct_io,
            write_through,
        )?),
        v2::tuning::IoEngine::Sync => Ok(SyncBlockDevice::new(
            path.to_path_buf(),
            readonly,
            direct_io,
            write_through,
        )?),
    }
}

pub fn build_raw_image_device(config: &v2::Config) -> Result<Option<Box<dyn BlockDevice>>> {
    if let Some(path) = config
        .stripe_source
        .as_ref()
        .and_then(|stripe_source| stripe_source.raw_image_path())
    {
        let readonly = true;
        Ok(Some(create_io_engine_device(
            config.tuning.io_engine.clone(),
            path.to_path_buf(),
            64,
            readonly,
            true,
            config.tuning.write_through,
        )?))
    } else {
        Ok(None)
    }
}

pub fn build_block_device(
    path: &Path,
    config: &v2::Config,
    readonly: bool,
) -> Result<Box<dyn BlockDevice>> {
    let mut block_device: Box<dyn BlockDevice> = create_io_engine_device(
        config.tuning.io_engine.clone(),
        PathBuf::from(path),
        config.tuning.queue_size,
        readonly,
        true,
        config.tuning.write_through,
    )?;

    if let Some(encryption) = &config.encryption {
        let xts_key = config
            .secrets
            .get(encryption.xts_key.id())
            .ok_or_else(|| {
                crate::ubiblk_error!(InvalidParameter {
                    description: format!(
                        "Encryption secret '{}' is missing",
                        encryption.xts_key.id()
                    ),
                })
            })?
            .as_bytes();
        let (key1, key2) = xts_key.split_at(32);
        block_device =
            block_device::CryptBlockDevice::new(block_device, key1.to_vec(), key2.to_vec())?;
    }

    Ok(block_device)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block_device::bdev_test::TestBlockDevice;
    use crate::config::v2::stripe_source::StripeSourceConfig;
    use crate::config::v2::{self, DeviceSection};
    use crate::utils::umask_guard::UMASK_LOCK;
    use std::os::unix::fs::symlink;
    use std::os::unix::fs::PermissionsExt;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;

    fn test_config(
        data_path: &Path,
        metadata_path: Option<&Path>,
        stripe_source: Option<StripeSourceConfig>,
    ) -> v2::Config {
        v2::Config {
            device: DeviceSection {
                data_path: data_path.to_path_buf(),
                metadata_path: metadata_path.map(|path| path.to_path_buf()),
                vhost_socket: None,
                rpc_socket: None,
                device_id: "ubiblk".to_string(),
                track_written: false,
            },
            tuning: v2::tuning::TuningSection {
                queue_size: 128,
                ..Default::default()
            },
            encryption: None,
            danger_zone: v2::DangerZone {
                enabled: true,
                allow_unencrypted_disk: true,
                allow_inline_plaintext_secrets: true,
                allow_secret_over_regular_file: true,
                allow_unencrypted_connection: true,
            },
            stripe_source,
            secrets: std::collections::HashMap::new(),
        }
    }

    #[test]
    fn build_backend_env_no_metadata() {
        let disk_file = tempfile::NamedTempFile::new().unwrap();
        disk_file.as_file().set_len(10 * 1024 * 1024).unwrap();

        let config = test_config(disk_file.path(), None, None);

        let result = BackendEnv::build(&config);
        assert!(result.is_ok());
    }

    #[test]
    fn ensure_metadata_file_creates_with_mode_0600() {
        let _umask_guard = UMASK_LOCK.lock().unwrap();
        let dir = tempfile::tempdir().unwrap();
        let metadata_path = dir.path().join("metadata.bin");

        ensure_metadata_file(&metadata_path, SECTOR_SIZE).unwrap();

        assert!(metadata_path.exists());
        let mode = std::fs::metadata(&metadata_path)
            .unwrap()
            .permissions()
            .mode()
            & 0o777;
        assert_eq!(mode, 0o600);
        assert_eq!(
            std::fs::metadata(&metadata_path).unwrap().len(),
            SECTOR_SIZE as u64
        );
    }

    #[test]
    fn ensure_metadata_file_fixes_existing_mode() {
        let _umask_guard = UMASK_LOCK.lock().unwrap();
        let dir = tempfile::tempdir().unwrap();
        let metadata_path = dir.path().join("metadata.bin");
        std::fs::write(&metadata_path, []).unwrap();
        std::fs::set_permissions(&metadata_path, std::fs::Permissions::from_mode(0o644)).unwrap();

        ensure_metadata_file(&metadata_path, SECTOR_SIZE * 4).unwrap();

        let mode = std::fs::metadata(&metadata_path)
            .unwrap()
            .permissions()
            .mode()
            & 0o777;
        assert_eq!(mode, 0o600);
        assert_eq!(
            std::fs::metadata(&metadata_path).unwrap().len(),
            (SECTOR_SIZE * 4) as u64
        );
    }

    #[test]
    fn ensure_metadata_file_clears_special_mode_bits() {
        let _umask_guard = UMASK_LOCK.lock().unwrap();
        let dir = tempfile::tempdir().unwrap();
        let metadata_path = dir.path().join("metadata.bin");
        std::fs::write(&metadata_path, []).unwrap();
        std::fs::set_permissions(&metadata_path, std::fs::Permissions::from_mode(0o4600)).unwrap();

        ensure_metadata_file(&metadata_path, SECTOR_SIZE * 6).unwrap();

        let mode = std::fs::metadata(&metadata_path)
            .unwrap()
            .permissions()
            .mode()
            & 0o7777;
        assert_eq!(mode, 0o600);
        assert_eq!(
            std::fs::metadata(&metadata_path).unwrap().len(),
            (SECTOR_SIZE * 6) as u64
        );
    }

    #[test]
    fn ensure_metadata_file_rejects_symlink_path() {
        let _umask_guard = UMASK_LOCK.lock().unwrap();
        let dir = tempfile::tempdir().unwrap();
        let target_path = dir.path().join("target.bin");
        let metadata_path = dir.path().join("metadata.bin");
        std::fs::write(&target_path, []).unwrap();
        symlink(&target_path, &metadata_path).unwrap();

        let result = ensure_metadata_file(&metadata_path, SECTOR_SIZE);
        assert!(result.is_err());
    }

    #[test]
    fn ensure_metadata_file_expands_existing_file_when_too_small() {
        let _umask_guard = UMASK_LOCK.lock().unwrap();
        let dir = tempfile::tempdir().unwrap();
        let metadata_path = dir.path().join("metadata.bin");
        std::fs::write(&metadata_path, [0u8; 1]).unwrap();

        ensure_metadata_file(&metadata_path, SECTOR_SIZE * 3).unwrap();

        assert_eq!(
            std::fs::metadata(&metadata_path).unwrap().len(),
            (SECTOR_SIZE * 3) as u64
        );
    }

    fn build_test_bgworker_config() -> (BgWorkerConfig, Sender<BgWorkerRequest>) {
        let stripe_sector_count_shift = 11;
        let target_dev = TestBlockDevice::new(1024 * 1024);
        let metadata_dev = TestBlockDevice::new(1024 * 1024);
        let metadata = UbiMetadata::new(stripe_sector_count_shift, 16, 0);
        metadata.save_to_bdev(&metadata_dev).unwrap();
        let loaded_metadata = UbiMetadata::load_from_bdev(&metadata_dev).unwrap();
        let shared_state = SharedMetadataState::new(&loaded_metadata);
        let stripe_source_builder = Box::new(StripeSourceBuilder::new(
            test_config(Path::new("/tmp/ubiblk-test-disk"), None, None),
            shared_state.stripe_sector_count(),
            loaded_metadata.has_fetched_all_stripes(),
        ));
        let (sender, receiver) = channel();

        (
            BgWorkerConfig {
                target_dev: Box::new(target_dev),
                stripe_source_builder,
                metadata_dev: Box::new(metadata_dev),
                alignment: 4096,
                autofetch: false,
                shared_state,
                receiver,
            },
            sender,
        )
    }

    #[test]
    fn run_bgworker_handles_shutdown_request() {
        let (config, sender) = build_test_bgworker_config();
        sender.send(BgWorkerRequest::Shutdown).unwrap();
        let mut worker = BackendEnv::build_bgworker(config).unwrap();
        worker.run();
    }

    #[test]
    fn spawn_bgworker_thread_runs_and_joins() {
        let (config, sender) = build_test_bgworker_config();
        let (startup_sender, startup_receiver) = channel();
        let handle = BackendEnv::spawn_bgworker_thread(config, startup_sender).unwrap();
        startup_receiver.recv().unwrap().unwrap();
        sender.send(BgWorkerRequest::Shutdown).unwrap();
        handle.join().unwrap();
    }

    #[test]
    fn run_backend_loop_invokes_backend_once() {
        let disk_file = tempfile::NamedTempFile::new().unwrap();
        disk_file.as_file().set_len(10 * 1024 * 1024).unwrap();

        let config = test_config(disk_file.path(), None, None);

        let call_count = Arc::new(AtomicUsize::new(0));
        let call_count_handle = call_count.clone();
        run_backend_loop(&config, "test-backend", false, |_| {
            call_count_handle.fetch_add(1, Ordering::SeqCst);
            Ok(())
        })
        .unwrap();

        assert_eq!(call_count.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn build_backend_env_with_invalid_path() {
        let config = test_config(Path::new("/non/existent/path"), None, None);

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

        let config = test_config(
            disk_file.path(),
            Some(metadata_path.path()),
            Some(StripeSourceConfig::Raw {
                image_path: image_file.path().to_path_buf(),
                autofetch: false,
                copy_on_read: false,
            }),
        );

        init_metadata(&config, 11).unwrap();

        let result = BackendEnv::build(&config);
        assert!(result.is_ok());
    }

    #[test]
    fn run_backend_loop_fails_when_bgworker_fails_to_start() {
        let disk_file = tempfile::NamedTempFile::new().unwrap();
        disk_file.as_file().set_len(1024 * 1024).unwrap();

        let image_file = tempfile::NamedTempFile::new().unwrap();
        image_file.as_file().set_len(4 * 1024 * 1024).unwrap();

        let metadata_path = tempfile::NamedTempFile::new().unwrap();
        metadata_path.as_file().set_len(1024 * 1024).unwrap();

        let config = test_config(
            disk_file.path(),
            Some(metadata_path.path()),
            Some(StripeSourceConfig::Raw {
                image_path: image_file.path().to_path_buf(),
                autofetch: false,
                copy_on_read: true,
            }),
        );

        init_metadata(&config, 11).unwrap();

        let call_count = Arc::new(AtomicUsize::new(0));
        let call_count_handle = call_count.clone();
        let result = run_backend_loop(&config, "test-backend", false, |_| {
            call_count_handle.fetch_add(1, Ordering::SeqCst);
            Ok(())
        });

        assert!(result.is_err());
        let err = result.err().unwrap().to_string();
        assert!(err.contains("Failed to run bgworker thread"));
        assert!(err.contains("Failed to build bgworker"));
        assert!(err.contains("Source stripe count 4 exceeds metadata stripe count 1"));

        assert_eq!(call_count.load(Ordering::SeqCst), 0);
    }
}
