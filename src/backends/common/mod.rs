use std::{
    cmp,
    path::{Path, PathBuf},
    sync::mpsc::{channel, Receiver, Sender},
};

use log::{error, info, warn};
use nix::sys::statfs::statfs;
use ubiblk_macros::error_context;

use crate::{
    block_device::{
        self, BgWorker, BgWorkerRequest, BlockDevice, SharedMetadataState, StatusReporter,
        SyncBlockDevice, UbiMetadata, UringBlockDevice,
    },
    config::{DeviceConfig, IoEngine},
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
    config: DeviceConfig,
    status_reporter: Option<StatusReporter>,
    io_trackers: Vec<io_tracking::IoTracker>,
}

impl BackendEnv {
    #[error_context("Failed to build backend environment")]
    pub fn build(config: &DeviceConfig) -> Result<Self> {
        let alignment = Self::determine_alignment(&config.path)?;

        let disk_device = build_block_device(&config.path, config, false)
            .context("Failed to build disk device")?;
        let metadata_device = config
            .metadata_path
            .as_ref()
            .map(|path| {
                warn_if_no_atomic_write_support(path);
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
            self.bgworker_thread = Some(Self::spawn_bgworker_thread(config)?);
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

    pub fn config(&self) -> &DeviceConfig {
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

    #[error_context("Failed to determine filesystem alignment for path: {}", path)]
    fn determine_alignment(path: &str) -> Result<usize> {
        let stat = statfs(Path::new(path)).map_err(|e| {
            crate::ubiblk_error!(InvalidParameter {
                description: format!("Failed to statfs {path}: {e}"),
            })
        })?;

        Ok(cmp::max(BUFFER_ALIGNMENT, stat.block_size() as usize))
    }

    #[error_context("Failed to build lazy block device")]
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

    fn build_io_trackers(config: &DeviceConfig) -> Vec<io_tracking::IoTracker> {
        (0..config.num_queues)
            .map(|_| io_tracking::IoTracker::new(config.queue_size))
            .collect()
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
}

impl Drop for BackendEnv {
    fn drop(&mut self) {
        self.stop_bgworker_thread();
    }
}

pub fn run_backend_loop<F>(
    config: &DeviceConfig,
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

    let _rpc_handle = if let Some(path) = config.rpc_socket_path.as_ref() {
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

pub fn init_metadata(config: &DeviceConfig, stripe_sector_count_shift: u8) -> Result<()> {
    let metadata_path = config.metadata_path.as_ref().ok_or_else(|| {
        crate::ubiblk_error!(InvalidParameter {
            description: "metadata_path is none".to_string(),
        })
    })?;

    let disk_bdev = build_block_device(&config.path, config, false)
        .context("Failed to build disk block device")?;
    let stripe_sector_count = 1u64 << stripe_sector_count_shift;
    let base_stripe_count = disk_bdev.stripe_count(stripe_sector_count);

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

    let metadata_bdev = build_block_device(metadata_path, config, false)
        .context("Failed to build metadata block device")?;
    metadata.save_to_bdev(metadata_bdev.as_ref())?;
    Ok(())
}

#[error_context("Failed to create I/O engine device")]
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

/// Check whether a metadata device path supports atomic sector writes via
/// `statx(STATX_WRITE_ATOMIC)` (Linux 6.13+). Logs a warning if the device
/// does not report atomic write support or if the check is unavailable.
/// Never fails — errors are silently ignored so startup is never blocked.
fn warn_if_no_atomic_write_support(path: &str) {
    // STATX_WRITE_ATOMIC was added in Linux 6.13. The constant is not yet in
    // the libc crate, so we define it ourselves. The kernel zeroes unknown mask
    // bits in the statx result, making this safe on older kernels.
    const STATX_WRITE_ATOMIC: u32 = 0x0001_0000;

    let c_path = match std::ffi::CString::new(path) {
        Ok(p) => p,
        Err(_) => return,
    };

    let mut stx: libc::statx = unsafe { std::mem::zeroed() };
    let ret = unsafe {
        libc::statx(
            libc::AT_FDCWD,
            c_path.as_ptr(),
            0,
            STATX_WRITE_ATOMIC,
            &mut stx,
        )
    };

    if ret != 0 {
        // statx syscall failed (ENOSYS on very old kernels, or other error).
        // Don't warn about atomic writes — we simply can't check.
        return;
    }

    // If the kernel populated the WRITE_ATOMIC field, check the value.
    // On kernels < 6.13, the bit won't be set in stx_mask and the atomic
    // write fields in the spare area will be zero.
    if stx.stx_mask & STATX_WRITE_ATOMIC != 0 {
        // Kernel supports STATX_WRITE_ATOMIC. The stx_atomic_write_unit_min
        // field lives at offset 0xa0 in the kernel statx struct (start of
        // the spare area). Read it via byte-offset pointer arithmetic since
        // the libc crate's __statx_pad3 field is private.
        let base = std::ptr::addr_of!(stx) as *const u8;
        let atomic_write_unit_min = unsafe { (base.add(0xa0) as *const u32).read_unaligned() };
        if atomic_write_unit_min >= SECTOR_SIZE as u32 {
            return; // Device reports atomic write support
        }
    }

    warn!(
        "Metadata device '{}' does not report atomic write support. \
         Torn metadata writes are possible on power failure. \
         Consider using an NVMe device or metadata format v2 (with checksums) for protection.",
        path
    );
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
    use crate::block_device::bdev_test::TestBlockDevice;
    use crate::config::{RawStripeSourceConfig, StripeSourceConfig};
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;

    #[test]
    fn build_backend_env_no_metadata() {
        let disk_file = tempfile::NamedTempFile::new().unwrap();
        disk_file.as_file().set_len(10 * 1024 * 1024).unwrap();

        let config = DeviceConfig {
            path: disk_file.path().to_str().unwrap().to_string(),
            socket: Some("/tmp/ubiblk-test.sock".to_string()),
            queue_size: 128,
            ..Default::default()
        };

        let result = BackendEnv::build(&config);
        assert!(result.is_ok());
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
            DeviceConfig::default(),
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
        BackendEnv::run_bgworker(config);
    }

    #[test]
    fn spawn_bgworker_thread_runs_and_joins() {
        let (config, sender) = build_test_bgworker_config();
        let handle = BackendEnv::spawn_bgworker_thread(config).unwrap();
        sender.send(BgWorkerRequest::Shutdown).unwrap();
        handle.join().unwrap();
    }

    #[test]
    fn run_backend_loop_invokes_backend_once() {
        let disk_file = tempfile::NamedTempFile::new().unwrap();
        disk_file.as_file().set_len(10 * 1024 * 1024).unwrap();

        let config = DeviceConfig {
            path: disk_file.path().to_str().unwrap().to_string(),
            queue_size: 128,
            ..Default::default()
        };

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
        let config = DeviceConfig {
            path: "/non/existent/path".to_string(),
            socket: Some("/tmp/ubiblk-test.sock".to_string()),
            queue_size: 128,
            ..Default::default()
        };

        let result = BackendEnv::build(&config);
        assert!(result.is_err());
    }

    #[test]
    fn warn_if_no_atomic_write_support_does_not_panic() {
        // Calling on a tempfile should not panic or crash, regardless of
        // kernel support for STATX_WRITE_ATOMIC.
        let tmpfile = tempfile::NamedTempFile::new().unwrap();
        warn_if_no_atomic_write_support(tmpfile.path().to_str().unwrap());
    }

    #[test]
    fn warn_if_no_atomic_write_support_nonexistent_path() {
        // Should not panic for a path that doesn't exist (statx will fail).
        warn_if_no_atomic_write_support("/nonexistent/path/for/testing");
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
            socket: Some("/tmp/ubiblk-test.sock".to_string()),
            queue_size: 128,
            ..Default::default()
        };

        init_metadata(&config, 11).unwrap();

        let result = BackendEnv::build(&config);
        assert!(result.is_ok());
    }
}
