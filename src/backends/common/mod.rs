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
        self,
        bdev_spill::{
            device::SpillBlockDevice,
            map::{
                format::Binding,
                sectors_needed,
                storage::{FileStorage, MapStorage},
                Map,
            },
            state::SharedState,
            task::{Geometry, SpillTask},
        },
        BgWorker, BgWorkerRequest, BlockDevice, LazyTask, SharedMetadataState, StatusReporter,
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

/// How many journal blocks the map gets. Each is a sector and a commit uses
/// one, so this is how many commits fit between checkpoints.
const MAP_JOURNAL_BLOCKS: u64 = 1024;

/// How many chunks the spill task moves at once.
const SPILL_CONCURRENCY: usize = 4;

/// How much memory the per-chunk state may take. At the default chunk size
/// this is a device of about 4 TiB; a larger one needs larger chunks.
const MAX_CHUNK_STATE_BYTES: u64 = 256 * 1024 * 1024;

/// What the worker thread needs to build the spill task once it is on it.
struct SpillTaskConfig {
    base: Box<dyn BlockDevice>,
    state: SharedState,
    geometry: Geometry,
    map_path: PathBuf,
    binding: Binding,
    store: v2::stripe_source::ArchiveStorageConfig,
    secrets: std::collections::HashMap<String, v2::secrets::ResolvedSecret>,
    prefix: String,
    open_id: u64,
}

struct BgWorkerConfig {
    target_dev: Box<dyn BlockDevice>,
    stripe_source_builder: Box<StripeSourceBuilder>,
    metadata_dev: Box<dyn BlockDevice>,
    alignment: usize,
    autofetch: bool,
    shared_state: SharedMetadataState,
}

pub struct BackendEnv {
    bdev: Box<dyn BlockDevice>,
    bgworker_config: Option<BgWorkerConfig>,
    spill_config: Option<SpillTaskConfig>,
    bgworker_receiver: Option<Receiver<BgWorkerRequest>>,
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

        if let Some(spill) = &config.spill {
            return Self::build_with_spill(config, spill, alignment);
        }

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
                spill_config: None,
                bgworker_receiver: None,
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
        let lazy = self.bgworker_config.take();
        let spill = self.spill_config.take();
        if let Some(receiver) = self.bgworker_receiver.take() {
            let (startup_sender, startup_receiver) = channel();
            self.bgworker_thread = Some(Self::spawn_bgworker_thread(
                receiver,
                lazy,
                spill,
                startup_sender,
            )?);

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
        };

        Ok(BackendEnv {
            bdev: bdev_lazy,
            bgworker_config: Some(bgworker_config),
            spill_config: None,
            bgworker_receiver: Some(bgworker_receiver),
            bgworker_sender: Some(bgworker_sender),
            bgworker_thread: None,
            alignment,
            config: config.clone(),
            status_reporter: Some(status_reporter),
            io_trackers: Self::build_io_trackers(config),
        })
    }

    /// A spill device: the disk below is a pool of slots, the object store
    /// holds what does not fit, and everything version one does not support is
    /// refused here rather than half-worked.
    #[error_context("Failed to build a spill device")]
    fn build_with_spill(
        config: &v2::Config,
        spill: &v2::spill::SpillSection,
        alignment: usize,
    ) -> Result<Self> {
        let refuse = |what: &str| -> Result<()> {
            Err(crate::ubiblk_error!(InvalidParameter {
                description: format!("a spill device does not support {what}"),
            }))
        };
        if config.encryption.is_none() {
            // Objects leave the host. Version one will not promise ciphertext
            // it is not producing.
            refuse("running unencrypted")?;
        }
        if config.stripe_source.is_some() {
            refuse("a stripe source")?;
        }
        if config.device.metadata_path.is_some() {
            refuse("lazy metadata")?;
        }
        if config.tuning.write_through {
            refuse("write_through, which needs durability on every write")?;
        }
        if matches!(config.tuning.io_engine, v2::tuning::IoEngine::Sync) {
            refuse("the sync engine, which blocks the worker it shares")?;
        }

        let chunk_bytes = spill.chunk_bytes();
        if chunk_bytes == 0 || !chunk_bytes.is_multiple_of(SECTOR_SIZE as u64) {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: format!("chunk_kb {} is not whole sectors", spill.chunk_kb),
            }));
        }
        let largest_request = u64::from(config.tuning.seg_size_max)
            .saturating_mul(u64::from(config.tuning.seg_count_max));
        if chunk_bytes > largest_request {
            // Repair is an overwrite of a whole chunk, and a guest that cannot
            // ask for one in a single request cannot repair anything.
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: format!(
                    "chunk_kb {} is larger than the {largest_request} bytes a request can carry",
                    spill.chunk_kb
                ),
            }));
        }

        let base = create_io_engine_device(
            config.tuning.io_engine.clone(),
            config.device.data_path.clone(),
            config.tuning.queue_size,
            false,
            true,
            false,
        )
        .context("Failed to build the disk the slots live on")?;

        let chunk_sectors = chunk_bytes / SECTOR_SIZE as u64;
        let device_bytes = spill.size_mb.checked_mul(1024 * 1024).ok_or_else(|| {
            crate::ubiblk_error!(InvalidParameter {
                description: format!("size_mb {} is not a size", spill.size_mb),
            })
        })?;
        let device_sectors = device_bytes.div_ceil(SECTOR_SIZE as u64);
        if device_sectors == 0 {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: "size_mb is zero, so there is no device".to_string(),
            }));
        }
        // Every chunk costs a word of memory whether or not anything is ever
        // written to it, so a device can be too large to serve with a chunk
        // this small.
        let chunk_count = device_sectors.div_ceil(chunk_sectors);
        let state_bytes = chunk_count.saturating_mul(8);
        if state_bytes > MAX_CHUNK_STATE_BYTES {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: format!(
                    "a {} MiB device in {} KiB chunks needs {} MiB just to track them; \
                     use a larger chunk_kb",
                    spill.size_mb,
                    spill.chunk_kb,
                    state_bytes / (1024 * 1024)
                ),
            }));
        }
        let slot_count = base.sector_count() / chunk_sectors;
        if slot_count == 0 {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: format!(
                    "{} holds {} sectors, not even one chunk",
                    config.device.data_path.display(),
                    base.sector_count()
                ),
            }));
        }
        if slot_count * chunk_sectors >= device_sectors {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: "the disk is as large as the device, so nothing can spill".to_string(),
            }));
        }
        // A chunk's word names its slot in 24 bits, and handing out one past
        // that would panic where nothing could catch it.
        if slot_count > u64::from(crate::block_device::bdev_spill::state::MAX_SLOTS) {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: format!(
                    "{} slots of {chunk_bytes} bytes is more than the {} a device can name; \
                     use a larger chunk_kb",
                    slot_count,
                    crate::block_device::bdev_spill::state::MAX_SLOTS
                ),
            }));
        }
        let slot_count = slot_count as u32;

        let geometry = Geometry {
            chunk_sectors,
            device_sectors,
            slot_count,
        };
        let state = SharedState::new(geometry.chunk_count() as usize);
        let (sender, receiver) = channel();
        let spill_device =
            SpillBlockDevice::new(base.clone(), state.clone(), geometry, sender.clone())?;
        let bdev = wrap_with_encryption(spill_device, config)?;

        let mut open_id = [0u8; 8];
        openssl::rand::rand_bytes(&mut open_id).map_err(|e| {
            crate::ubiblk_error!(InvalidParameter {
                description: format!("Failed to name this open: {e}"),
            })
        })?;

        Ok(BackendEnv {
            bdev,
            bgworker_config: None,
            spill_config: Some(SpillTaskConfig {
                base,
                state,
                geometry,
                map_path: spill.map_path.clone(),
                binding: Binding {
                    device_uuid: spill.uuid_bytes()?,
                    chunk_size: chunk_bytes as u32,
                    logical_sector_count: device_sectors,
                    slot_count,
                    store_digest: spill.store_digest(),
                },
                store: spill.store.clone(),
                secrets: config.secrets.clone(),
                prefix: spill.prefix.clone(),
                open_id: u64::from_le_bytes(open_id),
            }),
            bgworker_receiver: Some(receiver),
            bgworker_sender: Some(sender),
            bgworker_thread: None,
            alignment,
            config: config.clone(),
            status_reporter: None,
            io_trackers: Self::build_io_trackers(config),
        })
    }

    /// Open the map, or lay one out if this device has never been served
    /// before. Opening checks the map belongs to this device; creating refuses
    /// if one is already there.
    fn build_spill_task(config: SpillTaskConfig) -> Result<SpillTask> {
        let chunk_count = config.geometry.chunk_count();
        let sectors = sectors_needed(chunk_count, MAP_JOURNAL_BLOCKS);
        // What decides is whether there is a map here, not whether there is a
        // file: a creation interrupted after the file was sized leaves a
        // full-length file with nothing in it, and that has to be a fresh
        // start rather than a device that can never be opened again.
        let exists = FileStorage::open(&config.map_path)
            .ok()
            .and_then(|storage| {
                crate::block_device::bdev_spill::map::superblock::read(&storage).ok()
            })
            .flatten()
            .is_some();

        let map = if exists {
            Map::open(
                Box::new(FileStorage::open(&config.map_path)?) as Box<dyn MapStorage>,
                config.binding,
            )
            .context("Failed to open the spill map")?
        } else {
            Map::create(
                Box::new(FileStorage::create(&config.map_path, sectors)?) as Box<dyn MapStorage>,
                config.binding,
                chunk_count,
                MAP_JOURNAL_BLOCKS,
            )
            .context("Failed to lay out the spill map")?
        };

        let store = StripeSourceBuilder::build_archive_store(&config.store, &config.secrets)
            .context("Failed to reach the object store")?;

        SpillTask::new(
            config.state,
            map,
            store,
            config.base.create_channel()?,
            config.geometry,
            config.prefix,
            config.open_id,
            SPILL_CONCURRENCY,
        )
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
        receiver: Receiver<BgWorkerRequest>,
        lazy: Option<BgWorkerConfig>,
        spill: Option<SpillTaskConfig>,
        startup_sender: Sender<Result<()>>,
    ) -> Result<std::thread::JoinHandle<()>> {
        std::thread::Builder::new()
            .name("bgworker".to_string())
            .spawn(move || match Self::build_bgworker(receiver, lazy, spill) {
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

    /// Build the tasks here, on the thread that will drive them: a stripe
    /// source connects, and a map is opened and recovered.
    fn build_bgworker(
        receiver: Receiver<BgWorkerRequest>,
        lazy: Option<BgWorkerConfig>,
        spill: Option<SpillTaskConfig>,
    ) -> Result<BgWorker> {
        let mut worker = BgWorker::new(receiver);
        if let Some(config) = lazy {
            worker.set_lazy_task(Self::build_lazy_task(config)?);
        }
        if let Some(config) = spill {
            worker.set_spill_task(Self::build_spill_task(config)?);
        }
        Ok(worker)
    }

    fn build_lazy_task(config: BgWorkerConfig) -> Result<LazyTask> {
        let BgWorkerConfig {
            target_dev,
            stripe_source_builder,
            metadata_dev,
            alignment,
            autofetch,
            shared_state,
        } = config;

        let stripe_source = match stripe_source_builder.build() {
            Ok(source) => source,
            Err(e) => {
                error!("Failed to build stripe source: {e}");
                return Err(e);
            }
        };

        LazyTask::new(
            stripe_source,
            &*target_dev,
            &*metadata_dev,
            alignment,
            autofetch,
            shared_state,
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
    let block_device: Box<dyn BlockDevice> = create_io_engine_device(
        config.tuning.io_engine.clone(),
        PathBuf::from(path),
        config.tuning.queue_size,
        readonly,
        true,
        config.tuning.write_through,
    )?;

    wrap_with_encryption(block_device, config)
}

/// XTS goes on last, so what leaves for the object store is ciphertext.
fn wrap_with_encryption(
    mut block_device: Box<dyn BlockDevice>,
    config: &v2::Config,
) -> Result<Box<dyn BlockDevice>> {
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
            spill: None,
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
                allow_env_secrets: false,
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
        let dir = tempfile::tempdir().unwrap();
        let metadata_path = dir.path().join("metadata.bin");
        std::fs::write(&metadata_path, [0u8; 1]).unwrap();

        ensure_metadata_file(&metadata_path, SECTOR_SIZE * 3).unwrap();

        assert_eq!(
            std::fs::metadata(&metadata_path).unwrap().len(),
            (SECTOR_SIZE * 3) as u64
        );
    }

    fn build_test_bgworker_config() -> (
        BgWorkerConfig,
        Receiver<BgWorkerRequest>,
        Sender<BgWorkerRequest>,
    ) {
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
            },
            receiver,
            sender,
        )
    }

    #[test]
    fn run_bgworker_handles_shutdown_request() {
        let (config, receiver, sender) = build_test_bgworker_config();
        sender.send(BgWorkerRequest::Shutdown).unwrap();
        let mut worker = BackendEnv::build_bgworker(receiver, Some(config), None).unwrap();
        worker.run();
    }

    #[test]
    fn spawn_bgworker_thread_runs_and_joins() {
        let (config, receiver, sender) = build_test_bgworker_config();
        let (startup_sender, startup_receiver) = channel();
        let handle =
            BackendEnv::spawn_bgworker_thread(receiver, Some(config), None, startup_sender)
                .unwrap();
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

    #[test]
    fn init_metadata_without_stripe_source() {
        let disk_file = tempfile::NamedTempFile::new().unwrap();
        disk_file.as_file().set_len(10 * 1024 * 1024).unwrap();

        let metadata_file = tempfile::NamedTempFile::new().unwrap();
        metadata_file.as_file().set_len(1024 * 1024).unwrap();

        let config = test_config(disk_file.path(), Some(metadata_file.path()), None);
        init_metadata(&config, 11).unwrap();
    }

    #[test]
    fn init_metadata_fails_without_metadata_path() {
        let disk_file = tempfile::NamedTempFile::new().unwrap();
        disk_file.as_file().set_len(10 * 1024 * 1024).unwrap();

        let config = test_config(disk_file.path(), None, None);
        let result = init_metadata(&config, 11);
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("metadata_path"));
    }

    fn walkdir(path: &std::path::Path) -> usize {
        let Ok(entries) = std::fs::read_dir(path) else {
            return 0;
        };
        entries
            .filter_map(|entry| entry.ok())
            .map(|entry| {
                if entry.path().is_dir() {
                    walkdir(&entry.path())
                } else {
                    1
                }
            })
            .sum()
    }

    fn spill_config(dir: &std::path::Path, disk: &std::path::Path, size_mb: u64) -> v2::Config {
        use crate::config::v2::secrets::{
            resolve_secrets, SecretDef, SecretEncoding, SecretRef, SecretSource,
        };
        use base64::Engine;
        use std::collections::HashMap;

        let xts_key_b64 = base64::engine::general_purpose::STANDARD.encode([0x42u8; 64]);
        let secret_defs = HashMap::from([(
            "xts-key".to_string(),
            SecretDef {
                source: SecretSource::Inline(xts_key_b64),
                encrypted_by: None,
                encoding: SecretEncoding::Base64,
            },
        )]);
        let mut config = test_config(disk, None, None);
        let secrets = resolve_secrets(&secret_defs, &config.danger_zone).unwrap();
        config.encryption = Some(v2::EncryptionSection {
            xts_key: SecretRef::Ref("xts-key".to_string()),
        });
        config.secrets = secrets;
        config.spill = Some(v2::spill::SpillSection {
            size_mb,
            map_path: dir.join("map"),
            prefix: "spill/test".to_string(),
            device_uuid: "0123456789abcdef0123456789abcdef".to_string(),
            chunk_kb: 64,
            store: v2::stripe_source::ArchiveStorageConfig::Filesystem {
                path: dir.join("store"),
                archive_kek: None,
                autofetch: false,
            },
        });
        config
    }

    /// A spill device end to end: the map is laid out, the worker serves the
    /// chunks, and what the guest wrote comes back through a cache far smaller
    /// than the device.
    #[test]
    fn a_spill_device_serves_more_than_the_disk_holds() {
        let dir = tempfile::tempdir().unwrap();
        let disk = dir.path().join("disk.raw");
        std::fs::write(&disk, vec![0u8; 256 * 1024]).unwrap();
        std::fs::create_dir_all(dir.path().join("store")).unwrap();

        let config = spill_config(dir.path(), &disk, 4);
        let mut env = BackendEnv::build(&config).expect("a spill device");
        env.run_bgworker_thread().expect("the worker starts");

        let bdev = env.bdev();
        assert_eq!(bdev.sector_count(), 4 * 1024 * 1024 / SECTOR_SIZE as u64);
        let mut channel = bdev.create_channel().unwrap();

        // Four chunks of it, through a cache of four 64 KiB slots.
        let chunk_sectors = 64 * 1024 / SECTOR_SIZE as u64;
        for (i, byte) in [0x11u8, 0x22, 0x33, 0x44].into_iter().enumerate() {
            let buf = crate::block_device::shared_buffer(SECTOR_SIZE);
            buf.borrow_mut().as_mut_slice().fill(byte);
            let at = i as u64 * chunk_sectors * 5;
            channel.add_write(at, 1, buf.clone(), 1);
            channel.submit().expect("submit");
            crate::block_device::wait_for_completion(
                channel.as_mut(),
                1,
                std::time::Duration::from_secs(10),
            )
            .expect("write");
        }

        for (i, byte) in [0x11u8, 0x22, 0x33, 0x44].into_iter().enumerate() {
            let buf = crate::block_device::shared_buffer(SECTOR_SIZE);
            let at = i as u64 * chunk_sectors * 5;
            channel.add_read(at, 1, buf.clone(), 2);
            channel.submit().expect("submit");
            crate::block_device::wait_for_completion(
                channel.as_mut(),
                2,
                std::time::Duration::from_secs(10),
            )
            .expect("read");
            assert!(
                buf.borrow().as_slice().iter().all(|b| *b == byte),
                "chunk {i} came back as something else"
            );
        }

        env.stop_bgworker_thread();
    }

    /// Everything together: a device larger than its disk, written across
    /// more chunks than the cache holds, flushed, closed, and opened again
    /// from the same map and store.
    #[test]
    fn a_spill_device_comes_back_with_what_it_was_given() {
        let dir = tempfile::tempdir().unwrap();
        let disk = dir.path().join("disk.raw");
        std::fs::write(&disk, vec![0u8; 256 * 1024]).unwrap();
        std::fs::create_dir_all(dir.path().join("store")).unwrap();
        let config = spill_config(dir.path(), &disk, 4);

        let chunk_sectors = 64 * 1024 / SECTOR_SIZE as u64;
        let written: Vec<(u64, u8)> = (0..8u64)
            .map(|i| (i * chunk_sectors + i, 0x10 + i as u8))
            .collect();

        {
            let mut env = BackendEnv::build(&config).expect("a spill device");
            env.run_bgworker_thread().expect("the worker starts");
            let bdev = env.bdev();
            let mut channel = bdev.create_channel().unwrap();

            for (at, byte) in &written {
                let buf = crate::block_device::shared_buffer(SECTOR_SIZE);
                buf.borrow_mut().as_mut_slice().fill(*byte);
                channel.add_write(*at, 1, buf, 1);
                channel.submit().unwrap();
                crate::block_device::wait_for_completion(
                    channel.as_mut(),
                    1,
                    std::time::Duration::from_secs(10),
                )
                .expect("write");
            }

            channel.add_flush(2);
            channel.submit().unwrap();
            crate::block_device::wait_for_completion(
                channel.as_mut(),
                2,
                std::time::Duration::from_secs(10),
            )
            .expect("flush");

            env.stop_bgworker_thread();
        }

        let objects = walkdir(&dir.path().join("store"));
        assert!(
            objects > 0,
            "nothing was uploaded, so this never exercised the cold tier"
        );

        let mut env = BackendEnv::build(&config).expect("the device opens again");
        env.run_bgworker_thread().expect("the worker starts again");
        let bdev = env.bdev();
        let mut channel = bdev.create_channel().unwrap();

        for (at, byte) in &written {
            let buf = crate::block_device::shared_buffer(SECTOR_SIZE);
            channel.add_read(*at, 1, buf.clone(), 3);
            channel.submit().unwrap();
            crate::block_device::wait_for_completion(
                channel.as_mut(),
                3,
                std::time::Duration::from_secs(10),
            )
            .unwrap_or_else(|e| panic!("reading sector {at} back: {e}"));
            assert!(
                buf.borrow().as_slice().iter().all(|b| *b == *byte),
                "sector {at} came back as something else after a restart"
            );
        }

        env.stop_bgworker_thread();
    }

    /// A guest that never flushed still gets its writes back after an orderly
    /// shutdown: stopping records where everything is. A crash is what the
    /// flush contract is about; this is not one.
    #[test]
    fn stopping_a_spill_device_records_what_was_written() {
        let dir = tempfile::tempdir().unwrap();
        let disk = dir.path().join("disk.raw");
        std::fs::write(&disk, vec![0u8; 256 * 1024]).unwrap();
        std::fs::create_dir_all(dir.path().join("store")).unwrap();
        let config = spill_config(dir.path(), &disk, 4);

        {
            let mut env = BackendEnv::build(&config).expect("a spill device");
            env.run_bgworker_thread().expect("the worker starts");
            let bdev = env.bdev();
            let mut channel = bdev.create_channel().unwrap();
            let buf = crate::block_device::shared_buffer(SECTOR_SIZE);
            buf.borrow_mut().as_mut_slice().fill(0x5C);
            channel.add_write(9, 1, buf, 1);
            channel.submit().unwrap();
            crate::block_device::wait_for_completion(
                channel.as_mut(),
                1,
                std::time::Duration::from_secs(10),
            )
            .expect("write");
            // No flush from the guest at all.
            env.stop_bgworker_thread();
        }

        let mut env = BackendEnv::build(&config).expect("the device opens again");
        env.run_bgworker_thread().expect("the worker starts again");
        let bdev = env.bdev();
        let mut channel = bdev.create_channel().unwrap();
        let buf = crate::block_device::shared_buffer(SECTOR_SIZE);
        channel.add_read(9, 1, buf.clone(), 2);
        channel.submit().unwrap();
        crate::block_device::wait_for_completion(
            channel.as_mut(),
            2,
            std::time::Duration::from_secs(10),
        )
        .expect("read");

        assert!(
            buf.borrow().as_slice().iter().all(|b| *b == 0x5C),
            "an orderly shutdown lost a write"
        );
        env.stop_bgworker_thread();
    }

    #[test]
    fn what_a_spill_device_does_not_support_is_refused() {
        let dir = tempfile::tempdir().unwrap();
        let disk = dir.path().join("disk.raw");
        std::fs::write(&disk, vec![0u8; 256 * 1024]).unwrap();
        std::fs::create_dir_all(dir.path().join("store")).unwrap();

        type Change = Box<dyn Fn(&mut v2::Config)>;
        let unsupported: Vec<(&str, Change)> = vec![
            (
                "no encryption",
                Box::new(|c: &mut v2::Config| c.encryption = None),
            ),
            (
                "write through",
                Box::new(|c: &mut v2::Config| c.tuning.write_through = true),
            ),
            (
                "the sync engine",
                Box::new(|c: &mut v2::Config| c.tuning.io_engine = v2::tuning::IoEngine::Sync),
            ),
            (
                "lazy metadata",
                Box::new(|c: &mut v2::Config| {
                    c.device.metadata_path = Some(std::path::PathBuf::from("/tmp/meta"))
                }),
            ),
            (
                "a chunk larger than a request",
                Box::new(|c: &mut v2::Config| {
                    if let Some(spill) = &mut c.spill {
                        spill.chunk_kb = 1024;
                    }
                }),
            ),
            (
                "a device too large to track in chunks that small",
                Box::new(|c: &mut v2::Config| {
                    if let Some(spill) = &mut c.spill {
                        spill.size_mb = 64 * 1024 * 1024; // 64 TiB
                        spill.chunk_kb = 4;
                    }
                }),
            ),
            (
                "a size that is not a size",
                Box::new(|c: &mut v2::Config| {
                    if let Some(spill) = &mut c.spill {
                        spill.size_mb = u64::MAX;
                    }
                }),
            ),
            (
                "a device of no size",
                Box::new(|c: &mut v2::Config| {
                    if let Some(spill) = &mut c.spill {
                        spill.size_mb = 0;
                    }
                }),
            ),
        ];

        for (what, change) in unsupported {
            let mut config = spill_config(dir.path(), &disk, 4);
            change(&mut config);
            assert!(
                BackendEnv::build(&config).is_err(),
                "{what} was accepted by a spill device"
            );
        }

        // A slot number is 24 bits wide, and handing out one past that would
        // panic where nothing could catch it. The disk here is sparse: it is
        // the number of slots that matters, not the bytes.
        let huge = dir.path().join("huge.raw");
        std::fs::File::create(&huge)
            .unwrap()
            .set_len(2 * 1024 * 1024 * 1024 * 1024)
            .unwrap();
        let mut config = spill_config(dir.path(), &huge, 4 * 1024 * 1024);
        if let Some(spill) = &mut config.spill {
            spill.chunk_kb = 128;
        }
        assert!(
            BackendEnv::build(&config).is_err(),
            "a cache with more slots than a chunk's word can name was accepted"
        );

        // Nothing can spill when the disk is as large as the device, so the
        // layer would never do anything.
        let roomy = dir.path().join("roomy.raw");
        std::fs::write(&roomy, vec![0u8; 8 * 1024 * 1024]).unwrap();
        assert!(BackendEnv::build(&spill_config(dir.path(), &roomy, 4)).is_err());
    }

    /// The map belongs to the device it was made for.
    #[test]
    fn a_spill_map_from_another_device_is_refused() {
        let dir = tempfile::tempdir().unwrap();
        let disk = dir.path().join("disk.raw");
        std::fs::write(&disk, vec![0u8; 256 * 1024]).unwrap();
        std::fs::create_dir_all(dir.path().join("store")).unwrap();

        let config = spill_config(dir.path(), &disk, 4);
        let mut env = BackendEnv::build(&config).expect("a spill device");
        env.run_bgworker_thread().expect("the worker starts");
        env.stop_bgworker_thread();
        drop(env);

        let mut other = spill_config(dir.path(), &disk, 4);
        if let Some(spill) = &mut other.spill {
            spill.device_uuid = "ffffffffffffffffffffffffffffffff".to_string();
        }
        let mut env = BackendEnv::build(&other).expect("building does not read the map");

        assert!(
            env.run_bgworker_thread().is_err(),
            "a map made for another device was opened"
        );
    }

    #[test]
    fn build_block_device_with_encryption() {
        use crate::config::v2::secrets::{
            resolve_secrets, SecretDef, SecretEncoding, SecretRef, SecretSource,
        };
        use std::collections::HashMap;

        let disk_file = tempfile::NamedTempFile::new().unwrap();
        disk_file.as_file().set_len(10 * 1024 * 1024).unwrap();

        // Create a 64-byte XTS key (2x32 bytes) as base64-encoded inline secret
        use base64::Engine;
        let xts_key_b64 = base64::engine::general_purpose::STANDARD.encode([0x42u8; 64]);
        let secret_defs = HashMap::from([(
            "xts-key".to_string(),
            SecretDef {
                source: SecretSource::Inline(xts_key_b64),
                encrypted_by: None,
                encoding: SecretEncoding::Base64,
            },
        )]);
        let danger_zone = v2::DangerZone {
            enabled: true,
            allow_unencrypted_disk: true,
            allow_inline_plaintext_secrets: true,
            allow_secret_over_regular_file: true,
            allow_unencrypted_connection: true,
            allow_env_secrets: false,
        };
        let secrets = resolve_secrets(&secret_defs, &danger_zone).unwrap();

        let mut config = test_config(disk_file.path(), None, None);
        config.encryption = Some(v2::EncryptionSection {
            xts_key: SecretRef::Ref("xts-key".to_string()),
        });
        config.secrets = secrets;

        let result = build_block_device(disk_file.path(), &config, false);
        assert!(
            result.is_ok(),
            "build_block_device failed: {:?}",
            result.err().map(|e| e.to_string())
        );
    }

    #[test]
    fn build_block_device_with_encryption_missing_secret() {
        use crate::config::v2::secrets::SecretRef;

        let disk_file = tempfile::NamedTempFile::new().unwrap();
        disk_file.as_file().set_len(10 * 1024 * 1024).unwrap();

        let mut config = test_config(disk_file.path(), None, None);
        config.encryption = Some(v2::EncryptionSection {
            xts_key: SecretRef::Ref("missing-key".to_string()),
        });

        let result = build_block_device(disk_file.path(), &config, false);
        assert!(result.is_err());
        let err = format!("{}", result.err().unwrap());
        assert!(err.contains("missing"));
    }

    #[test]
    fn run_backend_loop_with_rpc_socket() {
        let disk_file = tempfile::NamedTempFile::new().unwrap();
        disk_file.as_file().set_len(10 * 1024 * 1024).unwrap();

        let rpc_dir = tempfile::tempdir().unwrap();
        let rpc_path = rpc_dir.path().join("test.sock");

        let mut config = test_config(disk_file.path(), None, None);
        config.device.rpc_socket = Some(rpc_path);

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
    fn status_reporter_returns_none_without_metadata() {
        let disk_file = tempfile::NamedTempFile::new().unwrap();
        disk_file.as_file().set_len(10 * 1024 * 1024).unwrap();

        let config = test_config(disk_file.path(), None, None);
        let env = BackendEnv::build(&config).unwrap();
        assert!(env.status_reporter().is_none());
    }

    #[test]
    fn ensure_metadata_file_rejects_non_regular_file() {
        // /dev/null can be opened read+write but is not a regular file
        let result = ensure_metadata_file(Path::new("/dev/null"), SECTOR_SIZE);
        assert!(result.is_err());
        let err = format!("{}", result.err().unwrap());
        assert!(
            err.contains("not a regular file"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn ensure_metadata_file_preserves_size_when_already_large_enough() {
        let dir = tempfile::tempdir().unwrap();
        let metadata_path = dir.path().join("metadata.bin");
        // Create file larger than minimum
        std::fs::write(&metadata_path, vec![0u8; SECTOR_SIZE * 8]).unwrap();
        std::fs::set_permissions(&metadata_path, std::fs::Permissions::from_mode(0o600)).unwrap();

        ensure_metadata_file(&metadata_path, SECTOR_SIZE).unwrap();

        // Size should NOT have been truncated
        assert_eq!(
            std::fs::metadata(&metadata_path).unwrap().len(),
            (SECTOR_SIZE * 8) as u64
        );
    }

    #[test]
    fn stop_bgworker_on_env_without_bgworker() {
        let disk_file = tempfile::NamedTempFile::new().unwrap();
        disk_file.as_file().set_len(10 * 1024 * 1024).unwrap();

        let config = test_config(disk_file.path(), None, None);
        let mut env = BackendEnv::build(&config).unwrap();
        // Should not panic when there is no bgworker
        env.stop_bgworker_thread();
    }

    #[test]
    fn run_bgworker_thread_noop_without_config() {
        let disk_file = tempfile::NamedTempFile::new().unwrap();
        disk_file.as_file().set_len(10 * 1024 * 1024).unwrap();

        let config = test_config(disk_file.path(), None, None);
        let mut env = BackendEnv::build(&config).unwrap();
        // No bgworker_config, so this is a no-op
        env.run_bgworker_thread().unwrap();
    }

    #[test]
    fn create_io_engine_sync() {
        let disk_file = tempfile::NamedTempFile::new().unwrap();
        disk_file.as_file().set_len(10 * 1024 * 1024).unwrap();

        let result = create_io_engine_device(
            v2::tuning::IoEngine::Sync,
            disk_file.path().to_path_buf(),
            128,
            false,
            true,
            true,
        );
        assert!(result.is_ok());
    }
}
