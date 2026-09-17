use libublk::{
    ctrl::{UblkCtrl, UblkCtrlBuilder},
    io::{BufDescList, UblkDev, UblkQueue},
    UblkError, UblkFlags,
};
use log::{error, info, warn};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};
use ubiblk_macros::error_context;

use crate::{
    backends::common::{io_tracking::IoTracker, run_backend_loop, BackendEnv, SECTOR_SIZE},
    block_device::BlockDevice,
    config::v2,
    Result, ResultExt,
};

mod io_handler;

use io_handler::UblkIoHandler;

/// How long to wait for the kernel to complete UBLK_U_CMD_ADD_DEV.
const DEVICE_CREATE_TIMEOUT: Duration = Duration::from_secs(30);

/// How long to wait for the block device node before creating the symlink.
const DEVICE_NODE_TIMEOUT: Duration = Duration::from_secs(10);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum UblkOp {
    Read,
    Write,
    Flush,
    Unsupported,
}

impl UblkOp {
    fn from_raw(op: u32) -> Self {
        match op {
            libublk::sys::UBLK_IO_OP_READ => Self::Read,
            libublk::sys::UBLK_IO_OP_WRITE => Self::Write,
            libublk::sys::UBLK_IO_OP_FLUSH => Self::Flush,
            _ => Self::Unsupported,
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct UblkIoRequest {
    op: UblkOp,
    sector_offset: u64,
    sector_count: u32,
    request_id: usize,
    bytes: usize,
}

pub fn ublk_backend_loop(config: &v2::Config, device_symlink: Option<PathBuf>) -> Result<()> {
    run_backend_loop(config, "ublk", false, move |backend_env| {
        serve_ublk(backend_env, device_symlink.clone())
    })
}

#[error_context("Failed to serve ublk backend")]
fn serve_ublk(backend_env: &BackendEnv, device_symlink: Option<PathBuf>) -> Result<()> {
    info!("Creating ublk backend ...");

    let bdev = backend_env.bdev();
    let device_size = bdev.sector_count() * SECTOR_SIZE as u64;
    let device_name = format!("ubiblk-{}", backend_env.config().device.device_id);
    let backend_alignment = backend_env.alignment();

    let config = backend_env.config();
    let num_queues = config.tuning.num_queues as u16;
    let queue_size = config.tuning.queue_size as u16;
    let io_buf_bytes = config.tuning.seg_size_max;

    let (created_sender, created_receiver) = std::sync::mpsc::channel();
    let device = Device {
        name: device_name,
        size: device_size,
        num_queues,
        queue_size,
        io_buf_bytes,
        alignment: backend_alignment,
        symlink: device_symlink.clone(),
    };
    let io_trackers = backend_env.io_trackers().clone();
    let thread = std::thread::Builder::new()
        .name("ublk-device".to_string())
        .spawn(move || run_ublk_device(device, bdev, io_trackers, created_sender))
        .map_err(|e| crate::ubiblk_error!(ThreadCreation { source: e }))?;

    let dev_id = await_device_creation(&created_receiver, DEVICE_CREATE_TIMEOUT)?;

    // Ensure the kernel device is torn down on Ctrl-C so we don't leave a stale
    // /dev/ublk* entry if the process exits without a clean shutdown. The
    // handler opens its own control handle from the id, since the one serving
    // the device belongs to another thread.
    let ctrl_symlink = device_symlink;
    if let Err(e) = ctrlc::set_handler(move || {
        handle_ctrlc_shutdown(dev_id, ctrl_symlink.as_deref());
    }) {
        log::warn!("Failed to set Ctrl-C handler: {e}");
    }

    thread.join().map_err(|_| {
        crate::ubiblk_error!(InvalidParameter {
            description: "the ublk device thread panicked".to_string(),
        })
    })?
}

/// Wait for the device thread to report that the kernel created the device.
fn await_device_creation(
    created: &std::sync::mpsc::Receiver<Result<u32>>,
    timeout: Duration,
) -> Result<u32> {
    match created.recv_timeout(timeout) {
        Ok(created) => created,
        Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => {
            Err(crate::ubiblk_error!(InvalidParameter {
                description: "the ublk device thread stopped without creating a device".to_string(),
            }))
        }
        Err(std::sync::mpsc::RecvTimeoutError::Timeout) => Err(crate::ubiblk_error!(Timeout {
            description: format!(
                "kernel did not complete ublk device creation (UBLK_U_CMD_ADD_DEV) \
                 within {}s. This usually indicates a kernel ublk regression (for \
                 example the NULL pointer dereference in ublk_init_queues on \
                 6.17.0-*-aws kernels); check `dmesg | grep -i ublk`. The creation \
                 thread is stuck in an uninterruptible io_uring wait and cannot be \
                 cancelled; the ublk control device may stay wedged until reboot.",
                timeout.as_secs()
            ),
        })),
    }
}

/// What the device thread needs to build and serve the device.
struct Device {
    name: String,
    size: u64,
    num_queues: u16,
    queue_size: u16,
    io_buf_bytes: u32,
    alignment: usize,
    symlink: Option<PathBuf>,
}

/// Build the device and serve it, all on one thread.
///
/// Every control command libublk issues goes through a ring it keeps in
/// thread-local storage, and `UblkCtrl` is `Send` regardless: moving one to
/// another thread compiles and then panics on the first command with "Control
/// ring not initialized". So the thread that creates the device is the thread
/// that serves it, and the caller learns the device exists through `created`
/// rather than by taking the handle.
fn run_ublk_device(
    device: Device,
    bdev: Box<dyn BlockDevice>,
    io_trackers: Vec<IoTracker>,
    created: std::sync::mpsc::Sender<Result<u32>>,
) -> Result<()> {
    let ctrl = UblkCtrlBuilder::default()
        .name(&device.name)
        .nr_queues(device.num_queues)
        .depth(device.queue_size)
        .io_buf_bytes(device.io_buf_bytes)
        // Add the device immediately so the backend can bind queues in run_target.
        .dev_flags(UblkFlags::UBLK_DEV_F_ADD_DEV)
        .build();

    let ctrl = match ctrl {
        Ok(ctrl) => ctrl,
        Err(e) => {
            let _ = created.send(Err(e.into()));
            return Ok(());
        }
    };

    if created.send(Ok(ctrl.dev_info().dev_id)).is_err() {
        // The caller gave up waiting; leaving the device behind would be worse
        // than the error it already returned.
        let _ = ctrl.del_dev();
        return Ok(());
    }

    let device_size = device.size;
    let alignment = device.alignment;
    let announce_symlink = device.symlink.clone();
    ctrl.run_target(
        move |dev| configure_ublk_device(dev, device_size),
        move |qid, dev| {
            let io_tracker = io_trackers[qid as usize].clone();
            serve_ublk_queue(qid, dev, bdev.clone(), alignment, io_tracker)
        },
        move |ctrl| announce_ublk_device(ctrl, announce_symlink.as_deref()),
    )?;

    if let Some(symlink_path) = device.symlink.as_deref() {
        if let Err(err) = remove_device_symlink(symlink_path) {
            warn!(
                "Failed to remove device symlink {}: {err}",
                symlink_path.display()
            );
        }
    }

    Ok(())
}

fn handle_ctrlc_shutdown(dev_id: u32, device_symlink: Option<&Path>) {
    if let Err(e) = UblkCtrl::new_simple(dev_id as i32).and_then(|c| c.del_dev()) {
        log::error!("Failed to delete ublk device (dev_id={dev_id}): {e}");
    }
    if let Some(symlink_path) = device_symlink {
        if let Err(err) = remove_device_symlink(symlink_path) {
            log::error!(
                "Failed to remove device symlink {}: {err}",
                symlink_path.display()
            );
        }
    }
}

fn configure_ublk_device(
    dev: &mut UblkDev,
    device_size: u64,
) -> std::result::Result<(), UblkError> {
    dev.set_default_params(device_size);
    Ok(())
}

fn announce_ublk_device(ctrl: &UblkCtrl, device_symlink: Option<&Path>) {
    let bdev_path = ctrl.get_bdev_path();

    // Only create the symlink once the device node exists, so a kernel-side
    // failure cannot leave a dangling symlink for callers to mkfs through.
    if let Err(err) = wait_for_path(Path::new(&bdev_path), DEVICE_NODE_TIMEOUT) {
        error!(
            "ublk block device node {bdev_path} did not appear: {err}. \
             Not creating device symlink; check `dmesg | grep -i ublk`."
        );
        return;
    }

    info!("ublk device is available at {}", bdev_path);
    if let Some(symlink_path) = device_symlink {
        if let Err(err) = create_device_symlink(Path::new(&bdev_path), symlink_path) {
            warn!(
                "Failed to create device symlink {} -> {}: {err}",
                symlink_path.display(),
                bdev_path
            );
        }
    }
}

/// Wait for a path to exist, polling until the timeout elapses.
fn wait_for_path(path: &Path, timeout: Duration) -> Result<()> {
    let start = Instant::now();
    loop {
        if path.exists() {
            return Ok(());
        }
        if start.elapsed() >= timeout {
            return Err(crate::ubiblk_error!(Timeout {
                description: format!(
                    "path {} did not appear within {}s",
                    path.display(),
                    timeout.as_secs()
                ),
            }));
        }
        std::thread::sleep(Duration::from_millis(50));
    }
}

#[error_context("Failed to create device symlink")]
fn create_device_symlink(target: &Path, link: &Path) -> Result<()> {
    if let Some(parent) = link.parent() {
        std::fs::create_dir_all(parent).context(format!(
            "Failed to create parent directory: {}",
            parent.display()
        ))?;
    }

    match std::fs::symlink_metadata(link) {
        Ok(_) => {
            warn!("{} already exists; removing it", link.display());
            std::fs::remove_file(link).context(format!(
                "Failed to remove existing path: {}",
                link.display()
            ))?;
        }
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
        Err(e) => {
            return Err(e).context(format!("Failed to read metadata for: {}", link.display()));
        }
    }

    std::os::unix::fs::symlink(target, link).context(format!(
        "Failed to create symlink: {} -> {}",
        link.display(),
        target.display()
    ))?;

    info!(
        "Created device symlink {} -> {}",
        link.display(),
        target.display()
    );

    Ok(())
}

#[error_context("Failed to remove device symlink")]
fn remove_device_symlink(link: &Path) -> Result<()> {
    match std::fs::symlink_metadata(link) {
        Ok(metadata) => {
            if !metadata.file_type().is_symlink() {
                warn!(
                    "{} exists but is not a symlink; leaving it in place",
                    link.display()
                );
                return Ok(());
            }
            std::fs::remove_file(link).context(format!(
                "Failed to remove device symlink: {}",
                link.display()
            ))?;
        }
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(()),
        Err(e) => {
            return Err(e).context(format!("Failed to read metadata for: {}", link.display()));
        }
    }

    info!("Removed device symlink {}", link.display());
    Ok(())
}

fn set_thread_name(name: &str) {
    #[cfg(target_os = "linux")]
    {
        use std::ffi::CString;
        match CString::new(name) {
            Ok(cname) => {
                if let Err(e) = nix::sys::prctl::set_name(&cname) {
                    error!("Failed to set thread name '{name}': {e}");
                }
            }
            Err(e) => {
                error!("Failed to set thread name '{name}': {e}");
            }
        }
    }
}

fn serve_ublk_queue(
    qid: u16,
    dev: &UblkDev,
    bdev: Box<dyn BlockDevice>,
    alignment: usize,
    io_tracker: IoTracker,
) {
    set_thread_name(&format!("ublk-q{qid}"));

    let io_channel = match bdev.create_channel() {
        Ok(channel) => channel,
        Err(err) => {
            error!("Failed to create IO channel: {err}");
            return;
        }
    };

    let max_io_bytes = dev.dev_info.max_io_buf_bytes as usize;
    let bufs = dev.alloc_queue_io_bufs();

    let queue = match UblkQueue::new(qid, dev) {
        Ok(queue) => {
            // Submit a unified fetch command so the kernel starts delivering IO
            // completions with our pre-registered buffers.
            match queue.submit_fetch_commands_unified(BufDescList::Slices(Some(bufs.as_ref()))) {
                Ok(queue) => queue,
                Err(err) => {
                    error!("Failed to submit fetch commands: {err}");
                    return;
                }
            }
        }
        Err(err) => {
            error!("Failed to create ublk queue: {err}");
            return;
        }
    };

    let mut handler = UblkIoHandler::new(
        alignment,
        max_io_bytes,
        io_channel,
        bufs,
        dev.dev_info.queue_depth as usize,
        io_tracker,
    );

    queue.wait_and_handle_io(move |q, tag, io| handler.handle(q, tag, io));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_device_symlink() {
        let tmp_dir = tempfile::tempdir().expect("Failed to create temp dir");
        let target = tmp_dir.path().join("ublk-target");
        let link = tmp_dir.path().join("ublk-symlink");

        create_device_symlink(&target, &link).expect("Failed to create device symlink");

        let symlink_target = std::fs::read_link(&link).expect("Failed to read symlink");
        assert_eq!(symlink_target, target);
    }

    #[test]
    fn test_create_device_symlink_existing() {
        let tmp_dir = tempfile::tempdir().expect("Failed to create temp dir");
        let target = tmp_dir.path().join("ublk-target");
        let link = tmp_dir.path().join("ublk-symlink");
        std::fs::write(&link, b"existing").expect("Failed to create existing file");
        create_device_symlink(&target, &link).expect("Failed to create device symlink");
        let symlink_target = std::fs::read_link(&link).expect("Failed to read symlink");
        assert_eq!(symlink_target, target);
    }

    #[test]
    fn test_remove_device_symlink() {
        let tmp_dir = tempfile::tempdir().expect("Failed to create temp dir");
        let link = tmp_dir.path().join("ublk-symlink");
        std::os::unix::fs::symlink("/dev/ublk-target", &link).expect("Failed to create symlink");
        remove_device_symlink(&link).expect("Failed to remove device symlink");
        assert!(!link.exists());
    }

    #[test]
    fn test_remove_device_symlink_not_found() {
        let tmp_dir = tempfile::tempdir().expect("Failed to create temp dir");
        let link = tmp_dir.path().join("nonexistent-symlink");
        // Should succeed silently when path doesn't exist
        remove_device_symlink(&link).expect("Should succeed for nonexistent path");
    }

    #[test]
    fn test_remove_device_symlink_not_a_symlink() {
        let tmp_dir = tempfile::tempdir().expect("Failed to create temp dir");
        let link = tmp_dir.path().join("regular-file");
        std::fs::write(&link, b"not a symlink").expect("Failed to create file");
        // Should succeed but leave the file in place
        remove_device_symlink(&link).expect("Should succeed for non-symlink");
        assert!(link.exists(), "Non-symlink file should be left in place");
    }

    #[test]
    fn test_wait_for_path_existing() {
        let tmp_dir = tempfile::tempdir().expect("Failed to create temp dir");
        wait_for_path(tmp_dir.path(), Duration::from_secs(1)).expect("existing path should be Ok");
    }

    #[test]
    fn test_wait_for_path_timeout() {
        let tmp_dir = tempfile::tempdir().expect("Failed to create temp dir");
        let missing = tmp_dir.path().join("missing");
        let result = wait_for_path(&missing, Duration::from_millis(100));
        assert!(result.is_err());
        assert!(result.err().unwrap().to_string().contains("did not appear"));
    }

    #[test]
    fn test_wait_for_path_appears_later() {
        let tmp_dir = tempfile::tempdir().expect("Failed to create temp dir");
        let path = tmp_dir.path().join("appears-later");
        let path_clone = path.clone();
        let writer = std::thread::spawn(move || {
            std::thread::sleep(Duration::from_millis(100));
            std::fs::write(&path_clone, b"ready").expect("Failed to create file");
        });
        wait_for_path(&path, Duration::from_secs(5)).expect("path should appear");
        writer.join().unwrap();
    }

    #[test]
    fn test_ublk_op_from_raw() {
        assert_eq!(
            UblkOp::from_raw(libublk::sys::UBLK_IO_OP_READ),
            UblkOp::Read
        );
        assert_eq!(
            UblkOp::from_raw(libublk::sys::UBLK_IO_OP_WRITE),
            UblkOp::Write
        );
        assert_eq!(
            UblkOp::from_raw(libublk::sys::UBLK_IO_OP_FLUSH),
            UblkOp::Flush
        );
        assert_eq!(UblkOp::from_raw(0xFF), UblkOp::Unsupported);
        assert_eq!(UblkOp::from_raw(u32::MAX), UblkOp::Unsupported);
    }

    #[test]
    fn test_create_device_symlink_nested_parent() {
        let tmp_dir = tempfile::tempdir().expect("Failed to create temp dir");
        let target = tmp_dir.path().join("ublk-target");
        let link = tmp_dir.path().join("a/b/c/ublk-symlink");
        create_device_symlink(&target, &link).expect("Failed to create device symlink");
        let symlink_target = std::fs::read_link(&link).expect("Failed to read symlink");
        assert_eq!(symlink_target, target);
    }

    #[test]
    fn test_create_device_symlink_replaces_existing_symlink() {
        let tmp_dir = tempfile::tempdir().expect("Failed to create temp dir");
        let target1 = tmp_dir.path().join("target1");
        let target2 = tmp_dir.path().join("target2");
        let link = tmp_dir.path().join("ublk-symlink");
        // Create initial symlink
        std::os::unix::fs::symlink(&target1, &link).expect("Failed to create symlink");
        // Replace with new target
        create_device_symlink(&target2, &link).expect("Failed to replace device symlink");
        let symlink_target = std::fs::read_link(&link).expect("Failed to read symlink");
        assert_eq!(symlink_target, target2);
    }

    #[test]
    fn test_set_thread_name_valid() {
        // Should not panic with a valid name
        set_thread_name("test-thread");
    }

    #[test]
    fn test_set_thread_name_with_nul() {
        // Name containing a null byte — CString::new will fail, but
        // set_thread_name should handle it gracefully (just log an error)
        set_thread_name("bad\0name");
    }

    #[test]
    fn test_ublk_io_request_fields() {
        let req = UblkIoRequest {
            op: UblkOp::Read,
            sector_offset: 100,
            sector_count: 8,
            request_id: 3,
            bytes: 4096,
        };
        assert_eq!(req.op, UblkOp::Read);
        assert_eq!(req.sector_offset, 100);
        assert_eq!(req.sector_count, 8);
        assert_eq!(req.request_id, 3);
        assert_eq!(req.bytes, 4096);
    }

    /// A thread that stopped without creating anything is not the kernel
    /// hanging, and saying it is sends whoever reads the log after the wrong
    /// thing entirely.
    #[test]
    fn a_device_thread_that_stops_is_not_reported_as_a_kernel_hang() {
        let (sender, receiver) = std::sync::mpsc::channel::<Result<u32>>();
        drop(sender);

        let err = await_device_creation(&receiver, Duration::from_secs(30))
            .expect_err("a thread that sent nothing has not created a device");

        assert!(
            !err.to_string().contains("UBLK_U_CMD_ADD_DEV"),
            "blamed the kernel for a thread that stopped: {err}"
        );
    }

    /// And the case the wait is actually for still reports what the kernel did
    /// not finish.
    #[test]
    fn a_kernel_that_never_finishes_creation_is_reported_as_such() {
        let (_sender, receiver) = std::sync::mpsc::channel::<Result<u32>>();
        let timeout = Duration::from_millis(200);

        // On another thread, so a wait that is no longer bounded fails this
        // test rather than hanging the run.
        let (done_sender, done) = std::sync::mpsc::channel();
        std::thread::spawn(move || {
            let outcome = await_device_creation(&receiver, timeout).map_err(|e| e.to_string());
            let _ = done_sender.send(outcome);
        });

        let err = done
            .recv_timeout(timeout * 20)
            .expect("the wait never gave up, so it is not bounded")
            .expect_err("a creation that never completes must not succeed");

        assert!(err.contains("UBLK_U_CMD_ADD_DEV"), "{err}");
    }
}
