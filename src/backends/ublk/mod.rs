use libublk::{
    ctrl::{UblkCtrl, UblkCtrlBuilder},
    io::{BufDescList, UblkDev, UblkQueue},
    UblkError, UblkFlags,
};
use log::{error, info, warn};
use std::path::{Path, PathBuf};
use ubiblk_macros::error_context;

use crate::{
    backends::common::{io_tracking::IoTracker, run_backend_loop, BackendEnv, SECTOR_SIZE},
    block_device::BlockDevice,
    config::v2,
    Result, ResultExt,
};

mod io_handler;

use io_handler::UblkIoHandler;

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

    let ctrl = std::sync::Arc::new(
        UblkCtrlBuilder::default()
            .name(&device_name)
            .nr_queues(num_queues)
            .depth(queue_size)
            .io_buf_bytes(io_buf_bytes)
            // Add the device immediately so the backend can bind queues in run_target.
            .dev_flags(UblkFlags::UBLK_DEV_F_ADD_DEV)
            .build()?,
    );

    // Ensure the kernel device is torn down on Ctrl-C so we don't leave a stale
    // /dev/ublk* entry if the process exits without a clean shutdown.
    let ctrl_sig = ctrl.clone();
    let ctrl_symlink = device_symlink.clone();
    if let Err(e) = ctrlc::set_handler(move || {
        handle_ctrlc_shutdown(&ctrl_sig, ctrl_symlink.as_deref());
    }) {
        log::warn!("Failed to set Ctrl-C handler: {e}");
    }

    let io_trackers = backend_env.io_trackers().clone();
    let announce_symlink = device_symlink.clone();
    ctrl.run_target(
        move |dev| configure_ublk_device(dev, device_size),
        move |qid, dev| {
            let io_tracker = io_trackers[qid as usize].clone();
            serve_ublk_queue(qid, dev, bdev.clone(), backend_alignment, io_tracker)
        },
        move |ctrl| announce_ublk_device(ctrl, announce_symlink.as_deref()),
    )?;

    if let Some(symlink_path) = device_symlink.as_deref() {
        if let Err(err) = remove_device_symlink(symlink_path) {
            warn!(
                "Failed to remove device symlink {}: {err}",
                symlink_path.display()
            );
        }
    }

    Ok(())
}

fn handle_ctrlc_shutdown(ctrl: &UblkCtrl, device_symlink: Option<&Path>) {
    let dev_id = ctrl.dev_info().dev_id;
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
            Ok(cname) => unsafe {
                libc::prctl(libc::PR_SET_NAME, cname.as_ptr(), 0, 0, 0);
            },
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
    use crate::utils::umask_guard::UMASK_LOCK;

    #[test]
    fn test_create_device_symlink() {
        let _l = UMASK_LOCK.lock().unwrap();
        let tmp_dir = tempfile::tempdir().expect("Failed to create temp dir");
        let target = tmp_dir.path().join("ublk-target");
        let link = tmp_dir.path().join("ublk-symlink");

        create_device_symlink(&target, &link).expect("Failed to create device symlink");

        let symlink_target = std::fs::read_link(&link).expect("Failed to read symlink");
        assert_eq!(symlink_target, target);
    }

    #[test]
    fn test_create_device_symlink_existing() {
        let _l = UMASK_LOCK.lock().unwrap();
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
        let _l = UMASK_LOCK.lock().unwrap();
        let tmp_dir = tempfile::tempdir().expect("Failed to create temp dir");
        let link = tmp_dir.path().join("ublk-symlink");
        std::os::unix::fs::symlink("/dev/ublk-target", &link).expect("Failed to create symlink");
        remove_device_symlink(&link).expect("Failed to remove device symlink");
        assert!(!link.exists());
    }

    #[test]
    fn test_remove_device_symlink_not_found() {
        let _l = UMASK_LOCK.lock().unwrap();
        let tmp_dir = tempfile::tempdir().expect("Failed to create temp dir");
        let link = tmp_dir.path().join("nonexistent-symlink");
        // Should succeed silently when path doesn't exist
        remove_device_symlink(&link).expect("Should succeed for nonexistent path");
    }

    #[test]
    fn test_remove_device_symlink_not_a_symlink() {
        let _l = UMASK_LOCK.lock().unwrap();
        let tmp_dir = tempfile::tempdir().expect("Failed to create temp dir");
        let link = tmp_dir.path().join("regular-file");
        std::fs::write(&link, b"not a symlink").expect("Failed to create file");
        // Should succeed but leave the file in place
        remove_device_symlink(&link).expect("Should succeed for non-symlink");
        assert!(link.exists(), "Non-symlink file should be left in place");
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
        let _l = UMASK_LOCK.lock().unwrap();
        let tmp_dir = tempfile::tempdir().expect("Failed to create temp dir");
        let target = tmp_dir.path().join("ublk-target");
        let link = tmp_dir.path().join("a/b/c/ublk-symlink");
        create_device_symlink(&target, &link).expect("Failed to create device symlink");
        let symlink_target = std::fs::read_link(&link).expect("Failed to read symlink");
        assert_eq!(symlink_target, target);
    }

    #[test]
    fn test_create_device_symlink_replaces_existing_symlink() {
        let _l = UMASK_LOCK.lock().unwrap();
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
}
