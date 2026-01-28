use libublk::{
    ctrl::{UblkCtrl, UblkCtrlBuilder},
    io::{BufDescList, UblkDev, UblkQueue},
    UblkError, UblkFlags,
};
use log::{error, info};

use crate::{
    backends::common::{run_backend_loop, BackendEnv, SECTOR_SIZE},
    block_device::BlockDevice,
    config::DeviceConfig,
    Result,
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

pub fn ublk_backend_loop(config: &DeviceConfig) -> Result<()> {
    run_backend_loop(config, "ublk", false, serve_ublk)
}

fn serve_ublk(backend_env: &BackendEnv) -> Result<()> {
    info!("Creating ublk backend ...");

    let bdev = backend_env.bdev();
    let device_size = bdev.sector_count() * SECTOR_SIZE as u64;
    let device_name = format!("ubiblk-{}", backend_env.config().device_id);
    let backend_alignment = backend_env.alignment();

    let config = backend_env.config();
    let num_queues = config.num_queues as u16;
    let queue_size = config.queue_size as u16;
    let io_buf_bytes = config.seg_size_max;

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
    if let Err(e) = ctrlc::set_handler(move || handle_ctrlc_shutdown(&ctrl_sig)) {
        log::warn!("Failed to set Ctrl-C handler: {e}");
    }

    ctrl.run_target(
        move |dev| configure_ublk_device(dev, device_size),
        move |qid, dev| serve_ublk_queue(qid, dev, bdev.clone(), backend_alignment),
        announce_ublk_device,
    )?;

    Ok(())
}

fn handle_ctrlc_shutdown(ctrl: &UblkCtrl) {
    let dev_id = ctrl.dev_info().dev_id;
    if let Err(e) = UblkCtrl::new_simple(dev_id as i32).and_then(|c| c.del_dev()) {
        log::error!("Failed to delete ublk device (dev_id={dev_id}): {e}");
    }
}

fn configure_ublk_device(
    dev: &mut UblkDev,
    device_size: u64,
) -> std::result::Result<(), UblkError> {
    dev.set_default_params(device_size);
    Ok(())
}

fn announce_ublk_device(ctrl: &UblkCtrl) {
    info!("ublk device is available at {}", ctrl.get_bdev_path());
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

fn serve_ublk_queue(qid: u16, dev: &UblkDev, bdev: Box<dyn BlockDevice>, alignment: usize) {
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
    );

    queue.wait_and_handle_io(move |q, tag, io| handler.handle(q, tag, io));
}
