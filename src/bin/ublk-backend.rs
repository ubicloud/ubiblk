use clap::Parser;
use log::error;
use std::cell::RefCell;
use std::fs::File;
use std::path::PathBuf;
use std::process;
use std::rc::Rc;
use std::sync::Arc;
use std::time::Duration;

use libublk::ctrl::UblkCtrlBuilder;
use libublk::io::{UblkDev, UblkIOCtx, UblkQueue};
use libublk::{UblkFlags, UblkIORes};

use ubiblk::block_device::{self, BlockDevice};
use ubiblk::utils::aligned_buffer::AlignedBuf;
use ubiblk::vhost_backend::Options;
use ubiblk::Result;

const UBLK_IO_OP_READ: u32 = 0;
const UBLK_IO_OP_WRITE: u32 = 1;
const UBLK_IO_OP_FLUSH: u32 = 2;

#[derive(Parser)]
#[command(
    name = "ublk-backend",
    version,
    author,
    about = "Launch a ublk block backend using a config file."
)]
struct Args {
    /// Path to the configuration YAML file.
    #[arg(short = 'f', long = "config")]
    config: String,
}

fn build_block_device(path: &str, options: &Options) -> Result<Box<dyn BlockDevice + Send + Sync>> {
    let block_device = block_device::UringBlockDevice::new(
        PathBuf::from(path),
        options.queue_size,
        false,
        options.direct_io,
        options.sync_io,
    )?;

    Ok(block_device)
}

fn main() {
    env_logger::builder().format_timestamp(None).init();
    let args = Args::parse();

    let file = match File::open(&args.config) {
        Ok(file) => file,
        Err(e) => {
            error!("Error opening config file {}: {}", args.config, e);
            process::exit(1);
        }
    };

    let options: Options = match serde_yaml::from_reader(file) {
        Ok(cfg) => cfg,
        Err(e) => {
            error!("Error parsing config file {}: {}", args.config, e);
            process::exit(1);
        }
    };

    if options.image_path.is_some() {
        error!("image_path is not supported in ublk-backend");
        process::exit(1);
    }

    if options.encryption_key.is_some() {
        error!("encryption_key is not supported in ublk-backend");
        process::exit(1);
    }

    let block_device: Arc<dyn BlockDevice + Send + Sync> =
        match build_block_device(&options.path, &options) {
            Ok(b) => Arc::from(b),
            Err(e) => {
                error!("Failed to create block device: {e:?}");
                process::exit(1);
            }
        };

    let size_bytes = block_device.sector_count() << 9;

    let ctrl = UblkCtrlBuilder::default()
        .name("ubiblk")
        .nr_queues(options.num_queues as u16)
        .depth(options.queue_size as u16)
        .io_buf_bytes(options.seg_size_max * options.seg_count_max)
        .dev_flags(UblkFlags::UBLK_DEV_F_ADD_DEV)
        .build()
        .unwrap_or_else(|e| {
            error!("Failed to build ublk ctrl: {e:?}");
            process::exit(1);
        });

    let tgt_init = move |dev: &mut UblkDev| {
        dev.set_default_params(size_bytes);
        Ok(())
    };

    let block_clone = block_device.clone();
    let q_handler = move |qid: u16, dev: &UblkDev| {
        let mut channel = block_clone.create_channel().expect("create_channel failed");
        let bufs_rc = Rc::new(dev.alloc_queue_io_bufs());
        let bufs = bufs_rc.clone();
        let io_handler = move |q: &UblkQueue, tag: u16, _io: &UblkIOCtx| {
            let iod = q.get_iod(tag);
            let sectors = iod.nr_sectors;
            let offset = iod.start_sector;
            let op = iod.op_flags & 0xff;
            let buf = &bufs[tag as usize];
            let bytes = (sectors << 9) as usize;
            match op {
                UBLK_IO_OP_READ => {
                    let data = Rc::new(RefCell::new(AlignedBuf::new(bytes)));
                    channel.add_read(offset, sectors, data.clone(), 0);
                    channel.submit().unwrap();
                    while channel.busy() {
                        channel.poll();
                        std::thread::sleep(Duration::from_millis(1));
                    }
                    let slice = data.borrow();
                    unsafe {
                        std::ptr::copy_nonoverlapping(slice.as_ptr(), buf.as_mut_ptr(), bytes);
                    }
                    q.complete_io_cmd(tag, buf.as_mut_ptr(), Ok(UblkIORes::Result(bytes as i32)));
                }
                UBLK_IO_OP_WRITE => {
                    let data = Rc::new(RefCell::new(AlignedBuf::new(bytes)));
                    {
                        let mut d = data.borrow_mut();
                        unsafe {
                            std::ptr::copy_nonoverlapping(buf.as_ptr(), d.as_mut_ptr(), bytes);
                        }
                    }
                    channel.add_write(offset, sectors, data.clone(), 0);
                    channel.submit().unwrap();
                    while channel.busy() {
                        channel.poll();
                        std::thread::sleep(Duration::from_millis(1));
                    }
                    q.complete_io_cmd(tag, buf.as_mut_ptr(), Ok(UblkIORes::Result(bytes as i32)));
                }
                UBLK_IO_OP_FLUSH => {
                    channel.add_flush(0);
                    channel.submit().unwrap();
                    while channel.busy() {
                        channel.poll();
                        std::thread::sleep(Duration::from_millis(1));
                    }
                    q.complete_io_cmd(tag, std::ptr::null_mut(), Ok(UblkIORes::Result(0)));
                }
                _ => {
                    q.complete_io_cmd(tag, buf.as_mut_ptr(), Ok(UblkIORes::Result(-libc::EINVAL)));
                }
            }
        };

        UblkQueue::new(qid, dev)
            .unwrap()
            .regiser_io_bufs(Some(&bufs_rc))
            .submit_fetch_commands(Some(&bufs_rc))
            .wait_and_handle_io(io_handler);
    };

    if let Err(e) = ctrl.run_target(tgt_init, q_handler, |_| {}) {
        error!("Failed to run ublk target: {e:?}");
        process::exit(1);
    }
}
