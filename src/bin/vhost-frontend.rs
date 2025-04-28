use clap::{Arg, Command};
use std::str::FromStr;
use std::sync::atomic::{fence, Ordering};
use std::{
    fs::File,
    io::Write,
    os::fd::AsRawFd,
    path::{Path, PathBuf},
};
use ubiblk::utils::{
    block::{print_features, VirtioBlockConfig},
    memory::allocate_hugepage_memory,
};
use vhost::{
    vhost_user::{
        message::{VhostUserConfigFlags, VhostUserHeaderFlag, VHOST_USER_CONFIG_OFFSET},
        Frontend, VhostUserFrontend,
    },
    VhostBackend, VhostUserMemoryRegionInfo, VringConfigData,
};
use virtio_bindings::{
    bindings::virtio_ring::{vring_avail, vring_desc, vring_used, VRING_DESC_F_NEXT},
    virtio_blk::virtio_blk_outhdr,
    virtio_ring::VRING_DESC_F_WRITE,
};
use vmm_sys_util::eventfd::EventFd;

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq)]
enum Stage {
    Setup = 0,
    ConfigRead = 1,
    MemoryAllocation = 2,
    VirtqueueSetup = 3,
    DeviceCopy = 4,
}

impl FromStr for Stage {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "0" | "setup" => Ok(Stage::Setup),
            "1" | "config" => Ok(Stage::ConfigRead),
            "2" | "memory" => Ok(Stage::MemoryAllocation),
            "3" | "virtqueue" => Ok(Stage::VirtqueueSetup),
            "4" | "copy" => Ok(Stage::DeviceCopy),
            _ => Err(format!("Unknown stage: {}", s)),
        }
    }
}

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let matches = Command::new("vhost-frontend")
        .about("A vhost-user-blk frontend")
        .arg(
            Arg::new("socket")
                .short('s')
                .long("socket")
                .help("Path to the vhost-user socket")
                .required(true),
        )
        .arg(
            Arg::new("output")
                .short('o')
                .long("output")
                .help("Path to the output file")
                .required(false),
        )
        .arg(
            Arg::new("stage")
                .long("stage")
                .help("Execution stage (0-4 or name: setup, config, memory, virtqueue, copy)")
                .default_value("4"),
        )
        .get_matches();

    let socket = matches.get_one::<String>("socket").unwrap();
    let socket_path = PathBuf::from(socket);

    let stage = matches
        .get_one::<String>("stage")
        .map(|s| Stage::from_str(s))
        .unwrap_or(Ok(Stage::DeviceCopy))?;

    let output = matches.get_one::<String>("output");
    if stage == Stage::DeviceCopy && output.is_none() {
        return Err("Output file is required for stage 4".into());
    }

    println!("Running in stage: {:?} ({})", stage, stage as u8);

    let mut frontend = setup_frontend(&socket_path)?;

    if stage == Stage::Setup {
        return Ok(());
    }

    println!("Getting config");
    let cfg = get_config(&mut frontend)?;
    let capacity_sectors = cfg.capacity;
    let num_queues = cfg.num_queues;
    let capacity_bytes = capacity_sectors * 512;
    println!("Config: {:?}", cfg);
    println!("Device capacity: {} MiB", capacity_bytes / 1024 / 1024);
    println!("Number of queues: {}", num_queues);

    if stage == Stage::ConfigRead {
        return Ok(());
    }

    println!("Allocating memory");
    let (file, mem, size) = allocate_hugepage_memory()?;

    println!("Setting up memory table");
    setup_mem_table(&frontend, &file, mem, size)?;

    if stage == Stage::MemoryAllocation {
        return Ok(());
    }

    // setup virtqueues
    let (desc, avail, used, header, data, status) = setup_pointers(&mem)?;

    let vring_conf_data = VringConfigData {
        queue_max_size: 16,
        queue_size: 16,
        flags: 0,
        desc_table_addr: desc.as_ptr() as u64,
        used_ring_addr: used as *const _ as u64,
        avail_ring_addr: avail as *const _ as u64,
        log_addr: None,
    };
    println!("set_vring_num");
    frontend.set_vring_num(0, 16)?;
    println!("set_vring_addr");
    frontend.set_vring_addr(0, &vring_conf_data)?;
    println!("set_vring_base");
    frontend.set_vring_base(0, 0)?;

    let kickfd = EventFd::new(libc::EFD_NONBLOCK | libc::EFD_CLOEXEC)?;
    let callfd = EventFd::new(libc::EFD_NONBLOCK | libc::EFD_CLOEXEC)?;
    println!("set_vring_kick");
    frontend.set_vring_kick(0, &kickfd)?;
    println!("set_vring_call");
    frontend.set_vring_call(0, &callfd)?;

    println!("set_vring_enable");
    frontend.set_vring_enable(0, true)?;

    if stage == Stage::VirtqueueSetup {
        return Ok(());
    }

    println!("Copying device to file");

    let output_path = PathBuf::from(output.unwrap());
    let output_file = File::create(output_path)?;

    copy_device_to_file(
        desc,
        avail,
        used,
        header,
        data,
        status,
        &kickfd,
        &callfd,
        capacity_bytes,
        output_file,
    )?;

    Ok(())
}

fn setup_frontend(socket: &Path) -> Result<Frontend, Box<dyn std::error::Error>> {
    println!("Connecting to frontend: {:?}", socket);
    let mut frontend = Frontend::connect(socket, 1)?;

    println!("Setting Owner");
    frontend.set_hdr_flags(VhostUserHeaderFlag::empty());
    frontend.set_owner()?;

    println!("Getting features");
    frontend.set_hdr_flags(VhostUserHeaderFlag::NEED_REPLY);
    let features = frontend.get_features()?;
    print_features(features);

    println!("Setting features");
    frontend.set_hdr_flags(VhostUserHeaderFlag::empty());
    frontend.set_features(features)?;

    println!("Getting protocol features");
    frontend.set_hdr_flags(VhostUserHeaderFlag::NEED_REPLY);
    let proto = frontend.get_protocol_features()?;
    println!("Protocol features: {:?}", proto);

    println!("Setting protocol features");
    frontend.set_hdr_flags(VhostUserHeaderFlag::empty());
    frontend.set_protocol_features(proto)?;

    println!("Finished setup_frontend");

    Ok(frontend)
}

fn get_config(frontend: &mut Frontend) -> Result<VirtioBlockConfig, Box<dyn std::error::Error>> {
    let input_buf = [0u8; std::mem::size_of::<VirtioBlockConfig>()];
    frontend.set_hdr_flags(VhostUserHeaderFlag::NEED_REPLY);
    let (_cfg, data) = frontend.get_config(
        VHOST_USER_CONFIG_OFFSET,
        input_buf.len() as u32,
        VhostUserConfigFlags::WRITABLE,
        &input_buf,
    )?;

    // deserialize data
    let output_buf: &[u8] = data.as_ref();
    let cfg: VirtioBlockConfig = bincode::deserialize(output_buf).unwrap();
    Ok(cfg)
}

fn setup_mem_table(
    frontend: &Frontend,
    file: &File,
    mem: *mut u8,
    size: usize,
) -> Result<(), Box<dyn std::error::Error>> {
    let regions = [VhostUserMemoryRegionInfo {
        guest_phys_addr: 0,
        memory_size: size as u64,
        userspace_addr: mem as u64,
        mmap_offset: 0,
        mmap_handle: file.as_raw_fd(),
    }];
    frontend.set_mem_table(&regions)?;
    Ok(())
}

fn setup_pointers<'a>(
    mem: &*mut u8,
) -> Result<
    (
        &'a mut [vring_desc],
        &'a mut vring_avail,
        &'a mut vring_used,
        &'a mut virtio_blk_outhdr,
        &'a mut [u8],
        &'a mut u8,
    ),
    &'static str,
> {
    unsafe {
        let base_ptr = *mem;

        // Set up descriptor table (assuming space for 3 descriptors)
        let desc = std::slice::from_raw_parts_mut(base_ptr as *mut vring_desc, 3);

        // Initialize descriptors
        desc[0] = vring_desc {
            addr: 1024,
            len: std::mem::size_of::<virtio_blk_outhdr>() as u32,
            flags: VRING_DESC_F_NEXT as u16,
            next: 1,
        };

        desc[1] = vring_desc {
            addr: 2048,
            len: 4096,
            flags: (VRING_DESC_F_NEXT | VRING_DESC_F_WRITE) as u16,
            next: 2,
        };

        desc[2] = vring_desc {
            addr: 6144,
            len: 1,
            flags: VRING_DESC_F_WRITE as u16,
            next: 0,
        };

        // Create references to the memory regions
        let avail = &mut *(base_ptr.add(256) as *mut vring_avail);
        let used = &mut *(base_ptr.add(512) as *mut vring_used);
        let header = &mut *(base_ptr.add(1024) as *mut virtio_blk_outhdr);
        let data = std::slice::from_raw_parts_mut(base_ptr.add(2048), 4096);
        let status = &mut *base_ptr.add(6144);

        Ok((desc, avail, used, header, data, status))
    }
}

pub fn copy_device_to_file(
    desc: &mut [vring_desc],
    avail: &mut vring_avail,
    used: &mut vring_used,
    header: &mut virtio_blk_outhdr,
    data_buffer: &mut [u8],
    status: &mut u8,
    kickfd: &EventFd,
    _callfd: &EventFd,
    capacity_bytes: u64,
    mut output_file: File,
) -> Result<(), Box<dyn std::error::Error>> {
    let block_size = 4096;
    let num_blocks = capacity_bytes / block_size;
    let sectors_per_block = block_size / 512;

    // Initialize the flags and index
    avail.flags = 0;
    avail.idx = 0;
    used.flags = 0;
    used.idx = 0;

    for current_block in 0..num_blocks {
        let sector = current_block * sectors_per_block;
        let remaining = capacity_bytes - (current_block * block_size);
        let len = if remaining < block_size {
            remaining as u32
        } else {
            block_size as u32
        };

        // Set up the request header
        header.type_ = virtio_bindings::virtio_blk::VIRTIO_BLK_T_IN;
        header.ioprio = 0;
        header.sector = sector;

        // Configure the descriptor
        if desc.len() > 1 {
            desc[1].len = len;
        } else {
            return Err("Descriptor array too small".into());
        }

        // Initialize status byte
        *status = 0xF8;

        // Add to available ring
        // Access the first element of the ring using raw pointer dereference
        unsafe {
            let ring_ptr = avail.ring.as_ptr() as *mut u16;
            if !ring_ptr.is_null() {
                *ring_ptr = 0;
            } else {
                return Err("Available ring is empty".into());
            }
        }
        avail.idx += 1;

        // Memory fence to ensure visibility of changes
        fence(Ordering::SeqCst);

        // Signal the device
        println!("Signaling device");
        kickfd.write(1)?;

        // Wait for the device to process the request
        println!("Waiting for device");
        while *status == 0xF8 {
            fence(Ordering::SeqCst);
        }

        fence(Ordering::SeqCst);

        println!("Device processed request");
        // Write the buffer to the output file
        let data_to_write = &data_buffer[..len as usize];
        output_file.write_all(data_to_write)?;
        output_file.flush()?;
        println!("Wrote {} bytes to output file", len);

        // Reset used ring
        used.idx = 0;

        // Report progress
        let progress = (current_block as f64 / num_blocks as f64) * 100.0;
        print!("\rProgress: {:.2}%", progress);
    }

    println!("\rProgress: Done!     ");
    println!();
    Ok(())
}
