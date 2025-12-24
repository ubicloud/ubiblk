use clap::{Parser, ValueEnum};
use log::error;
use std::cell::RefCell;
use std::fs::{File, OpenOptions};
use std::io::{BufWriter, Read, Seek, SeekFrom, Write};
use std::path::PathBuf;
use std::process;
use std::rc::Rc;
use std::thread;
use std::time::Duration;
use ubiblk::block_device::{self, BlockDevice};
use ubiblk::utils::aligned_buffer::AlignedBuf;
use ubiblk::vhost_backend::{Options, SECTOR_SIZE};
use ubiblk::KeyEncryptionCipher;

const MAX_CHUNK_SECTORS: u32 = 1024;

#[derive(Copy, Clone, Debug, Eq, PartialEq, ValueEnum)]
enum Action {
    Encode,
    Decode,
}

#[derive(Parser)]
#[command(
    name = "xts",
    version,
    author,
    about = "Encode or decode an AES-XTS encrypted image"
)]
struct Args {
    /// Path to the configuration YAML file
    #[arg(short = 'f', long = "config")]
    config: String,

    /// Path to the key encryption key file
    #[arg(short = 'k', long = "kek")]
    kek: Option<String>,

    /// Starting sector offset
    #[arg(long = "start")]
    start_sector: Option<u64>,

    /// Number of sectors to process
    #[arg(long = "len")]
    sector_count: Option<u64>,

    /// Whether to encode or decode the image
    #[arg(long = "action", value_enum, default_value_t = Action::Decode)]
    action: Action,

    /// Input file
    input: String,

    /// Output file
    output: String,
}

fn load_kek(path: &str) -> Option<KeyEncryptionCipher> {
    let file = match File::open(path) {
        Ok(f) => f,
        Err(e) => {
            error!("Error opening KEK file {path}: {e}");
            return None;
        }
    };

    match serde_yaml::from_reader(file) {
        Ok(kek) => Some(kek),
        Err(e) => {
            error!("Error parsing KEK file {path}: {e}");
            None
        }
    }
}

fn wait_for_completion(channel: &mut dyn block_device::IoChannel, request_id: usize) -> bool {
    loop {
        let events = channel.poll();
        for (id, result) in events {
            if id == request_id {
                return result;
            }
        }

        if !channel.busy() {
            thread::sleep(Duration::from_millis(10));
        }
    }
}

fn decode(args: &Args, key1: Vec<u8>, key2: Vec<u8>, kek: KeyEncryptionCipher) {
    let base_device: Box<dyn BlockDevice> =
        block_device::SyncBlockDevice::new(PathBuf::from(&args.input), true, false, false)
            .unwrap_or_else(|e| {
                error!("Failed to open input file {}: {e}", args.input);
                process::exit(1);
            });

    let crypt_device = match block_device::CryptBlockDevice::new(base_device, key1, key2, kek) {
        Ok(dev) => dev,
        Err(e) => {
            error!("Failed to create crypt device: {e}");
            process::exit(1);
        }
    };

    let total_sectors = crypt_device.sector_count();
    let start_sector = args.start_sector.unwrap_or(0);
    if start_sector >= total_sectors {
        error!("Start sector {start_sector} is out of range (device has {total_sectors} sectors)");
        process::exit(1);
    }

    let max_available = total_sectors - start_sector;
    let sectors_to_process = match args.sector_count {
        Some(len) => {
            if len == 0 {
                0
            } else if len > max_available {
                error!("Requested length {len} exceeds available sectors ({max_available})");
                process::exit(1);
            } else {
                len
            }
        }
        None => max_available,
    };

    let output_file = match OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .open(&args.output)
    {
        Ok(f) => f,
        Err(e) => {
            error!("Failed to open output file {}: {}", args.output, e);
            process::exit(1);
        }
    };
    let mut writer = BufWriter::new(output_file);

    let mut channel = match crypt_device.create_channel() {
        Ok(chan) => chan,
        Err(e) => {
            error!("Failed to create IO channel: {e}");
            process::exit(1);
        }
    };

    let mut remaining = sectors_to_process;
    let mut current_sector = start_sector;
    let request_id = 0usize;

    while remaining > 0 {
        let chunk_sectors = std::cmp::min(remaining, MAX_CHUNK_SECTORS as u64) as u32;
        let chunk_bytes = chunk_sectors as usize * SECTOR_SIZE;
        let buffer = Rc::new(RefCell::new(AlignedBuf::new(chunk_bytes)));

        channel.add_read(current_sector, chunk_sectors, buffer.clone(), request_id);
        if let Err(e) = channel.submit() {
            error!("Failed to submit read request: {e}");
            process::exit(1);
        }

        if !wait_for_completion(channel.as_mut(), request_id) {
            error!("Read request failed at sector {current_sector}");
            process::exit(1);
        }

        let data = buffer.borrow();
        if let Err(e) = writer.write_all(&data.as_slice()[..chunk_bytes]) {
            error!("Failed to write decrypted data: {e}");
            process::exit(1);
        }

        current_sector += chunk_sectors as u64;
        remaining -= chunk_sectors as u64;
    }

    if let Err(e) = writer.flush() {
        error!("Failed to flush output file: {e}");
        process::exit(1);
    }
}

fn encode(args: &Args, key1: Vec<u8>, key2: Vec<u8>, kek: KeyEncryptionCipher) {
    let mut input_file = match File::open(&args.input) {
        Ok(f) => f,
        Err(e) => {
            error!("Failed to open input file {}: {}", args.input, e);
            process::exit(1);
        }
    };

    let input_metadata = match input_file.metadata() {
        Ok(meta) => meta,
        Err(e) => {
            error!(
                "Failed to get metadata for input file {}: {}",
                args.input, e
            );
            process::exit(1);
        }
    };

    let input_len = input_metadata.len();
    if input_len % SECTOR_SIZE as u64 != 0 {
        error!(
            "Input file size {} is not a multiple of sector size",
            input_len
        );
        process::exit(1);
    }

    let total_sectors = input_len / SECTOR_SIZE as u64;
    let start_sector = args.start_sector.unwrap_or(0);
    if start_sector >= total_sectors {
        error!("Start sector {start_sector} is out of range (input has {total_sectors} sectors)");
        process::exit(1);
    }

    let max_available = total_sectors - start_sector;
    let sectors_to_process = match args.sector_count {
        Some(len) => {
            if len == 0 {
                0
            } else if len > max_available {
                error!("Requested length {len} exceeds available sectors ({max_available})");
                process::exit(1);
            } else {
                len
            }
        }
        None => max_available,
    };

    let target_size = sectors_to_process * SECTOR_SIZE as u64;
    match OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .open(&args.output)
    {
        Ok(f) => {
            if let Err(e) = f.set_len(target_size) {
                error!("Failed to resize output file {}: {}", args.output, e);
                process::exit(1);
            }
        }
        Err(e) => {
            error!("Failed to prepare output file {}: {}", args.output, e);
            process::exit(1);
        }
    }

    let base_device: Box<dyn BlockDevice> =
        block_device::SyncBlockDevice::new(PathBuf::from(&args.output), false, false, false)
            .unwrap_or_else(|e| {
                error!("Failed to open output file {}: {e}", args.output);
                process::exit(1);
            });

    let crypt_device = match block_device::CryptBlockDevice::new(base_device, key1, key2, kek) {
        Ok(dev) => dev,
        Err(e) => {
            error!("Failed to create crypt device: {e}");
            process::exit(1);
        }
    };

    if let Err(e) = input_file.seek(SeekFrom::Start(start_sector * SECTOR_SIZE as u64)) {
        error!("Failed to seek input file to sector {start_sector}: {e}");
        process::exit(1);
    }

    let mut channel = match crypt_device.create_channel() {
        Ok(chan) => chan,
        Err(e) => {
            error!("Failed to create IO channel: {e}");
            process::exit(1);
        }
    };

    let mut remaining = sectors_to_process;
    let mut current_sector = start_sector;
    let request_id = 0usize;

    while remaining > 0 {
        let chunk_sectors = std::cmp::min(remaining, MAX_CHUNK_SECTORS as u64) as u32;
        let chunk_bytes = chunk_sectors as usize * SECTOR_SIZE;
        let buffer = Rc::new(RefCell::new(AlignedBuf::new(chunk_bytes)));

        {
            let mut data = buffer.borrow_mut();
            if let Err(e) = input_file.read_exact(&mut data.as_mut_slice()[..chunk_bytes]) {
                error!("Failed to read plaintext data: {e}");
                process::exit(1);
            }
        }

        channel.add_write(current_sector, chunk_sectors, buffer.clone(), request_id);
        if let Err(e) = channel.submit() {
            error!("Failed to submit write request: {e}");
            process::exit(1);
        }

        if !wait_for_completion(channel.as_mut(), request_id) {
            error!("Write request failed at sector {current_sector}");
            process::exit(1);
        }

        current_sector += chunk_sectors as u64;
        remaining -= chunk_sectors as u64;
    }
}

fn main() {
    env_logger::builder().format_timestamp(None).init();

    let args = Args::parse();

    let config_file = match File::open(&args.config) {
        Ok(f) => f,
        Err(e) => {
            error!("Error opening config file {}: {}", args.config, e);
            process::exit(1);
        }
    };

    let options: Options = match serde_yaml::from_reader(config_file) {
        Ok(cfg) => cfg,
        Err(e) => {
            error!("Error parsing config file {}: {}", args.config, e);
            process::exit(1);
        }
    };

    let (key1, key2) = match options.encryption_key.clone() {
        Some(keys) => keys,
        None => {
            error!("Configuration does not contain encryption keys");
            process::exit(1);
        }
    };

    let mut kek = KeyEncryptionCipher::default();
    if let Some(kek_path) = &args.kek {
        kek = match load_kek(kek_path) {
            Some(k) => k,
            None => process::exit(1),
        };
    }

    match args.action {
        Action::Decode => decode(&args, key1, key2, kek),
        Action::Encode => encode(&args, key1, key2, kek),
    }
}
