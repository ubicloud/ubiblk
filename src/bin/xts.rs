use std::{
    fs::{File, OpenOptions},
    io::{BufWriter, Read, Seek, SeekFrom, Write},
    path::PathBuf,
    time::Duration,
};

use clap::{Parser, ValueEnum};
use log::error;

use ubiblk::{
    backends::SECTOR_SIZE,
    block_device::{self, shared_buffer, wait_for_completion, BlockDevice},
    config::v2,
    Result,
};

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
    /// Path to the configuration TOML file
    #[arg(short = 'f', long = "config")]
    config: String,

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

fn decode(args: &Args, key1: Vec<u8>, key2: Vec<u8>) -> Result<()> {
    let base_device: Box<dyn BlockDevice> =
        block_device::SyncBlockDevice::new(PathBuf::from(&args.input), true, false, false)?;

    let crypt_device = block_device::CryptBlockDevice::new(base_device, key1, key2)?;

    let total_sectors = crypt_device.sector_count();
    let start_sector = args.start_sector.unwrap_or(0);
    if start_sector >= total_sectors {
        return Err(ubiblk::ubiblk_error!(InvalidParameter {
            description: format!(
                "Start sector {start_sector} is out of range (device has {total_sectors} sectors)",
            ),
        }));
    }

    let max_available = total_sectors - start_sector;
    let sectors_to_process = match args.sector_count {
        Some(len) => {
            if len == 0 {
                0
            } else if len > max_available {
                return Err(ubiblk::ubiblk_error!(InvalidParameter {
                    description: format!(
                        "Requested length {len} exceeds available sectors ({max_available})",
                    ),
                }));
            } else {
                len
            }
        }
        None => max_available,
    };

    let output_file = OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .open(&args.output)?;
    let mut writer = BufWriter::new(output_file);

    let mut channel = crypt_device.create_channel()?;

    let mut remaining = sectors_to_process;
    let mut current_sector = start_sector;
    let request_id = 0usize;

    while remaining > 0 {
        let chunk_sectors = std::cmp::min(remaining, MAX_CHUNK_SECTORS as u64) as u32;
        let chunk_bytes = chunk_sectors as usize * SECTOR_SIZE;
        let buffer = shared_buffer(chunk_bytes);

        channel.add_read(current_sector, chunk_sectors, buffer.clone(), request_id);
        channel.submit()?;

        wait_for_completion(channel.as_mut(), request_id, Duration::from_secs(30))?;

        let data = buffer.borrow();
        writer.write_all(&data.as_slice()[..chunk_bytes])?;

        current_sector += chunk_sectors as u64;
        remaining -= chunk_sectors as u64;
    }

    writer.flush()?;

    Ok(())
}

fn encode(args: &Args, key1: Vec<u8>, key2: Vec<u8>) -> Result<()> {
    let mut input_file = File::open(&args.input)?;

    let input_metadata = input_file.metadata()?;

    let input_len = input_metadata.len();
    if input_len % SECTOR_SIZE as u64 != 0 {
        return Err(ubiblk::ubiblk_error!(InvalidParameter {
            description: format!("Input file size {input_len} is not a multiple of sector size",),
        }));
    }

    let total_sectors = input_len / SECTOR_SIZE as u64;
    let start_sector = args.start_sector.unwrap_or(0);
    if start_sector >= total_sectors {
        return Err(ubiblk::ubiblk_error!(InvalidParameter {
            description: format!(
                "Start sector {start_sector} is out of range (input has {total_sectors} sectors)",
            ),
        }));
    }

    let max_available = total_sectors - start_sector;
    let sectors_to_process = match args.sector_count {
        Some(len) => {
            if len == 0 {
                0
            } else if len > max_available {
                return Err(ubiblk::ubiblk_error!(InvalidParameter {
                    description: format!(
                        "Requested length {len} exceeds available sectors ({max_available})",
                    ),
                }));
            } else {
                len
            }
        }
        None => max_available,
    };

    let target_size = sectors_to_process * SECTOR_SIZE as u64;
    let output_file = OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .open(&args.output)?;
    output_file.set_len(target_size)?;

    let base_device: Box<dyn BlockDevice> =
        block_device::SyncBlockDevice::new(PathBuf::from(&args.output), false, false, false)?;

    let crypt_device = block_device::CryptBlockDevice::new(base_device, key1, key2)?;

    input_file.seek(SeekFrom::Start(start_sector * SECTOR_SIZE as u64))?;

    let mut channel = crypt_device.create_channel()?;

    let mut remaining = sectors_to_process;
    let mut current_sector = start_sector;
    let request_id = 0usize;

    while remaining > 0 {
        let chunk_sectors = std::cmp::min(remaining, MAX_CHUNK_SECTORS as u64) as u32;
        let chunk_bytes = chunk_sectors as usize * SECTOR_SIZE;
        let buffer = shared_buffer(chunk_bytes);

        {
            let mut data = buffer.borrow_mut();
            input_file.read_exact(&mut data.as_mut_slice()[..chunk_bytes])?;
        }

        channel.add_write(current_sector, chunk_sectors, buffer.clone(), request_id);
        channel.submit()?;

        wait_for_completion(channel.as_mut(), request_id, Duration::from_secs(30))?;

        current_sector += chunk_sectors as u64;
        remaining -= chunk_sectors as u64;
    }

    Ok(())
}

fn main() {
    env_logger::builder().format_timestamp(None).init();

    if let Err(err) = run() {
        error!("{err}");
        std::process::exit(1);
    }
}

fn run() -> Result<()> {
    let args = Args::parse();
    let config = v2::Config::load(&PathBuf::from(&args.config))?;

    let encryption = config.encryption.as_ref().ok_or_else(|| {
        ubiblk::ubiblk_error!(InvalidParameter {
            description: "Configuration does not contain encryption keys".to_string(),
        })
    })?;
    let xts_key = config
        .secrets
        .get(encryption.xts_key.id())
        .ok_or_else(|| {
            ubiblk::ubiblk_error!(InvalidParameter {
                description: format!("Encryption secret '{}' not found", encryption.xts_key.id()),
            })
        })?
        .as_bytes();
    let (key1, key2) = (xts_key[..32].to_vec(), xts_key[32..].to_vec());

    match args.action {
        Action::Decode => decode(&args, key1, key2),
        Action::Encode => encode(&args, key1, key2),
    }
}
