use clap::Parser;
use log::{error, info};
use std::{
    fs::{File, OpenOptions},
    io::{BufRead, BufReader, Read, Seek, Write},
};
use ubiblk::utils::decode_hex;

fn first_difference<T: PartialEq>(a: &[T], b: &[T]) -> Option<usize> {
    a.iter().zip(b.iter()).position(|(x, y)| x != y)
}

#[derive(Parser)]
#[command(name = "replay-log", version, author, about = "Replay a log file.")]
struct Args {
    /// Path to the log file
    #[arg(short, long)]
    log: String,

    /// Disk path
    #[arg(short, long)]
    disk: String,
}

fn main() {
    let args = Args::parse();

    env_logger::init();

    let log_file = match File::open(&args.log) {
        Ok(file) => file,
        Err(e) => {
            error!("Error opening log file {}: {}", args.log, e);
            std::process::exit(1);
        }
    };

    let mut disk_file = match OpenOptions::new().read(true).write(true).open(&args.disk) {
        Ok(file) => file,
        Err(e) => {
            error!("Error opening disk file {}: {}", args.disk, e);
            std::process::exit(1);
        }
    };

    let reader = BufReader::new(log_file);
    let mut lines = reader.lines().enumerate().peekable();

    while let Some((line_num, Ok(line))) = lines.next() {
        let command = line.trim();

        let (_, sector) = lines.next().unwrap_or_else(|| {
            error!(
                "Error reading line {}: expected sector number",
                line_num + 1
            );
            std::process::exit(1);
        });
        let sector = sector.unwrap_or_else(|_| {
            error!(
                "Error reading line {}: expected sector number",
                line_num + 1
            );
            std::process::exit(1);
        });
        let sector: u64 = sector.trim().parse().unwrap_or_else(|_| {
            error!(
                "Error parsing sector number on line {}: {}",
                line_num + 1,
                sector
            );
            std::process::exit(1);
        });

        let (_, len) = lines.next().unwrap_or_else(|| {
            error!("Error reading line {}: expected length", line_num + 2);
            std::process::exit(1);
        });
        let len = len.unwrap_or_else(|_| {
            error!("Error reading line {}: expected length", line_num + 2);
            std::process::exit(1);
        });
        let len: usize = len.trim().parse().unwrap_or_else(|_| {
            error!("Error parsing length on line {}: {}", line_num + 2, len);
            std::process::exit(1);
        });

        let (_, data) = lines.next().unwrap_or_else(|| {
            error!("Error reading line {}: expected data", line_num + 3);
            std::process::exit(1);
        });
        let data = data.unwrap_or_else(|_| {
            error!("Error reading line {}: expected data", line_num + 3);
            std::process::exit(1);
        });
        let data = decode_hex(data.trim()).unwrap_or_else(|_| {
            error!("Error decoding hex data on line {}: {}", line_num + 3, data);
            std::process::exit(1);
        });
        if data.len() != len {
            error!(
                "Error: length mismatch on line {}: expected {}, got {}",
                line_num + 3,
                len,
                data.len()
            );
            std::process::exit(1);
        }

        let offset = sector * 512;
        info!(
            "[{}] {}: sector {}, len {}",
            line_num + 1,
            command,
            sector,
            len
        );

        if command == "WRITE" {
            if let Err(e) = disk_file.seek(std::io::SeekFrom::Start(offset)) {
                error!("Error seeking to offset {}: {}", offset, e);
                std::process::exit(1);
            }
            if let Err(e) = disk_file.write_all(&data) {
                error!("Error writing data to disk: {}", e);
                std::process::exit(1);
            }
        } else if command == "READ" {
            let mut buffer = vec![0; len];
            if let Err(e) = disk_file.seek(std::io::SeekFrom::Start(offset)) {
                error!("Error seeking to offset {}: {}", offset, e);
                std::process::exit(1);
            }
            if let Err(e) = disk_file.read_exact(&mut buffer) {
                error!("Error reading data from disk: {}", e);
                std::process::exit(1);
            }
            let first_diff = first_difference(&data, &buffer);
            if let Some(index) = first_diff {
                error!(
                    "Data mismatch on line {}: expected {:?}..., got {:?}... at index {}",
                    line_num + 1,
                    &buffer[index..std::cmp::min(index + 10, buffer.len())],
                    &data[index..std::cmp::min(index + 10, data.len())],
                    index
                );
            }
        } else {
            error!("Unknown command on line {}: {}", line_num + 1, command);
            std::process::exit(1);
        }
    }
}
