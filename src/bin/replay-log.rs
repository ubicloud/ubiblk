use clap::{Arg, Command};
use log::{error, info};
use std::{
    fs::{File, OpenOptions},
    io::{BufRead, BufReader, Read, Seek, Write},
};
use ubiblk::utils::decode_hex;

fn main() {
    let cmd_arguments = Command::new("replay-log")
        .version(env!("CARGO_PKG_VERSION"))
        .author(env!("CARGO_PKG_AUTHORS"))
        .about("Replay a log file.")
        .arg(
            Arg::new("log")
                .short('l')
                .long("log")
                .required(true)
                .help("Path to the log file."),
        )
        .arg(
            Arg::new("disk")
                .short('d')
                .long("disk")
                .required(true)
                .help("Disk path."),
        )
        .get_matches();

    env_logger::init();

    let log_path = cmd_arguments.get_one::<String>("log").unwrap();
    let disk_path = cmd_arguments.get_one::<String>("disk").unwrap();
    let log_file = match File::open(log_path) {
        Ok(file) => file,
        Err(e) => {
            error!("Error opening log file {}: {}", log_path, e);
            std::process::exit(1);
        }
    };

    let mut disk_file = match OpenOptions::new().read(true).write(true).open(disk_path) {
        Ok(file) => file,
        Err(e) => {
            error!("Error opening disk file {}: {}", disk_path, e);
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
            if buffer != data {
                error!(
                    "Data mismatch on line {}: expected {:?}..., got {:?}...",
                    line_num + 1,
                    &data[..10],
                    &buffer[..10]
                );
                std::process::exit(1);
            }
        } else {
            error!("Unknown command on line {}: {}", line_num + 1, command);
            std::process::exit(1);
        }
    }

    println!("Replay completed successfully.");
}
