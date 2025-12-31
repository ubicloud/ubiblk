use clap::Parser;
use log::info;
use std::{
    fs::{File, OpenOptions},
    io::{BufRead, BufReader, Lines, Read, Seek, Write},
    iter::{Enumerate, Peekable},
};
use ubiblk::{utils::decode_hex, vhost_backend::SECTOR_SIZE, Error, Result};

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

fn main() -> Result<()> {
    let args = Args::parse();

    env_logger::init();

    let log_file = File::open(&args.log)?;

    let mut disk_file = OpenOptions::new().read(true).write(true).open(&args.disk)?;

    let reader = BufReader::new(log_file);
    let mut lines = reader.lines().enumerate().peekable();

    while let Some((line_num, line)) = lines.next() {
        let line = line?;
        let command = line.trim();

        let sector_line = read_required_line(&mut lines, line_num + 2, "sector number")?;
        let sector: u64 = sector_line
            .trim()
            .parse()
            .map_err(|_| Error::InvalidParameter {
                description: format!(
                    "Error parsing sector number on line {}: {}",
                    line_num + 2,
                    sector_line
                ),
            })?;

        let len_line = read_required_line(&mut lines, line_num + 3, "length")?;
        let len: usize = len_line
            .trim()
            .parse()
            .map_err(|_| Error::InvalidParameter {
                description: format!("Error parsing length on line {}: {len_line}", line_num + 3),
            })?;

        let data_line = read_required_line(&mut lines, line_num + 4, "data")?;
        let data = decode_hex(data_line.trim()).map_err(|_| Error::InvalidParameter {
            description: format!(
                "Error decoding hex data on line {}: {data_line}",
                line_num + 4
            ),
        })?;
        if data.len() != len {
            return Err(Error::InvalidParameter {
                description: format!(
                    "Error: length mismatch on line {}: expected {}, got {}",
                    line_num + 4,
                    len,
                    data.len()
                ),
            });
        }

        let offset = sector * SECTOR_SIZE as u64;
        info!(
            "[{}] {}: sector {}, len {}",
            line_num + 1,
            command,
            sector,
            len
        );

        if command == "WRITE" {
            disk_file.seek(std::io::SeekFrom::Start(offset))?;
            disk_file.write_all(&data)?;
        } else if command == "READ" {
            let mut buffer = vec![0; len];
            disk_file.seek(std::io::SeekFrom::Start(offset))?;
            disk_file.read_exact(&mut buffer)?;
            if let Some(index) = first_difference(&data, &buffer) {
                return Err(Error::ProtocolError {
                    description: format!(
                        "Data mismatch on line {}: expected {:?}..., got {:?}... at index {}",
                        line_num + 1,
                        &buffer[index..std::cmp::min(index + 10, buffer.len())],
                        &data[index..std::cmp::min(index + 10, data.len())],
                        index
                    ),
                });
            }
        } else {
            return Err(Error::InvalidParameter {
                description: format!("Unknown command on line {}: {command}", line_num + 1),
            });
        }
    }

    Ok(())
}

fn read_required_line<R: BufRead>(
    lines: &mut Peekable<Enumerate<Lines<R>>>,
    line_num: usize,
    expectation: &str,
) -> Result<String> {
    let (_, line) = lines.next().ok_or_else(|| Error::InvalidParameter {
        description: format!("Error reading line {line_num}: expected {expectation}"),
    })?;
    line.map_err(|_| Error::InvalidParameter {
        description: format!("Error reading line {line_num}: expected {expectation}"),
    })
}
