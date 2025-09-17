use std::collections::HashMap;
use std::io::{self, BufRead, ErrorKind, Read, Write};
use std::net::TcpStream;
use std::num::TryFromIntError;

use clap::Parser;
use ubiblk::block_device::UbiMetadata;
use ubiblk::vhost_backend::SECTOR_SIZE;

const READ_STRIPE_CMD: u8 = 0x01;
const STATUS_OK: u8 = 0x00;
const STATUS_INVALID_STRIPE: u8 = 0x01;
const STATUS_UNWRITTEN: u8 = 0x02;
const STATUS_SERVER_ERROR: u8 = 0xFF;
const STRIPE_WRITTEN_MASK: u8 = 1 << 1;

#[derive(Parser)]
#[command(
    name = "remote-shell",
    about = "Interactive shell for remote-bdev-server"
)]
struct Args {
    /// Address of the remote-bdev-server, e.g. 127.0.0.1:4555
    #[arg(value_name = "IP:PORT")]
    server: String,
}

fn main() -> io::Result<()> {
    let args = Args::parse();

    let mut stream = TcpStream::connect(&args.server)?;
    let metadata_bytes = read_metadata(&mut stream)?;
    let metadata = parse_metadata(&metadata_bytes)?;

    let stripe_len_bytes = stripe_len_bytes(&metadata)?;

    let stdin = io::stdin();
    let mut stdin_lock = stdin.lock();
    let mut stdout = io::stdout();
    let mut line = String::new();
    let mut fetched_stripes: HashMap<u64, Vec<u8>> = HashMap::new();

    loop {
        write!(stdout, "> ")?;
        stdout.flush()?;

        line.clear();
        let bytes = stdin_lock.read_line(&mut line)?;
        if bytes == 0 {
            break;
        }

        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }

        let mut parts = trimmed.split_whitespace();
        let cmd = parts.next().unwrap();

        match cmd {
            "exit" | "quit" => break,
            "stripe_header" => match parse_usize(parts.next()) {
                Ok(stripe_idx) => {
                    if stripe_idx >= metadata.stripe_headers.len() {
                        println!("INVALID_STRIPE");
                        continue;
                    }
                    let header = metadata.stripe_headers[stripe_idx];
                    let status = if header & STRIPE_WRITTEN_MASK != 0 {
                        "WRITTEN"
                    } else {
                        "NOT_WRITTEN"
                    };
                    println!("0x{header:02x} {status}");
                }
                Err(err) => println!("{err}"),
            },
            "fetch_stripe" => match parse_u64(parts.next()) {
                Ok(stripe_idx) => {
                    if stripe_idx as usize >= metadata.stripe_headers.len() {
                        println!("INVALID_STRIPE");
                        continue;
                    }

                    match fetch_stripe(&mut stream, stripe_idx, stripe_len_bytes) {
                        Ok(data) => {
                            fetched_stripes.insert(stripe_idx, data);
                            println!("FETCHED");
                        }
                        Err(err) => println!("{err}"),
                    }
                }
                Err(err) => println!("{err}"),
            },
            "dump_stripe" => match (
                parse_u64(parts.next()),
                parse_usize(parts.next()),
                parse_usize(parts.next()),
            ) {
                (Ok(stripe_idx), Ok(offset), Ok(len)) => {
                    if let Some(data) = fetched_stripes.get(&stripe_idx) {
                        if offset.saturating_add(len) > data.len() {
                            println!("INVALID_RANGE");
                            continue;
                        }
                        let end = offset + len;
                        let hex = hex::encode(&data[offset..end]);
                        println!("{hex}");
                    } else {
                        println!("NOT_FETCHED_FROM_REMOTE");
                    }
                }
                (Err(err), _, _) | (_, Err(err), _) | (_, _, Err(err)) => println!("{err}"),
            },
            other => {
                println!("UNKNOWN_COMMAND: {other}");
            }
        }
    }

    Ok(())
}

fn parse_usize(input: Option<&str>) -> Result<usize, String> {
    input
        .ok_or_else(|| "MISSING_ARGUMENT".to_string())
        .and_then(|value| {
            value
                .parse::<usize>()
                .map_err(|_| format!("INVALID_NUMBER: {value}"))
        })
}

fn parse_u64(input: Option<&str>) -> Result<u64, String> {
    input
        .ok_or_else(|| "MISSING_ARGUMENT".to_string())
        .and_then(|value| {
            value
                .parse::<u64>()
                .map_err(|_| format!("INVALID_NUMBER: {value}"))
        })
}

fn read_metadata(stream: &mut TcpStream) -> io::Result<Vec<u8>> {
    let mut len_buf = [0u8; 4];
    stream.read_exact(&mut len_buf)?;
    let metadata_len = u32::from_le_bytes(len_buf) as usize;
    if metadata_len < UbiMetadata::HEADER_SIZE {
        return Err(io::Error::new(
            ErrorKind::InvalidData,
            format!(
                "metadata too small: {metadata_len} < {}",
                UbiMetadata::HEADER_SIZE
            ),
        ));
    }
    let mut buf = vec![0u8; metadata_len];
    stream.read_exact(&mut buf)?;
    Ok(buf)
}

fn parse_metadata(bytes: &[u8]) -> io::Result<Box<UbiMetadata>> {
    if bytes.len() < UbiMetadata::HEADER_SIZE {
        return Err(io::Error::new(
            ErrorKind::InvalidData,
            format!(
                "metadata too small: {} < {}",
                bytes.len(),
                UbiMetadata::HEADER_SIZE
            ),
        ));
    }
    Ok(UbiMetadata::from_bytes(bytes))
}

fn stripe_len_bytes(metadata: &UbiMetadata) -> io::Result<usize> {
    let stripe_sector_count = metadata.stripe_size();
    if stripe_sector_count == 0 {
        return Err(io::Error::new(
            ErrorKind::InvalidData,
            "metadata describes zero-sized stripes",
        ));
    }

    let bytes = stripe_sector_count
        .checked_mul(SECTOR_SIZE as u64)
        .ok_or_else(|| io::Error::new(ErrorKind::InvalidData, "stripe size overflow"))?;

    usize::try_from(bytes).map_err(|err: TryFromIntError| {
        io::Error::new(ErrorKind::InvalidData, format!("stripe too large: {err}"))
    })
}

fn fetch_stripe(
    stream: &mut TcpStream,
    stripe_idx: u64,
    stripe_len: usize,
) -> Result<Vec<u8>, String> {
    let mut request = [0u8; 9];
    request[0] = READ_STRIPE_CMD;
    request[1..].copy_from_slice(&stripe_idx.to_le_bytes());
    if let Err(err) = stream.write_all(&request) {
        return Err(format!("IO_ERROR: {err}"));
    }

    let mut status = [0u8; 1];
    if let Err(err) = stream.read_exact(&mut status) {
        return Err(format!("IO_ERROR: {err}"));
    }

    match status[0] {
        STATUS_OK => {
            let mut buf = vec![0u8; stripe_len];
            if let Err(err) = stream.read_exact(&mut buf) {
                return Err(format!("IO_ERROR: {err}"));
            }
            Ok(buf)
        }
        STATUS_INVALID_STRIPE => Err("INVALID_STRIPE".to_string()),
        STATUS_UNWRITTEN => Err("NOT_WRITTEN".to_string()),
        STATUS_SERVER_ERROR => Err("SERVER_ERROR".to_string()),
        other => Err(format!("UNKNOWN_STATUS: 0x{other:02x}")),
    }
}
