use std::error::Error;
use std::fs::File;
use std::io::{self, ErrorKind, Read, Seek, SeekFrom, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::path::PathBuf;
use std::sync::{Arc, Mutex};
use std::thread;

use clap::Parser;
use log::{error, info, warn};
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
    name = "remote-bdev-server",
    about = "Sample remote block device server"
)]
struct Args {
    /// Address to listen on, e.g. 127.0.0.1:4555.
    #[arg(long, default_value = "127.0.0.1:4555")]
    bind: String,

    /// Path to the metadata file produced by `UbiMetadata::write_to_buf`.
    #[arg(long)]
    metadata: PathBuf,

    /// Path to the backing image whose stripes are served to clients.
    #[arg(long)]
    image: PathBuf,
}

fn main() {
    env_logger::builder().format_timestamp(None).init();

    let args = Args::parse();

    if let Err(err) = run(args) {
        error!("{err}");
        std::process::exit(1);
    }
}

fn run(args: Args) -> Result<(), Box<dyn Error>> {
    let metadata_bytes = std::fs::read(&args.metadata)?;
    if metadata_bytes.len() < UbiMetadata::HEADER_SIZE {
        return Err(format!("metadata file {} is too small", args.metadata.display()).into());
    }
    if metadata_bytes.len() > u32::MAX as usize {
        return Err(format!(
            "metadata file {} exceeds protocol limits",
            args.metadata.display()
        )
        .into());
    }

    let metadata = UbiMetadata::from_bytes(&metadata_bytes);
    let stripe_sector_count = metadata.stripe_size();
    if stripe_sector_count == 0 {
        return Err("metadata describes zero-sized stripes".into());
    }
    let max_stripe_sectors = (usize::MAX / SECTOR_SIZE) as u64;
    if stripe_sector_count > max_stripe_sectors {
        return Err("stripe size is too large for this platform".into());
    }
    let stripe_len_bytes = (stripe_sector_count as usize) * SECTOR_SIZE;

    let metadata: Arc<UbiMetadata> = Arc::from(metadata);
    let metadata_bytes = Arc::new(metadata_bytes);

    let image_file = File::open(&args.image)?;
    let image_len = image_file.metadata()?.len();
    let expected_len = stripe_len_bytes as u64 * metadata.stripe_count();
    if image_len < expected_len {
        warn!(
            "image file {} is smaller than the metadata implies ({} < {})",
            args.image.display(),
            image_len,
            expected_len
        );
    }
    let image = Arc::new(Mutex::new(image_file));

    let listener = TcpListener::bind(&args.bind)?;
    info!("listening on {}", listener.local_addr()?);

    loop {
        let (stream, addr) = listener.accept()?;
        info!("accepted connection from {addr}");
        let metadata_bytes = Arc::clone(&metadata_bytes);
        let metadata = Arc::clone(&metadata);
        let image = Arc::clone(&image);
        thread::spawn(move || {
            match handle_client(
                stream,
                addr,
                metadata_bytes,
                metadata,
                image,
                stripe_len_bytes,
            ) {
                Ok(()) => info!("client {addr} disconnected"),
                Err(err) => error!("client {addr}: {err}"),
            }
        });
    }
}

fn handle_client(
    mut stream: TcpStream,
    peer: SocketAddr,
    metadata_bytes: Arc<Vec<u8>>,
    metadata: Arc<UbiMetadata>,
    image: Arc<Mutex<File>>,
    stripe_len_bytes: usize,
) -> Result<(), Box<dyn Error>> {
    stream.write_all(&(metadata_bytes.len() as u32).to_le_bytes())?;
    stream.write_all(&metadata_bytes)?;

    loop {
        let mut request = [0u8; 9];
        match stream.read_exact(&mut request) {
            Ok(()) => {}
            Err(err) => match err.kind() {
                ErrorKind::Interrupted => continue,
                ErrorKind::UnexpectedEof | ErrorKind::ConnectionReset => return Ok(()),
                _ => return Err(err.into()),
            },
        }

        match request[0] {
            READ_STRIPE_CMD => {
                let mut stripe_bytes = [0u8; 8];
                stripe_bytes.copy_from_slice(&request[1..]);
                let stripe_id = u64::from_le_bytes(stripe_bytes);
                if stripe_id > usize::MAX as u64 {
                    stream.write_all(&[STATUS_INVALID_STRIPE])?;
                    continue;
                }
                let stripe_idx = stripe_id as usize;
                if stripe_idx >= metadata.stripe_headers.len() {
                    stream.write_all(&[STATUS_INVALID_STRIPE])?;
                    continue;
                }
                let header = metadata.stripe_headers[stripe_idx];
                if header & STRIPE_WRITTEN_MASK == 0 {
                    stream.write_all(&[STATUS_UNWRITTEN])?;
                    continue;
                }

                match read_stripe(&image, stripe_idx, stripe_len_bytes) {
                    Ok(data) => {
                        stream.write_all(&[STATUS_OK])?;
                        stream.write_all(&data)?;
                    }
                    Err(err) => {
                        error!("client {peer} failed to read stripe {stripe_idx}: {err}");
                        stream.write_all(&[STATUS_SERVER_ERROR])?;
                    }
                }
            }
            other => {
                error!("client {peer} sent unsupported opcode 0x{other:02x}");
                stream.write_all(&[STATUS_SERVER_ERROR])?;
                return Err(format!("unsupported opcode 0x{other:02x}").into());
            }
        }
    }
}

fn read_stripe(
    image: &Arc<Mutex<File>>,
    stripe_idx: usize,
    stripe_len_bytes: usize,
) -> io::Result<Vec<u8>> {
    let mut buf = vec![0u8; stripe_len_bytes];
    let mut file = image
        .lock()
        .map_err(|_| io::Error::other("image file lock poisoned"))?;
    let offset = stripe_idx as u64 * stripe_len_bytes as u64;
    file.seek(SeekFrom::Start(offset))?;
    file.read_exact(&mut buf)?;
    Ok(buf)
}
