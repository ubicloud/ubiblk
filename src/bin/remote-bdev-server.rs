use std::error::Error;
use std::fs::File;
use std::io::{self, ErrorKind, Read, Seek, SeekFrom, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::path::PathBuf;
use std::sync::{Arc, Mutex};
use std::thread;

use clap::Parser;
use log::{error, info, warn};
use openssl::ssl::SslAcceptor;
use ubiblk::block_device::UbiMetadata;
use ubiblk::utils::tls;
use ubiblk::vhost_backend::SECTOR_SIZE;

trait ReadWrite: Read + Write {}
impl<T: Read + Write> ReadWrite for T {}

type DynStream = Box<dyn ReadWrite + Send>;

#[derive(Clone)]
struct TlsServerConfig {
    acceptor: Arc<SslAcceptor>,
}

impl TlsServerConfig {
    fn new(acceptor: SslAcceptor) -> Self {
        Self {
            acceptor: Arc::new(acceptor),
        }
    }

    fn accept(&self, stream: TcpStream) -> io::Result<DynStream> {
        let stream = tls::accept_psk_stream(self.acceptor.as_ref(), stream)?;
        Ok(Box::new(stream))
    }
}

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

    /// Enable TLS using the provided PSK identity when `--tls-psk-key` is set.
    #[arg(long, requires = "tls_psk_key")]
    tls_psk_identity: Option<String>,

    /// Path to a hex-encoded PSK shared with clients when `--tls-psk-identity` is set.
    #[arg(long, requires = "tls_psk_identity")]
    tls_psk_key: Option<PathBuf>,
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
    let Args {
        bind,
        metadata,
        image,
        tls_psk_identity,
        tls_psk_key,
    } = args;

    let metadata_bytes = std::fs::read(&metadata)?;
    if metadata_bytes.len() < UbiMetadata::HEADER_SIZE {
        return Err(format!("metadata file {} is too small", metadata.display()).into());
    }
    if metadata_bytes.len() > u32::MAX as usize {
        return Err(format!(
            "metadata file {} exceeds protocol limits",
            metadata.display()
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

    let image_file = File::open(&image)?;
    let image_len = image_file.metadata()?.len();
    let expected_len = stripe_len_bytes as u64 * metadata.stripe_count();
    if image_len < expected_len {
        warn!(
            "image file {} is smaller than the metadata implies ({} < {})",
            image.display(),
            image_len,
            expected_len
        );
    }
    let image = Arc::new(Mutex::new(image_file));

    let tls_config = match (tls_psk_identity.as_deref(), tls_psk_key.as_ref()) {
        (Some(identity), Some(key_path)) => {
            let identity_bytes = tls::prepare_psk_identity(identity)
                .map_err(|err| format!("invalid TLS PSK identity: {err}"))?;
            let key_bytes = tls::read_psk_key(key_path)
                .map_err(|err| format!("failed to read TLS PSK key: {err}"))?;
            let acceptor = tls::build_psk_acceptor(Arc::new(identity_bytes), Arc::new(key_bytes))
                .map_err(|err| format!("failed to configure TLS acceptor: {err}"))?;
            Some(TlsServerConfig::new(acceptor))
        }
        (None, None) => None,
        _ => {
            return Err(
                "TLS PSK identity and key must either both be provided or both omitted".into(),
            )
        }
    };

    let listener = TcpListener::bind(&bind)?;
    info!("listening on {}", listener.local_addr()?);

    loop {
        let (stream, addr) = listener.accept()?;
        info!("accepted connection from {addr}");
        let metadata_bytes = Arc::clone(&metadata_bytes);
        let metadata = Arc::clone(&metadata);
        let image = Arc::clone(&image);
        let tls_config = tls_config.clone();
        thread::spawn(move || {
            let result = (|| -> Result<(), Box<dyn Error>> {
                let stream = match wrap_stream(stream, tls_config.as_ref()) {
                    Ok(stream) => stream,
                    Err(err) => return Err(Box::new(err)),
                };
                handle_client(
                    stream,
                    addr,
                    metadata_bytes,
                    metadata,
                    image,
                    stripe_len_bytes,
                )
            })();
            match result {
                Ok(()) => info!("client {addr} disconnected"),
                Err(err) => error!("client {addr}: {err}"),
            }
        });
    }
}

fn wrap_stream(stream: TcpStream, tls: Option<&TlsServerConfig>) -> io::Result<DynStream> {
    match tls {
        Some(cfg) => cfg.accept(stream),
        None => Ok(Box::new(stream)),
    }
}

fn handle_client(
    mut stream: DynStream,
    peer: SocketAddr,
    metadata_bytes: Arc<Vec<u8>>,
    metadata: Arc<UbiMetadata>,
    image: Arc<Mutex<File>>,
    stripe_len_bytes: usize,
) -> Result<(), Box<dyn Error>> {
    info!("sending metadata to client {peer} ...");
    stream.write_all(&(metadata_bytes.len() as u32).to_le_bytes())?;
    stream.write_all(&metadata_bytes)?;
    info!("sent metadata to client {peer}");

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
                info!("client {peer} requests stripe {stripe_id}");
                if stripe_id > usize::MAX as u64 {
                    error!("client {peer} requests invalid stripe {stripe_id}");
                    stream.write_all(&[STATUS_INVALID_STRIPE])?;
                    continue;
                }
                let stripe_idx = stripe_id as usize;
                if stripe_idx >= metadata.stripe_headers.len() {
                    error!("client {peer} requests out-of-bounds stripe {stripe_id}");
                    stream.write_all(&[STATUS_INVALID_STRIPE])?;
                    continue;
                }
                let header = metadata.stripe_headers[stripe_idx];
                if header & STRIPE_WRITTEN_MASK == 0 {
                    info!("client {peer} requests unwritten stripe {stripe_id}");
                    stream.write_all(&[STATUS_UNWRITTEN])?;
                    continue;
                }

                match read_stripe(&image, stripe_idx, stripe_len_bytes) {
                    Ok(data) => {
                        stream.write_all(&[STATUS_OK])?;
                        stream.write_all(&data)?;
                        info!("served stripe {stripe_id} to client {peer}");
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
