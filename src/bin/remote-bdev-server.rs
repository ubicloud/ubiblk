use std::cell::RefCell;
use std::error::Error;
use std::fs::File;
use std::io::{self, ErrorKind, Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::Arc;
use std::thread;
use std::time::Duration;

use clap::Parser;
use log::{error, info, warn};
use openssl::ssl::SslAcceptor;
use ubiblk::block_device::{load_metadata, BlockDevice, IoChannel, UbiMetadata};
use ubiblk::utils::{aligned_buffer::AlignedBuf, tls};
use ubiblk::vhost_backend::{build_block_device, KeyEncryptionCipher, Options, SECTOR_SIZE};

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

const METADATA_CMD: u8 = 0x00;
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

    /// Path to the configuration YAML file used to describe the block device.
    #[arg(short = 'f', long = "config")]
    config: PathBuf,

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
        config,
        tls_psk_identity,
        tls_psk_key,
    } = args;

    let options = load_options(&config)?;
    if options.image_path.is_some() {
        return Err("config must not specify image_path when used with remote-bdev-server".into());
    }

    let metadata_path = options
        .metadata_path
        .as_ref()
        .ok_or_else(|| "config is missing metadata_path".to_string())?;

    let server_state = prepare_server_state(&options, metadata_path)?;

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
        let server_state = Arc::clone(&server_state);
        let tls_config = tls_config.clone();
        thread::spawn(move || {
            let result = (|| -> Result<(), Box<dyn Error>> {
                let stream = match wrap_stream(stream, tls_config.as_ref()) {
                    Ok(stream) => stream,
                    Err(err) => return Err(Box::new(err)),
                };
                handle_client(stream, addr, server_state)
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
    state: Arc<ServerState>,
) -> Result<(), Box<dyn Error>> {
    let mut stripe_channel = state
        .stripe_device
        .create_channel()
        .map_err(into_boxed_error)?;

    loop {
        let mut opcode = [0u8; 1];
        match stream.read_exact(&mut opcode) {
            Ok(()) => {}
            Err(err) => match err.kind() {
                ErrorKind::Interrupted => continue,
                ErrorKind::UnexpectedEof | ErrorKind::ConnectionReset => return Ok(()),
                _ => return Err(err.into()),
            },
        }

        match opcode[0] {
            METADATA_CMD => {
                info!("client {peer} requested metadata");
                stream.write_all(&(state.metadata_bytes.len() as u32).to_le_bytes())?;
                stream.write_all(state.metadata_bytes.as_slice())?;
                info!("sent metadata to client {peer}");
            }
            READ_STRIPE_CMD => {
                let mut stripe_bytes = [0u8; 8];
                loop {
                    match stream.read_exact(&mut stripe_bytes) {
                        Ok(()) => break,
                        Err(err) => match err.kind() {
                            ErrorKind::Interrupted => continue,
                            ErrorKind::UnexpectedEof | ErrorKind::ConnectionReset => return Ok(()),
                            _ => return Err(err.into()),
                        },
                    }
                }
                let stripe_id = u64::from_le_bytes(stripe_bytes);
                info!("client {peer} requests stripe {stripe_id}");
                if stripe_id > usize::MAX as u64 {
                    error!("client {peer} requests invalid stripe {stripe_id}");
                    stream.write_all(&[STATUS_INVALID_STRIPE])?;
                    continue;
                }
                let stripe_idx = stripe_id as usize;
                if stripe_idx >= state.metadata.stripe_headers.len() {
                    error!("client {peer} requests out-of-bounds stripe {stripe_id}");
                    stream.write_all(&[STATUS_INVALID_STRIPE])?;
                    continue;
                }
                let header = state.metadata.stripe_headers[stripe_idx];
                if header & STRIPE_WRITTEN_MASK == 0 {
                    info!("client {peer} requests unwritten stripe {stripe_id}");
                    stream.write_all(&[STATUS_UNWRITTEN])?;
                    continue;
                }

                match read_stripe(
                    stripe_channel.as_mut(),
                    stripe_idx,
                    state.stripe_sector_count,
                    state.stripe_len_bytes,
                ) {
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

fn load_options(config: &PathBuf) -> Result<Options, Box<dyn Error>> {
    let file = File::open(config).map_err(|err| {
        Box::<dyn Error>::from(io::Error::new(
            err.kind(),
            format!("failed to open config file {}: {err}", config.display()),
        ))
    })?;

    serde_yaml::from_reader(file).map_err(|err| {
        Box::<dyn Error>::from(io::Error::new(
            ErrorKind::InvalidData,
            format!("failed to parse config file {}: {err}", config.display()),
        ))
    })
}

fn prepare_server_state(
    options: &Options,
    metadata_path: &str,
) -> Result<Arc<ServerState>, Box<dyn Error>> {
    let kek = KeyEncryptionCipher::default();

    let stripe_device =
        build_block_device(&options.path, options, kek.clone()).map_err(into_boxed_error)?;
    let stripe_device: Arc<dyn BlockDevice> = Arc::from(stripe_device);

    let metadata_device =
        build_block_device(metadata_path, options, kek).map_err(into_boxed_error)?;
    let mut metadata_channel = metadata_device.create_channel().map_err(into_boxed_error)?;
    let metadata = load_metadata(&mut metadata_channel, metadata_device.sector_count())
        .map_err(into_boxed_error)?;
    let metadata: Arc<UbiMetadata> = Arc::from(metadata);

    let metadata_len = metadata.metadata_size();
    if metadata_len < UbiMetadata::HEADER_SIZE {
        return Err("metadata is too small".into());
    }
    if metadata_len > u32::MAX as usize {
        return Err("metadata exceeds protocol limits".into());
    }

    let mut metadata_bytes = vec![0u8; metadata_len];
    metadata.write_to_buf(&mut metadata_bytes);

    let stripe_sector_count = metadata.stripe_size();
    if stripe_sector_count == 0 {
        return Err("metadata describes zero-sized stripes".into());
    }
    if stripe_sector_count > (usize::MAX / SECTOR_SIZE) as u64 {
        return Err("stripe size is too large for this platform".into());
    }
    let stripe_sector_count_u32 =
        u32::try_from(stripe_sector_count).map_err(|_| "stripe size exceeds IO channel limits")?;
    let stripe_len_bytes = stripe_sector_count_u32 as usize * SECTOR_SIZE;

    let available_bytes = stripe_device.sector_count() * SECTOR_SIZE as u64;
    let expected_bytes = (stripe_len_bytes as u64)
        .checked_mul(metadata.stripe_count())
        .ok_or_else(|| "metadata describes too many stripes".to_string())?;
    if available_bytes < expected_bytes {
        warn!(
            "data file {} is smaller than the metadata implies ({} < {})",
            options.path, available_bytes, expected_bytes
        );
    }

    Ok(Arc::new(ServerState {
        metadata_bytes,
        metadata,
        stripe_device,
        stripe_sector_count: stripe_sector_count_u32,
        stripe_len_bytes,
    }))
}

fn read_stripe(
    channel: &mut dyn IoChannel,
    stripe_idx: usize,
    stripe_sector_count: u32,
    stripe_len_bytes: usize,
) -> Result<Vec<u8>, Box<dyn Error>> {
    let offset = stripe_idx as u64 * u64::from(stripe_sector_count);
    let buffer = Rc::new(RefCell::new(AlignedBuf::new(stripe_len_bytes)));
    channel.add_read(offset, stripe_sector_count, buffer.clone(), 0);
    channel.submit().map_err(into_boxed_error)?;
    wait_for_completion(channel, 0)?;
    let data = buffer.borrow();
    Ok(data.as_slice()[..stripe_len_bytes].to_vec())
}

fn wait_for_completion(
    channel: &mut dyn IoChannel,
    request_id: usize,
) -> Result<(), Box<dyn Error>> {
    loop {
        for (id, success) in channel.poll() {
            if id == request_id {
                if success {
                    return Ok(());
                }
                return Err(Box::new(io::Error::other("I/O request failed")));
            }
        }

        if !channel.busy() {
            thread::sleep(Duration::from_millis(1));
        }
    }
}

fn into_boxed_error<E>(err: E) -> Box<dyn Error>
where
    E: Error + 'static,
{
    Box::new(err)
}

struct ServerState {
    metadata_bytes: Vec<u8>,
    metadata: Arc<UbiMetadata>,
    stripe_device: Arc<dyn BlockDevice>,
    stripe_sector_count: u32,
    stripe_len_bytes: usize,
}
