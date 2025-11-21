use std::io::{self, ErrorKind, Read, Write};
use std::net::{SocketAddr, TcpStream};
use std::sync::Arc;

use log::{debug, error};

use super::{BlockDevice, IoChannel, SharedBuffer, UbiMetadata};
use crate::utils::tls;
use crate::vhost_backend::SECTOR_SIZE;
use crate::{Result, VhostUserBlockError};

use openssl::ssl::SslConnector;

trait ReadWrite: Read + Write {}
impl<T: Read + Write> ReadWrite for T {}

type RemoteStream = dyn ReadWrite + Send;

const METADATA_CMD: u8 = 0x00;
const READ_STRIPE_CMD: u8 = 0x01;
const STATUS_OK: u8 = 0x00;
const STATUS_INVALID_STRIPE: u8 = 0x01;
const STATUS_UNWRITTEN: u8 = 0x02;
const STRIPE_WRITTEN_MASK: u8 = 1 << 1;

#[derive(Clone)]
pub struct RemoteTlsConfig {
    connector: Arc<SslConnector>,
}

impl RemoteTlsConfig {
    pub fn new(identity: Vec<u8>, key: Vec<u8>) -> Result<Self> {
        let connector =
            tls::build_psk_connector(Arc::new(identity), Arc::new(key)).map_err(|err| {
                VhostUserBlockError::InvalidParameter {
                    description: format!("failed to configure TLS connector: {err}"),
                }
            })?;

        Ok(Self {
            connector: Arc::new(connector),
        })
    }

    fn connect(&self, addr: SocketAddr) -> io::Result<Box<RemoteStream>> {
        let stream = TcpStream::connect(addr)?;
        let stream = tls::connect_psk_stream(self.connector.as_ref(), stream)?;
        Ok(Box::new(stream))
    }
}

fn open_stream(addr: SocketAddr, tls: Option<&RemoteTlsConfig>) -> io::Result<Box<RemoteStream>> {
    match tls {
        Some(cfg) => cfg.connect(addr),
        None => {
            let stream = TcpStream::connect(addr)?;
            Ok(Box::new(stream))
        }
    }
}

fn read_metadata_bytes(stream: &mut dyn Read) -> io::Result<Vec<u8>> {
    debug!("Reading metadata from remote server");
    let mut len_buf = [0u8; 4];
    stream.read_exact(&mut len_buf)?;
    let metadata_len = u32::from_le_bytes(len_buf) as usize;
    debug!("Remote metadata length: {metadata_len} bytes");
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
    debug!("Read {} bytes of metadata", buf.len());
    Ok(buf)
}

fn fetch_metadata(stream: &mut dyn ReadWrite) -> io::Result<Vec<u8>> {
    stream.write_all(&[METADATA_CMD])?;
    read_metadata_bytes(stream)
}

fn parse_metadata(bytes: &[u8]) -> Result<Box<UbiMetadata>> {
    debug!("Parsing metadata");
    if bytes.len() < UbiMetadata::HEADER_SIZE {
        return Err(VhostUserBlockError::MetadataError {
            description: format!(
                "metadata buffer too small: {} < {}",
                bytes.len(),
                UbiMetadata::HEADER_SIZE
            ),
        });
    }

    let metadata = UbiMetadata::from_bytes(bytes);
    let expected_magic: [u8; 9] = *b"BDEV_UBI\0";
    if metadata.magic != expected_magic {
        return Err(VhostUserBlockError::MetadataError {
            description: "remote metadata magic does not match UBI header".to_string(),
        });
    }

    debug!("Parsed metadata: {metadata:?}");

    Ok(metadata)
}

pub struct RemoteBlockDevice {
    server_addr: SocketAddr,
    sector_count: u64,
    stripe_sector_count: u64,
    tls: Option<RemoteTlsConfig>,
}

impl RemoteBlockDevice {
    pub fn new(server_addr: String, tls: Option<RemoteTlsConfig>) -> Result<Box<Self>> {
        let socket_addr = server_addr.parse::<SocketAddr>().map_err(|err| {
            VhostUserBlockError::InvalidParameter {
                description: format!("invalid remote address {server_addr}: {err}"),
            }
        })?;

        let mut stream = open_stream(socket_addr, tls.as_ref())
            .map_err(|e| VhostUserBlockError::IoError { source: e })?;
        let metadata_bytes = fetch_metadata(stream.as_mut())
            .map_err(|e| VhostUserBlockError::IoError { source: e })?;
        let metadata = parse_metadata(&metadata_bytes)?;

        let stripe_sector_count = metadata.stripe_size();
        if stripe_sector_count == 0 {
            return Err(VhostUserBlockError::MetadataError {
                description: "remote metadata specifies zero stripe size".to_string(),
            });
        }
        let max_stripe_sectors = (usize::MAX / SECTOR_SIZE) as u64;
        if stripe_sector_count > max_stripe_sectors {
            return Err(VhostUserBlockError::MetadataError {
                description: format!(
                    "stripe size {stripe_sector_count} sectors is too large for host architecture"
                ),
            });
        }

        let stripe_count = metadata.stripe_count();
        let sector_count = stripe_sector_count
            .checked_mul(stripe_count)
            .ok_or_else(|| VhostUserBlockError::MetadataError {
                description: "overflow computing total sector count".to_string(),
            })?;

        Ok(Box::new(Self {
            server_addr: socket_addr,
            sector_count,
            stripe_sector_count,
            tls,
        }))
    }
}

impl BlockDevice for RemoteBlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>> {
        let channel =
            RemoteIoChannel::new(self.server_addr, self.stripe_sector_count, self.tls.clone())?;
        Ok(Box::new(channel))
    }

    fn sector_count(&self) -> u64 {
        self.sector_count
    }

    fn clone(&self) -> Box<dyn BlockDevice> {
        Box::new(Self {
            server_addr: self.server_addr,
            sector_count: self.sector_count,
            stripe_sector_count: self.stripe_sector_count,
            tls: self.tls.clone(),
        })
    }
}

struct RemoteIoChannel {
    stream: Box<RemoteStream>,
    metadata: Arc<UbiMetadata>,
    stripe_sector_count: u64,
    finished_requests: Vec<(usize, bool)>,
}

impl RemoteIoChannel {
    fn new(
        server_addr: SocketAddr,
        stripe_sector_count: u64,
        tls: Option<RemoteTlsConfig>,
    ) -> Result<Self> {
        let mut stream = open_stream(server_addr, tls.as_ref())
            .map_err(|e| VhostUserBlockError::IoChannelCreation { source: e })?;
        let metadata_bytes = fetch_metadata(stream.as_mut())
            .map_err(|e| VhostUserBlockError::IoChannelCreation { source: e })?;
        let remote_metadata = parse_metadata(&metadata_bytes)?;

        Ok(Self {
            stream,
            metadata: remote_metadata.into(),
            stripe_sector_count,
            finished_requests: Vec::new(),
        })
    }

    fn stripe_len_bytes(&self) -> usize {
        (self.stripe_sector_count as usize) * SECTOR_SIZE
    }

    fn fetch_stripe(&mut self, stripe_id: u64, dest: &mut [u8]) -> io::Result<()> {
        let mut request = [0u8; 9];
        request[0] = READ_STRIPE_CMD;
        request[1..].copy_from_slice(&stripe_id.to_le_bytes());
        self.stream.write_all(&request)?;

        let mut status = [0u8; 1];
        self.stream.read_exact(&mut status)?;
        match status[0] {
            STATUS_OK => self.stream.read_exact(dest),
            STATUS_INVALID_STRIPE => Err(io::Error::new(
                ErrorKind::InvalidData,
                format!("invalid stripe id {stripe_id}"),
            )),
            STATUS_UNWRITTEN => Err(io::Error::new(
                ErrorKind::InvalidData,
                format!("stripe {stripe_id} reported as unwritten by server"),
            )),
            other => Err(io::Error::other(format!(
                "unexpected server status 0x{other:02x} while fetching stripe {stripe_id}"
            ))),
        }
    }
}

impl IoChannel for RemoteIoChannel {
    fn stripe_has_data(&self, stripe_id: u64) -> bool {
        let stripe_id = stripe_id as usize;
        if stripe_id >= self.metadata.stripe_headers.len() {
            return false;
        }
        let header = self.metadata.stripe_headers[stripe_id];
        header & STRIPE_WRITTEN_MASK != 0
    }

    fn add_read(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        if self.stripe_sector_count == 0 {
            error!("Remote stripe size is zero");
            self.finished_requests.push((id, false));
            return;
        }

        if !sector_offset.is_multiple_of(self.stripe_sector_count) {
            error!("Read request {id} not aligned to stripe boundary: sector {sector_offset}");
            self.finished_requests.push((id, false));
            return;
        }

        if sector_count as u64 != self.stripe_sector_count {
            error!(
                "Read request {id} has length {} sectors but stripe size is {}",
                sector_count, self.stripe_sector_count
            );
            self.finished_requests.push((id, false));
            return;
        }

        let stripe_id = (sector_offset / self.stripe_sector_count) as usize;
        if stripe_id >= self.metadata.stripe_headers.len() {
            error!("Read request {id} targets out-of-range stripe {stripe_id}");
            self.finished_requests.push((id, false));
            return;
        }

        let stripe_len_bytes = self.stripe_len_bytes();
        let header = self.metadata.stripe_headers[stripe_id];
        if header & STRIPE_WRITTEN_MASK == 0 {
            let mut buf = buf.borrow_mut();
            let slice = buf.as_mut_slice();
            if slice.len() < stripe_len_bytes {
                error!(
                    "Buffer too small for request {id}: {} < {}",
                    slice.len(),
                    stripe_len_bytes
                );
                self.finished_requests.push((id, false));
                return;
            }
            slice[..stripe_len_bytes].fill(0);
            self.finished_requests.push((id, true));
            return;
        }

        let mut buf = buf.borrow_mut();
        let slice = buf.as_mut_slice();
        if slice.len() < stripe_len_bytes {
            error!(
                "Buffer too small for request {id}: {} < {}",
                slice.len(),
                stripe_len_bytes
            );
            self.finished_requests.push((id, false));
            return;
        }

        if let Err(e) = self.fetch_stripe(stripe_id as u64, &mut slice[..stripe_len_bytes]) {
            error!("Failed to fetch stripe {stripe_id}: {e}");
            self.finished_requests.push((id, false));
            return;
        }

        debug!("Fetched stripe {stripe_id} for request {id}");

        self.finished_requests.push((id, true));
    }

    fn add_write(
        &mut self,
        _sector_offset: u64,
        _sector_count: u32,
        _buf: SharedBuffer,
        id: usize,
    ) {
        error!("Write requested on read-only remote block device");
        self.finished_requests.push((id, false));
    }

    fn add_flush(&mut self, id: usize) {
        error!("Flush requested on read-only remote block device");
        self.finished_requests.push((id, false));
    }

    fn submit(&mut self) -> Result<()> {
        Ok(())
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        std::mem::take(&mut self.finished_requests)
    }

    fn busy(&self) -> bool {
        false
    }
}
