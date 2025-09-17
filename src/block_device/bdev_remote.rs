use std::io::{self, ErrorKind, Read, Write};
use std::net::TcpStream;
use std::sync::Arc;

use log::error;

use super::{BlockDevice, IoChannel, SharedBuffer, UbiMetadata};
use crate::vhost_backend::SECTOR_SIZE;
use crate::{Result, VhostUserBlockError};

const READ_STRIPE_CMD: u8 = 0x01;
const STATUS_OK: u8 = 0x00;
const STATUS_INVALID_STRIPE: u8 = 0x01;
const STATUS_UNWRITTEN: u8 = 0x02;
const STRIPE_WRITTEN_MASK: u8 = 1 << 1;

fn read_metadata_bytes(stream: &mut TcpStream) -> io::Result<Vec<u8>> {
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

fn parse_metadata(bytes: &[u8]) -> Result<Box<UbiMetadata>> {
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

    Ok(metadata)
}

fn metadata_equal(lhs: &UbiMetadata, rhs: &UbiMetadata) -> bool {
    lhs.magic == rhs.magic
        && lhs.version_major == rhs.version_major
        && lhs.version_minor == rhs.version_minor
        && lhs.stripe_sector_count_shift == rhs.stripe_sector_count_shift
        && lhs.stripe_headers == rhs.stripe_headers
}

pub struct RemoteBlockDevice {
    server_addr: String,
    metadata: Arc<UbiMetadata>,
    sector_count: u64,
    stripe_sector_count: u64,
}

impl RemoteBlockDevice {
    pub fn new(server_addr: String) -> Result<Box<Self>> {
        let mut stream = TcpStream::connect(&server_addr)
            .map_err(|e| VhostUserBlockError::IoError { source: e })?;
        let metadata_bytes = read_metadata_bytes(&mut stream)
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
            server_addr,
            metadata: Arc::from(metadata),
            sector_count,
            stripe_sector_count,
        }))
    }
}

impl BlockDevice for RemoteBlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>> {
        let channel = RemoteIoChannel::new(
            &self.server_addr,
            Arc::clone(&self.metadata),
            self.stripe_sector_count,
        )?;
        Ok(Box::new(channel))
    }

    fn sector_count(&self) -> u64 {
        self.sector_count
    }
}

struct RemoteIoChannel {
    stream: TcpStream,
    metadata: Arc<UbiMetadata>,
    stripe_sector_count: u64,
    finished_requests: Vec<(usize, bool)>,
}

impl RemoteIoChannel {
    fn new(
        server_addr: &str,
        metadata: Arc<UbiMetadata>,
        stripe_sector_count: u64,
    ) -> Result<Self> {
        let mut stream = TcpStream::connect(server_addr)
            .map_err(|e| VhostUserBlockError::IoChannelCreation { source: e })?;
        let metadata_bytes = read_metadata_bytes(&mut stream)
            .map_err(|e| VhostUserBlockError::IoChannelCreation { source: e })?;
        let remote_metadata = parse_metadata(&metadata_bytes)?;

        if !metadata_equal(&metadata, &remote_metadata) {
            return Err(VhostUserBlockError::MetadataError {
                description: "remote metadata changed between connections".to_string(),
            });
        }

        Ok(Self {
            stream,
            metadata,
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
    fn add_read(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        if self.stripe_sector_count == 0 {
            error!("Remote stripe size is zero");
            self.finished_requests.push((id, false));
            return;
        }

        if sector_offset % self.stripe_sector_count != 0 {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::aligned_buffer::AlignedBuf;
    use std::cell::RefCell;
    use std::io::{ErrorKind, Read, Write};
    use std::net::TcpListener;
    use std::rc::Rc;
    use std::thread;
    use std::time::Duration;

    #[test]
    fn fills_sparse_stripes_without_network_access() -> Result<()> {
        let stripe_shift = 3u8;
        let mut metadata = UbiMetadata::new(stripe_shift, 2, 2);
        metadata.stripe_headers[0] = (1 << 0) | STRIPE_WRITTEN_MASK;
        metadata.stripe_headers[1] = 1 << 0;

        let metadata_size = metadata.metadata_size();
        let mut metadata_bytes = vec![0u8; metadata_size];
        metadata.write_to_buf(&mut metadata_bytes[..metadata_size]);

        let stripe_sector_count = metadata.stripe_size();
        let stripe_len_bytes = (stripe_sector_count as usize) * SECTOR_SIZE;
        let stripe_payload = (0..stripe_len_bytes)
            .map(|i| (i % 251) as u8)
            .collect::<Vec<u8>>();
        let stripe_payload_clone = stripe_payload.clone();

        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = listener.local_addr().unwrap();

        let server_handle = thread::spawn(move || {
            for conn_idx in 0..2 {
                let (mut stream, _) = listener.accept().unwrap();
                stream
                    .write_all(&(metadata_bytes.len() as u32).to_le_bytes())
                    .unwrap();
                stream.write_all(&metadata_bytes).unwrap();

                if conn_idx == 1 {
                    let mut req = [0u8; 9];
                    stream.read_exact(&mut req).unwrap();
                    assert_eq!(req[0], READ_STRIPE_CMD);
                    let stripe_id = u64::from_le_bytes(req[1..].try_into().unwrap());
                    assert_eq!(stripe_id, 0);
                    stream.write_all(&[STATUS_OK]).unwrap();
                    stream.write_all(&stripe_payload).unwrap();
                }

                stream
                    .set_read_timeout(Some(Duration::from_millis(200)))
                    .unwrap();
                let mut tmp = [0u8; 9];
                match stream.read(&mut tmp) {
                    Ok(0) => {}
                    Err(e)
                        if matches!(
                            e.kind(),
                            ErrorKind::WouldBlock | ErrorKind::TimedOut | ErrorKind::UnexpectedEof
                        ) => {}
                    Ok(_) => panic!("unexpected additional data on connection {conn_idx}"),
                    Err(e) => panic!("unexpected io error: {e}"),
                }
            }
        });

        let device = RemoteBlockDevice::new(addr.to_string())?;
        let mut channel = device.create_channel()?;

        let stripe_sector_count_u32 = stripe_sector_count as u32;
        let buffer_written = Rc::new(RefCell::new(AlignedBuf::new(stripe_len_bytes)));
        channel.add_read(0, stripe_sector_count_u32, buffer_written.clone(), 1);
        channel.submit()?;
        let results = channel.poll();
        assert_eq!(results, vec![(1, true)]);
        assert_eq!(
            &buffer_written.borrow().as_slice()[..stripe_len_bytes],
            &stripe_payload_clone[..]
        );

        let buffer_sparse = Rc::new(RefCell::new(AlignedBuf::new(stripe_len_bytes)));
        channel.add_read(
            stripe_sector_count,
            stripe_sector_count_u32,
            buffer_sparse.clone(),
            2,
        );
        channel.submit()?;
        let results = channel.poll();
        assert_eq!(results, vec![(2, true)]);
        assert!(buffer_sparse.borrow().as_slice()[..stripe_len_bytes]
            .iter()
            .all(|&b| b == 0));

        drop(channel);
        drop(device);

        server_handle.join().unwrap();
        Ok(())
    }
}
