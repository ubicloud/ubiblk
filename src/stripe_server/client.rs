use std::collections::HashMap;
use std::net::{SocketAddr, TcpStream};
use std::time::Duration;

use log::{info, warn};
use ubiblk_macros::error_context;

use crate::backends::SECTOR_SIZE;
use crate::config::v2::secrets::{get_resolved_secret, ResolvedSecret};
use crate::config::v2::stripe_source::RemoteStripeConfig;

use super::*;

const MAX_REMOTE_METADATA_SIZE: usize = 64 * 1024 * 1024;

impl StripeServerClient {
    pub fn new(stream: DynStream) -> Self {
        Self {
            stream,
            metadata: None,
        }
    }

    #[error_context("Failed to fetch metadata from stripe server")]
    fn fetch_metadata(&mut self) -> Result<()> {
        info!("Fetching metadata from server");

        // Send metadata request opcode
        self.stream.write_all(&[METADATA_CMD])?;
        self.stream.flush()?;

        // Read response status
        let mut status = [0u8; 1];
        self.stream.read_exact(&mut status)?;

        if status[0] != STATUS_OK {
            return Err(crate::ubiblk_error!(RemoteStatus { status: status[0] }));
        }

        // Read metadata size
        let mut size_bytes = [0u8; 8];
        self.stream.read_exact(&mut size_bytes)?;
        let metadata_size_u64 = u64::from_le_bytes(size_bytes);
        let metadata_size = usize::try_from(metadata_size_u64).map_err(|_| {
            crate::ubiblk_error!(ProtocolError {
                description: format!(
                    "Remote metadata size {metadata_size_u64} exceeds local limits"
                ),
            })
        })?;
        if metadata_size < SECTOR_SIZE {
            return Err(crate::ubiblk_error!(ProtocolError {
                description: format!("Remote metadata size {metadata_size} is too small"),
            }));
        }
        if metadata_size > MAX_REMOTE_METADATA_SIZE {
            return Err(crate::ubiblk_error!(ProtocolError {
                description: format!(
                    "Remote metadata size {metadata_size} exceeds maximum {MAX_REMOTE_METADATA_SIZE}"
                ),
            }));
        }

        // Read metadata
        let mut metadata_bytes = vec![0u8; metadata_size];
        self.stream.read_exact(&mut metadata_bytes)?;

        let metadata = UbiMetadata::from_bytes(&metadata_bytes)?;
        self.metadata = Some(*metadata);

        Ok(())
    }

    #[error_context("Failed to complete hello handshake with stripe server")]
    fn hello(&mut self) -> Result<()> {
        info!("Performing hello handshake with server");

        // Send hello opcode
        self.stream.write_all(&[HELLO_CMD])?;
        self.stream.flush()?;

        // Read response status
        let mut status = [0u8; 1];
        self.stream.read_exact(&mut status)?;
        if status[0] == STATUS_INVALID_COMMAND {
            // An old server that predates HELLO_CMD rejects the unknown opcode.
            return Err(crate::ubiblk_error!(ProtocolError {
                description:
                    "Remote stripe server does not support protocol-version negotiation (server too old)"
                        .to_string(),
            }));
        }
        if status[0] != STATUS_OK {
            return Err(crate::ubiblk_error!(RemoteStatus { status: status[0] }));
        }

        // Read and check the server's protocol version
        let mut version_bytes = [0u8; 4];
        self.stream.read_exact(&mut version_bytes)?;
        let version = u32::from_le_bytes(version_bytes);
        if version != PROTOCOL_VERSION {
            return Err(crate::ubiblk_error!(ProtocolError {
                description: format!(
                    "Remote stripe server protocol version {version} is incompatible with client version {PROTOCOL_VERSION}"
                ),
            }));
        }

        Ok(())
    }

    #[cfg(test)]
    fn send_invalid_command(&mut self) -> Result<u8> {
        self.stream.write_all(&[0xFF])?;
        self.stream.flush()?;

        let mut status = [0u8; 1];
        self.stream.read_exact(&mut status)?;

        Ok(status[0])
    }
}

impl RemoteStripeProvider for StripeServerClient {
    #[error_context("Failed to fetch stripe {} from stripe server", stripe_idx)]
    fn fetch_stripe(&mut self, stripe_idx: u64) -> Result<Vec<u8>> {
        info!("Fetching stripe {} from server", stripe_idx);

        let metadata = self
            .metadata
            .as_ref()
            .ok_or(crate::ubiblk_error!(MissingStripeMetadata))?;

        // Prepare request
        let mut request = [0u8; 9];
        request[0] = READ_STRIPE_CMD;
        request[1..].copy_from_slice(&stripe_idx.to_le_bytes());

        // Send request
        self.stream.write_all(&request)?;
        self.stream.flush()?;

        // Read response status
        let mut status = [0u8; 1];
        self.stream.read_exact(&mut status)?;

        match status[0] {
            STATUS_OK => {
                // Read stripe size
                let mut size_bytes = [0u8; 8];
                self.stream.read_exact(&mut size_bytes)?;
                let stripe_size = u64::from_le_bytes(size_bytes) as usize;

                let expected_stripe_size = metadata.stripe_size();

                if stripe_size != expected_stripe_size {
                    return Err(crate::ubiblk_error!(StripeSizeMismatch {
                        stripe: stripe_idx,
                        expected: expected_stripe_size,
                        actual: stripe_size,
                    }));
                }

                // Read stripe data
                let mut stripe_data = vec![0u8; stripe_size];
                self.stream.read_exact(&mut stripe_data)?;

                Ok(stripe_data)
            }
            STATUS_INVALID_STRIPE => Err(crate::ubiblk_error!(InvalidParameter {
                description: format!("Invalid stripe index: {}", stripe_idx),
            })),
            STATUS_NO_DATA | STATUS_NOT_FETCHED => {
                Err(crate::ubiblk_error!(StripeUnavailableData {
                    stripe: stripe_idx
                }))
            }
            STATUS_SERVER_ERROR => Err(crate::ubiblk_error!(RemoteStatus {
                status: STATUS_SERVER_ERROR,
            })),
            _ => Err(crate::ubiblk_error!(RemoteStatus { status: status[0] })),
        }
    }

    fn get_metadata(&self) -> Option<&UbiMetadata> {
        self.metadata.as_ref()
    }
}

#[error_context("Failed to connect to stripe server")]
pub fn connect_to_stripe_server(
    conf: &RemoteStripeConfig,
    resolved_secrets: &HashMap<String, ResolvedSecret>,
) -> Result<StripeServerClient> {
    if conf.psk.is_none() {
        warn!("No PSK credentials configured — connecting to stripe server WITHOUT transport encryption.");
    }

    let server_addr: SocketAddr = conf.address.parse().map_err(|err| {
        crate::ubiblk_error!(InvalidParameter {
            description: format!("invalid server address {}: {}", conf.address, err),
        })
    })?;

    let creds = if let Some(psk) = &conf.psk {
        let resolved = get_resolved_secret(&psk.secret, resolved_secrets)?;
        Some(PskCredentials::new(
            psk.identity.clone(),
            resolved.as_bytes().to_vec(),
        )?)
    } else {
        None
    };

    let tcp =
        TcpStream::connect_timeout(&server_addr, Duration::from_millis(conf.connect_timeout_ms))?;
    tcp.set_read_timeout(Some(Duration::from_millis(
        conf.operation_attempt_timeout_ms,
    )))?;
    tcp.set_write_timeout(Some(Duration::from_millis(
        conf.operation_attempt_timeout_ms,
    )))?;
    let stream: DynStream = Box::new(tcp);
    let stream = if let Some(creds) = creds {
        wrap_psk_client_stream(stream, &creds)?
    } else {
        stream
    };

    let mut client = StripeServerClient::new(stream);
    client.hello()?;
    client.fetch_metadata()?;

    Ok(client)
}

#[cfg(test)]
mod tests {
    use std::io::{Cursor, Read, Write};
    use std::{os::unix::net::UnixStream, sync::Arc, thread};

    use crate::backends::SECTOR_SIZE;
    use crate::block_device::{
        bdev_test::TestBlockDevice, metadata_flags, BlockDevice, UbiMetadata,
    };
    use crate::config::v2::stripe_source::RemoteStripeConfig;
    use crate::stripe_server::StripeServer;
    use crate::UbiblkError;

    use super::*;

    fn run_client_with_server<F, T>(
        metadata: Arc<UbiMetadata>,
        stripe_device: Arc<TestBlockDevice>,
        psk: Option<PskCredentials>,
        f: F,
    ) -> T
    where
        F: FnOnce(&mut StripeServerClient) -> T + Send + 'static,
        T: Send + 'static,
    {
        let server_device: Arc<dyn BlockDevice> = stripe_device.clone();
        let server = StripeServer::new(server_device, metadata, None);
        let (server_stream, client_stream) = UnixStream::pair().unwrap();
        let (sender, receiver) = std::sync::mpsc::channel();
        let server_stream: DynStream = Box::new(server_stream);
        let client_stream: DynStream = Box::new(client_stream);
        let client_psk = psk.clone();
        thread::spawn(move || {
            let client_stream = if let Some(ref creds) = client_psk {
                wrap_psk_client_stream(client_stream, creds).expect("TLS setup should succeed")
            } else {
                client_stream
            };

            let mut client = StripeServerClient::new(client_stream);
            let result = f(&mut client);
            sender.send(result).unwrap();
        });

        let server_stream = if let Some(ref creds) = psk {
            wrap_psk_server_stream(server_stream, creds).expect("TLS setup should succeed")
        } else {
            server_stream
        };
        let mut session = server
            .start_session(server_stream)
            .expect("session creation should succeed");

        session.handle_requests();
        receiver.recv().expect("client thread should send a result")
    }

    fn test_metadata(
        device_stripe_count: usize,
        image_stripe_count: usize,
        fetched_stripes: &[usize],
        written_stripes: &[usize],
    ) -> Arc<UbiMetadata> {
        let mut metadata = UbiMetadata::new(0, device_stripe_count, image_stripe_count);
        for &idx in fetched_stripes {
            metadata.stripe_headers[idx] |= metadata_flags::FETCHED;
        }
        for &idx in written_stripes {
            metadata.stripe_headers[idx] |= metadata_flags::WRITTEN;
        }
        Arc::from(metadata)
    }

    #[test]
    fn fetches_metadata_with_written_and_no_data_bits() {
        let stripe_count = 2;
        let metadata = test_metadata(stripe_count, stripe_count, &[], &[0]);
        let stripe_device = Arc::new(TestBlockDevice::new(
            (stripe_count as u64) * SECTOR_SIZE as u64,
        ));

        let fetched_metadata =
            run_client_with_server(metadata.clone(), stripe_device, None, |client| {
                client
                    .fetch_metadata()
                    .expect("metadata fetch should succeed");
                client.get_metadata().unwrap().clone()
            });

        assert_eq!(fetched_metadata.stripe_headers.len(), stripe_count);
        assert_ne!(
            fetched_metadata.stripe_headers[0] & metadata_flags::WRITTEN,
            0
        );
        assert_eq!(
            fetched_metadata.stripe_headers[1] & metadata_flags::WRITTEN,
            0
        );
    }

    #[test]
    fn fetches_written_stripe() {
        let stripe_count = 2;
        let metadata = test_metadata(stripe_count, 0, &[], &[0]);
        let stripe_device = Arc::new(TestBlockDevice::new(
            (stripe_count as u64) * SECTOR_SIZE as u64,
        ));

        let pattern = (0..SECTOR_SIZE)
            .map(|idx| (idx % (u8::MAX as usize + 1)) as u8)
            .collect::<Vec<_>>();
        stripe_device.write(0, &pattern, pattern.len());

        let stripe_data = run_client_with_server(metadata, stripe_device, None, |client| {
            client
                .fetch_metadata()
                .expect("metadata fetch should succeed");
            client
                .fetch_stripe(0)
                .expect("written stripe should be readable")
        });
        assert_eq!(stripe_data, pattern);
    }

    #[test]
    fn fetches_fetched_stripe() {
        let stripe_count = 2;
        let metadata = test_metadata(stripe_count, stripe_count, &[1], &[]);
        let stripe_device = Arc::new(TestBlockDevice::new(
            (stripe_count as u64) * SECTOR_SIZE as u64,
        ));

        let pattern = (0..SECTOR_SIZE)
            .map(|idx| (idx % (u8::MAX as usize + 1)) as u8)
            .collect::<Vec<_>>();
        stripe_device.write(SECTOR_SIZE, &pattern, pattern.len());

        let stripe_data = run_client_with_server(metadata, stripe_device, None, |client| {
            client
                .fetch_metadata()
                .expect("metadata fetch should succeed");
            client
                .fetch_stripe(1)
                .expect("fetched stripe should be readable")
        });
        assert_eq!(stripe_data, pattern);
    }

    #[test]
    fn fetching_no_data_stripe_returns_error() {
        let device_stripe_count: usize = 6;
        let image_device_stripe_count: usize = 2;
        let metadata = test_metadata(device_stripe_count, image_device_stripe_count, &[], &[0]);
        let stripe_device = Arc::new(TestBlockDevice::new(
            (device_stripe_count as u64) * SECTOR_SIZE as u64,
        ));

        let err = run_client_with_server(metadata.clone(), stripe_device.clone(), None, |client| {
            client
                .fetch_metadata()
                .expect("metadata fetch should succeed");
            client
                .fetch_stripe(1)
                .expect_err("unfetched stripe should return an error")
        });
        assert!(matches!(
            err,
            UbiblkError::StripeUnavailableData { stripe, .. } if stripe == 1
        ));

        let err = run_client_with_server(metadata, stripe_device, None, |client| {
            client
                .fetch_metadata()
                .expect("metadata fetch should succeed");
            client
                .fetch_stripe(4)
                .expect_err("unwritten stripe should return an error")
        });
        assert!(matches!(
            err,
            UbiblkError::StripeUnavailableData { stripe, .. } if stripe == 4
        ));
    }

    #[test]
    fn fetching_out_of_bounds_stripe_returns_error() {
        let stripe_count = 2;
        let metadata = test_metadata(stripe_count, stripe_count, &[], &[0]);
        let stripe_device = Arc::new(TestBlockDevice::new(
            (stripe_count as u64) * SECTOR_SIZE as u64,
        ));

        let err = run_client_with_server(metadata, stripe_device, None, |client| {
            client
                .fetch_metadata()
                .expect("metadata fetch should succeed");
            client
                .fetch_stripe(10)
                .expect_err("out-of-bounds stripe should return an error")
        });
        assert!(matches!(
            err,
            UbiblkError::InvalidParameter { description, .. }
                if description.contains("Invalid stripe index")
        ));
    }

    #[test]
    fn sending_invalid_command_returns_error_status() {
        let stripe_count = 1;
        let metadata = test_metadata(stripe_count, stripe_count, &[], &[0]);
        let stripe_device = Arc::new(TestBlockDevice::new(
            (stripe_count as u64) * SECTOR_SIZE as u64,
        ));

        let status = run_client_with_server(metadata, stripe_device, None, |client| {
            client
                .send_invalid_command()
                .expect("sending invalid command should succeed")
        });

        assert_eq!(status, STATUS_INVALID_COMMAND);
    }

    #[test]
    fn hello_succeeds_with_matching_version() {
        let stripe_count = 1;
        let metadata = test_metadata(stripe_count, stripe_count, &[], &[0]);
        let stripe_device = Arc::new(TestBlockDevice::new(
            (stripe_count as u64) * SECTOR_SIZE as u64,
        ));

        run_client_with_server(metadata, stripe_device, None, |client| {
            client.hello().expect("hello handshake should succeed");
        });
    }

    struct CannedStream {
        read: Cursor<Vec<u8>>,
    }

    impl Read for CannedStream {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            self.read.read(buf)
        }
    }

    impl Write for CannedStream {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            Ok(buf.len())
        }

        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    #[test]
    fn hello_rejects_incompatible_version() {
        let mut response = vec![STATUS_OK];
        response.extend_from_slice(&(PROTOCOL_VERSION + 1).to_le_bytes());
        let stream: DynStream = Box::new(CannedStream {
            read: Cursor::new(response),
        });
        let mut client = StripeServerClient::new(stream);

        let err = client
            .hello()
            .expect_err("incompatible version should be rejected");
        assert!(matches!(err, UbiblkError::ProtocolError { .. }));
    }

    #[test]
    fn hello_rejects_old_server() {
        // An old server that predates HELLO_CMD replies STATUS_INVALID_COMMAND.
        let stream: DynStream = Box::new(CannedStream {
            read: Cursor::new(vec![STATUS_INVALID_COMMAND]),
        });
        let mut client = StripeServerClient::new(stream);

        let err = client
            .hello()
            .expect_err("an old server should be rejected");
        assert!(matches!(err, UbiblkError::ProtocolError { .. }));
    }

    #[test]
    fn hello_propagates_error_status() {
        let stream: DynStream = Box::new(CannedStream {
            read: Cursor::new(vec![STATUS_SERVER_ERROR]),
        });
        let mut client = StripeServerClient::new(stream);

        let err = client
            .hello()
            .expect_err("a server error status should be rejected");
        assert!(matches!(
            err,
            UbiblkError::RemoteStatus { status, .. } if status == STATUS_SERVER_ERROR
        ));
    }

    #[test]
    fn fetches_metadata_over_psk() {
        let stripe_count = 1;
        let metadata = test_metadata(stripe_count, stripe_count, &[], &[0]);
        let stripe_device = Arc::new(TestBlockDevice::new(
            (stripe_count as u64) * SECTOR_SIZE as u64,
        ));

        let psk = PskCredentials::new(
            "client1".to_string(),
            vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16],
        )
        .expect("PSK credentials should be valid");

        let metadata_result =
            run_client_with_server(metadata.clone(), stripe_device, Some(psk), |client| {
                client
                    .fetch_metadata()
                    .expect("metadata fetch should succeed");
                client.metadata.clone()
            });

        let fetched_metadata = metadata_result.expect("metadata should be returned");
        assert_eq!(fetched_metadata.stripe_headers.len(), stripe_count);
    }

    #[test]
    fn test_connection_failure() {
        let conf = RemoteStripeConfig {
            address: "127.0.0.1:9999".to_string(),
            psk: None,
            autofetch: false,
            connect_timeout_ms: 5_000,
            operation_attempt_timeout_ms: 20_000,
        };
        let result = connect_to_stripe_server(&conf, &HashMap::new());
        assert!(result.is_err());
        let error_message = result.err().unwrap().to_string();
        assert!(error_message.contains("Failed to connect to stripe server"));
    }

    #[test]
    fn serves_unfetched_source_stripe_from_source() -> Result<()> {
        use crate::config::v2::stripe_source::StripeSourceConfig;
        use crate::config::v2::{self, DangerZone, DeviceSection};
        use crate::stripe_source::StripeSourceBuilder;
        use std::io::Write as _;
        use tempfile::NamedTempFile;

        let stripe_count = 4usize;
        let stripe_size = SECTOR_SIZE; // stripe_sector_count_shift = 0 -> one sector

        // Source holds pattern A; the overlay holds a different pattern B. Every
        // stripe has a source and is NOT fetched, so it must be served from the
        // source (A) rather than the overlay (B).
        let source_file = NamedTempFile::new()?;
        let overlay_file = NamedTempFile::new()?;
        let pattern_a: Vec<u8> = (0..stripe_count * stripe_size)
            .map(|i| (i % 251) as u8)
            .collect();
        let pattern_b = vec![0xBBu8; stripe_count * stripe_size];
        source_file.as_file().write_all(&pattern_a)?;
        overlay_file.as_file().write_all(&pattern_b)?;

        let metadata: Arc<UbiMetadata> = Arc::from(UbiMetadata::new(0, stripe_count, stripe_count));

        let config = v2::Config {
            device: DeviceSection {
                data_path: overlay_file.path().into(),
                metadata_path: None,
                vhost_socket: None,
                rpc_socket: None,
                device_id: "ubiblk".to_string(),
                track_written: false,
            },
            tuning: v2::tuning::TuningSection {
                queue_size: 128,
                ..Default::default()
            },
            encryption: None,
            danger_zone: DangerZone {
                enabled: true,
                allow_unencrypted_disk: true,
                ..Default::default()
            },
            stripe_source: Some(StripeSourceConfig::Raw {
                image_path: source_file.path().into(),
                autofetch: false,
                copy_on_read: false,
            }),
            secrets: HashMap::new(),
        };

        let overlay: Arc<dyn BlockDevice> = Arc::from(crate::backends::build_block_device(
            overlay_file.path(),
            &config,
            false,
        )?);
        let builder =
            StripeSourceBuilder::new(config.clone(), metadata.stripe_sector_count(), false);
        let server = StripeServer::new(overlay, metadata, Some(builder));

        let (server_stream, client_stream) = UnixStream::pair().unwrap();
        let (tx, rx) = std::sync::mpsc::channel();
        let client_stream: DynStream = Box::new(client_stream);
        thread::spawn(move || {
            let mut client = StripeServerClient::new(client_stream);
            client
                .fetch_metadata()
                .expect("metadata fetch should succeed");
            let data = client
                .fetch_stripe(0)
                .expect("unfetched source stripe should be served");
            tx.send(data).unwrap();
        });

        let mut session = server
            .start_session(Box::new(server_stream))
            .expect("session creation should succeed");
        session.handle_requests();
        let served = rx.recv().expect("client thread should return data");

        assert_eq!(
            served,
            pattern_a[0..stripe_size],
            "stripe 0 served from the source"
        );
        assert_ne!(
            served,
            pattern_b[0..stripe_size],
            "must not be the overlay's data"
        );
        Ok(())
    }
}
