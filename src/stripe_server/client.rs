use std::net::{SocketAddr, TcpStream};

use log::{info, warn};

use crate::config::RemoteStripeSourceConfig;

use super::*;

impl StripeServerClient {
    pub fn new(stream: DynStream) -> Self {
        Self {
            stream,
            metadata: None,
        }
    }

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
        let metadata_size = u64::from_le_bytes(size_bytes) as usize;

        // Read metadata
        let mut metadata_bytes = vec![0u8; metadata_size];
        self.stream.read_exact(&mut metadata_bytes)?;

        let metadata = UbiMetadata::from_bytes(&metadata_bytes);
        self.metadata = Some(*metadata);

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

pub fn connect_to_stripe_server(
    conf: &RemoteStripeSourceConfig,
    allow_insecure: bool,
) -> Result<StripeServerClient> {
    let psk = if let (Some(identity), Some(secret)) = (&conf.psk_identity, &conf.psk_secret) {
        Some(PskCredentials::new(identity.clone(), secret.clone())?)
    } else {
        None
    };

    if psk.is_none() {
        if !allow_insecure {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: "No PSK credentials configured and allow_insecure not set. Refusing to connect without transport encryption.".to_string(),
            }));
        }
        warn!("No PSK credentials configured — connecting to stripe server WITHOUT transport encryption.");
    }

    let server_addr: SocketAddr = conf.address.parse().map_err(|err| {
        crate::ubiblk_error!(InvalidParameter {
            description: format!("invalid server address {}: {}", conf.address, err),
        })
    })?;

    let stream: DynStream = Box::new(TcpStream::connect(server_addr)?);
    let stream = if let Some(creds) = psk {
        wrap_psk_client_stream(stream, &creds)?
    } else {
        stream
    };

    let mut client = StripeServerClient::new(stream);
    client.fetch_metadata()?;

    Ok(client)
}

#[cfg(test)]
mod tests {
    use std::{os::unix::net::UnixStream, sync::Arc, thread};

    use crate::backends::SECTOR_SIZE;
    use crate::block_device::{
        bdev_test::TestBlockDevice, metadata_flags, BlockDevice, UbiMetadata,
    };
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
        let server = StripeServer::new(server_device, metadata);
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
        let conf = RemoteStripeSourceConfig {
            address: "127.0.0.1:9999".to_string(),
            psk_identity: None,
            psk_secret: None,
        };
        let result = connect_to_stripe_server(&conf, true);
        assert!(result.is_err());
        let err_msg = format!("{}", result.err().unwrap());
        assert!(err_msg.contains("Connection refused"));
    }

    #[test]
    fn test_refuses_without_psk_and_allow_insecure() {
        let conf = RemoteStripeSourceConfig {
            address: "127.0.0.1:9999".to_string(),
            psk_identity: None,
            psk_secret: None,
        };
        let result = connect_to_stripe_server(&conf, false);
        assert!(result.is_err());
        let err_msg = format!("{}", result.err().unwrap());
        assert!(err_msg.contains("Refusing to connect without transport encryption"));
    }
}
