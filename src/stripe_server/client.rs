use log::info;

use crate::{vhost_backend::SECTOR_SIZE, VhostUserBlockError};

use super::*;

impl StripeServerClient {
    pub fn new(stream: DynStream) -> Self {
        Self {
            stream,
            metadata: None,
        }
    }

    pub fn fetch_metadata(&mut self) -> Result<()> {
        info!("Fetching metadata from server");

        // Send metadata request opcode
        self.stream.write_all(&[METADATA_CMD])?;
        self.stream.flush()?;

        // Read response status
        let mut status = [0u8; 1];
        self.stream.read_exact(&mut status)?;

        if status[0] != STATUS_OK {
            return Err(VhostUserBlockError::Other {
                description: format!("Server returned error status: {}", status[0]),
            });
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

    pub fn fetch_stripe(&mut self, stripe_idx: u64) -> Result<Vec<u8>> {
        info!("Fetching stripe {} from server", stripe_idx);

        let metadata = self.metadata.as_ref().ok_or(VhostUserBlockError::Other {
            description: "Metadata not fetched yet".to_string(),
        })?;

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

                let expected_stripe_size = metadata.stripe_size() as usize * SECTOR_SIZE;

                if stripe_size != expected_stripe_size {
                    return Err(VhostUserBlockError::Other {
                        description: format!(
                            "Unexpected stripe size: {} (expected {})",
                            stripe_size, expected_stripe_size
                        ),
                    });
                }

                // Read stripe data
                let mut stripe_data = vec![0u8; stripe_size];
                self.stream.read_exact(&mut stripe_data)?;

                Ok(stripe_data)
            }
            STATUS_INVALID_STRIPE => Err(VhostUserBlockError::InvalidParameter {
                description: format!("Invalid stripe index: {}", stripe_idx),
            }),
            STATUS_UNWRITTEN => Err(VhostUserBlockError::Other {
                description: format!("Stripe {} is unwritten", stripe_idx),
            }),
            STATUS_SERVER_ERROR => Err(VhostUserBlockError::Other {
                description: "Server reported an internal error".to_string(),
            }),
            _ => Err(VhostUserBlockError::Other {
                description: format!("Unknown status code: {}", status[0]),
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{os::unix::net::UnixStream, sync::Arc, thread};

    use crate::block_device::{
        bdev_test::TestBlockDevice, BlockDevice, UbiMetadata, STRIPE_WRITTEN_MASK,
    };
    use crate::stripe_server::StripeServer;
    use crate::vhost_backend::SECTOR_SIZE;

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

    fn written_unwritten_metadata(stripe_count: usize) -> Arc<UbiMetadata> {
        let mut metadata = UbiMetadata::new(0, stripe_count, stripe_count);
        metadata.stripe_headers[0] |= STRIPE_WRITTEN_MASK;
        Arc::from(metadata)
    }

    #[test]
    fn fetches_metadata_with_written_and_unwritten_bits() {
        let stripe_count = 2;
        let metadata = written_unwritten_metadata(stripe_count);
        let stripe_device = Arc::new(TestBlockDevice::new(
            (stripe_count as u64) * SECTOR_SIZE as u64,
        ));

        let metadata_result =
            run_client_with_server(metadata.clone(), stripe_device, None, |client| {
                client
                    .fetch_metadata()
                    .expect("metadata fetch should succeed");
                client.metadata.clone()
            });

        let fetched_metadata = metadata_result
            .as_ref()
            .expect("client should have fetched metadata");
        assert_eq!(fetched_metadata.stripe_headers.len(), stripe_count);
        assert_ne!(fetched_metadata.stripe_headers[0] & STRIPE_WRITTEN_MASK, 0);
        assert_eq!(fetched_metadata.stripe_headers[1] & STRIPE_WRITTEN_MASK, 0);
    }

    #[test]
    fn fetches_written_stripe() {
        let stripe_count = 2;
        let metadata = written_unwritten_metadata(stripe_count);
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
    fn fetching_unwritten_stripe_returns_error() {
        let stripe_count = 2;
        let metadata = written_unwritten_metadata(stripe_count);
        let stripe_device = Arc::new(TestBlockDevice::new(
            (stripe_count as u64) * SECTOR_SIZE as u64,
        ));

        let err = run_client_with_server(metadata, stripe_device, None, |client| {
            client
                .fetch_metadata()
                .expect("metadata fetch should succeed");
            client
                .fetch_stripe(1)
                .expect_err("unwritten stripe should return an error")
        });
        assert!(matches!(
            err,
            VhostUserBlockError::Other {
                description
            } if description.contains("Stripe 1 is unwritten")
        ));
    }

    #[test]
    fn fetches_metadata_over_psk() {
        let stripe_count = 1;
        let metadata = written_unwritten_metadata(stripe_count);
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
}
