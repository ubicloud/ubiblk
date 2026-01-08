use std::collections::VecDeque;

use log::{error, warn};

use crate::{
    block_device::{metadata_flags, SharedBuffer},
    stripe_server::RemoteStripeProvider,
    Result, UbiblkError,
};

use super::StripeSource;

pub struct RemoteStripeSource {
    client: Box<dyn RemoteStripeProvider>,
    source_sector_count: u64,
    pending_requests: VecDeque<(usize, SharedBuffer)>,
    remote_headers: Vec<u8>,
}

impl RemoteStripeSource {
    pub fn new(client: Box<dyn RemoteStripeProvider>, stripe_sector_count: u64) -> Result<Self> {
        let metadata = client
            .get_metadata()
            .ok_or_else(|| UbiblkError::MetadataError {
                description: "metadata not fetched from remote server".to_string(),
            })?;
        let remote_headers = metadata.stripe_headers.clone();

        let remote_stripe_sector_count = metadata.stripe_sector_count();
        if remote_stripe_sector_count != stripe_sector_count {
            return Err(UbiblkError::InvalidParameter {
                description: format!(
                    "remote stripe sector count {remote_stripe_sector_count} does not match expected {stripe_sector_count}",
                ),
            });
        }

        let source_sector_count = metadata
            .stripe_count()
            .checked_mul(remote_stripe_sector_count)
            .ok_or_else(|| UbiblkError::InvalidParameter {
                description: "remote stripe count too large (overflow)".to_string(),
            })?;

        Ok(Self {
            client,
            source_sector_count,
            pending_requests: VecDeque::new(),
            remote_headers,
        })
    }
}

impl StripeSource for RemoteStripeSource {
    fn request(&mut self, stripe_id: usize, buffer: SharedBuffer) -> Result<()> {
        self.pending_requests.push_back((stripe_id, buffer));
        Ok(())
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        let mut completions = Vec::with_capacity(self.pending_requests.len());

        while let Some((stripe_id, buffer)) = self.pending_requests.pop_front() {
            let result = match self.client.fetch_stripe(stripe_id as u64) {
                Ok(data) => {
                    let mut buf_ref = buffer.borrow_mut();
                    let buf = buf_ref.as_mut_slice();

                    if data.len() > buf.len() {
                        error!(
                            "Stripe {} returned {} bytes which exceeds buffer size {}",
                            stripe_id,
                            data.len(),
                            buf.len()
                        );
                        false
                    } else {
                        let (dst, rest) = buf.split_at_mut(data.len());
                        dst.copy_from_slice(&data);
                        rest.fill(0);

                        if !rest.is_empty() {
                            warn!(
                                "Stripe {} returned fewer bytes ({}) than buffer capacity ({})",
                                stripe_id,
                                data.len(),
                                buf.len()
                            );
                        }
                        true
                    }
                }
                Err(err) => {
                    error!("Failed to fetch stripe {}: {err}", stripe_id);
                    false
                }
            };

            completions.push((stripe_id, result));
        }

        completions
    }

    fn busy(&self) -> bool {
        !self.pending_requests.is_empty()
    }

    fn sector_count(&self) -> u64 {
        self.source_sector_count
    }

    fn has_stripe(&self, stripe_id: usize) -> bool {
        if stripe_id >= self.remote_headers.len() {
            return false;
        }
        let written_on_remote = self.remote_headers[stripe_id] & metadata_flags::WRITTEN != 0;
        let exists_on_remote_base_image =
            self.remote_headers[stripe_id] & metadata_flags::HAS_SOURCE != 0;
        written_on_remote || exists_on_remote_base_image
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        block_device::{shared_buffer, UbiMetadata},
        vhost_backend::SECTOR_SIZE,
    };

    const STRIPE_SECTOR_COUNT_SHIFT: u8 = 4;
    const STRIPE_SECTORS: usize = 1 << STRIPE_SECTOR_COUNT_SHIFT;
    const STRIPE_SIZE: usize = STRIPE_SECTORS * SECTOR_SIZE;
    const TOTAL_STRIPES: usize = 16;

    struct MockRemoteStripeProvider {
        metadata: Box<UbiMetadata>,
    }

    impl MockRemoteStripeProvider {
        pub fn new() -> Self {
            let metadata = UbiMetadata::new(STRIPE_SECTOR_COUNT_SHIFT, TOTAL_STRIPES, 0);
            Self { metadata }
        }

        pub fn new_with_bad_metadata() -> Self {
            let metadata = UbiMetadata::new(STRIPE_SECTOR_COUNT_SHIFT + 1, TOTAL_STRIPES, 0);
            Self { metadata }
        }
    }

    impl RemoteStripeProvider for MockRemoteStripeProvider {
        fn fetch_stripe(&mut self, stripe_id: u64) -> Result<Vec<u8>> {
            if stripe_id % 2 == 1 {
                return Err(UbiblkError::IoError {
                    source: std::io::Error::other("simulated fetch error"),
                });
            }
            Ok(vec![stripe_id as u8; STRIPE_SIZE])
        }

        fn get_metadata(&self) -> Option<&UbiMetadata> {
            Some(&self.metadata)
        }
    }

    fn prep() -> RemoteStripeSource {
        let provider = Box::new(MockRemoteStripeProvider::new());
        RemoteStripeSource::new(provider, STRIPE_SECTORS as u64).unwrap()
    }

    #[test]
    fn test_fetch_good_stripe() {
        let mut source = prep();
        let buffer_1 = shared_buffer(STRIPE_SIZE);
        let buffer_2 = shared_buffer(STRIPE_SIZE);
        source.request(2, buffer_1.clone()).unwrap();
        source.request(4, buffer_2.clone()).unwrap();
        let completions = source.poll();
        assert_eq!(completions.len(), 2);

        for (stripe_id, success) in completions {
            assert!(success);
            let expected_byte = stripe_id as u8;
            let buf_ref = if stripe_id == 2 {
                buffer_1.borrow()
            } else {
                buffer_2.borrow()
            };
            for &byte in buf_ref.as_slice() {
                assert_eq!(byte, expected_byte);
            }
        }
    }

    #[test]
    fn test_fetch_stripe_with_error() {
        let mut source = prep();
        let buffer_1 = shared_buffer(STRIPE_SIZE);
        let buffer_2 = shared_buffer(STRIPE_SIZE);
        source.request(1, buffer_1.clone()).unwrap();
        source.request(3, buffer_2.clone()).unwrap();
        let completions = source.poll();
        assert_eq!(completions.len(), 2);
        for (_, success) in completions {
            assert!(!success);
        }
    }

    #[test]
    fn test_invalid_metadata() {
        let provider = Box::new(MockRemoteStripeProvider::new_with_bad_metadata());
        let result = RemoteStripeSource::new(provider, STRIPE_SECTORS as u64);
        assert!(result.is_err());
    }

    #[test]
    fn test_zeroed_buffer_on_short_stripe() {
        let mut source = prep();
        let buffer = shared_buffer(STRIPE_SIZE + 100);
        source.request(2, buffer.clone()).unwrap();
        let completions = source.poll();
        assert_eq!(completions.len(), 1);
        assert_eq!(completions[0], (2, true));
        for (i, &byte) in buffer.borrow().as_slice().iter().enumerate() {
            if i < STRIPE_SIZE {
                assert_eq!(byte, 2u8);
            } else {
                assert_eq!(byte, 0u8);
            }
        }
    }
}
