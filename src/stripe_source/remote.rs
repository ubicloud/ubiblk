use std::collections::VecDeque;

use log::error;

use crate::{
    block_device::SharedBuffer, stripe_server::StripeServerClient, Result, VhostUserBlockError,
};

use super::StripeSource;

pub struct RemoteStripeSource {
    client: StripeServerClient,
    source_sector_count: u64,
    pending_requests: VecDeque<(usize, SharedBuffer)>,
    inflight: Option<(usize, SharedBuffer)>,
}

impl RemoteStripeSource {
    pub fn new(client: StripeServerClient, stripe_sector_count: u64) -> Result<Self> {
        let metadata = client.metadata.as_ref().ok_or(VhostUserBlockError::Other {
            description: "metadata not fetched from remote server".to_string(),
        })?;

        let remote_stripe_size = metadata.stripe_size();
        if remote_stripe_size != stripe_sector_count {
            return Err(VhostUserBlockError::InvalidParameter {
                description: format!(
                    "remote stripe size {remote_stripe_size} does not match expected {stripe_sector_count}",
                ),
            });
        }

        let source_sector_count = metadata
            .stripe_count()
            .checked_mul(remote_stripe_size)
            .ok_or(VhostUserBlockError::InvalidParameter {
                description: "remote stripe count too large".to_string(),
            })?;

        Ok(Self {
            client,
            source_sector_count,
            pending_requests: VecDeque::new(),
            inflight: None,
        })
    }
}

impl StripeSource for RemoteStripeSource {
    fn request(&mut self, stripe_id: usize, buffer: SharedBuffer) -> Result<()> {
        self.pending_requests.push_back((stripe_id, buffer));
        Ok(())
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        if self.inflight.is_none() {
            self.inflight = self.pending_requests.pop_front();
        }

        let mut completions = Vec::new();
        if let Some((stripe_id, buffer)) = self.inflight.take() {
            match self.client.fetch_stripe(stripe_id as u64) {
                Ok(data) => {
                    let mut buf_ref = buffer.borrow_mut();
                    if data.len() > buf_ref.len() {
                        error!(
                            "Stripe {} returned {} bytes which exceeds buffer size {}",
                            stripe_id,
                            data.len(),
                            buf_ref.len()
                        );
                        completions.push((stripe_id, false));
                    } else {
                        let dest = buf_ref.as_mut_slice();
                        dest[..data.len()].copy_from_slice(&data);
                        completions.push((stripe_id, true));
                    }
                }
                Err(err) => {
                    error!("Failed to fetch stripe {}: {err}", stripe_id);
                    completions.push((stripe_id, false));
                }
            }
        }

        completions
    }

    fn busy(&self) -> bool {
        self.inflight.is_some() || !self.pending_requests.is_empty()
    }

    fn sector_count(&self) -> u64 {
        self.source_sector_count
    }
}
