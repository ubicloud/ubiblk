use std::collections::HashMap;

use crate::{
    archive::{ArchiveMetadata, ArchiveStore},
    block_device::SharedBuffer,
    crypt::XtsBlockCipher,
    Result, UbiblkError,
};

use super::StripeSource;

pub struct ArchiveStripeSource {
    store: Box<dyn ArchiveStore>,
    xts_cipher: Option<XtsBlockCipher>,
    stripe_sha256: HashMap<usize, String>,
    max_stripe_id: usize,
    stripe_sector_count: u64,
    finished_requests: Vec<(usize, bool)>,
}

impl ArchiveStripeSource {
    pub fn new(store: Box<dyn ArchiveStore>) -> Result<Self> {
        let metadata = Self::fetch_metadata(&store)?;
        let stripe_sha256 = Self::fetch_stripe_info(&store)?;
        let max_stripe_id = stripe_sha256.keys().max().cloned().unwrap_or(0);
        let stripe_sector_count = metadata.stripe_sector_count;
        let finished_requests = Vec::new();
        let xts_cipher = None;
        Ok(Self {
            store,
            xts_cipher,
            stripe_sha256,
            max_stripe_id,
            stripe_sector_count,
            finished_requests,
        })
    }

    fn fetch_metadata(store: &Box<dyn ArchiveStore>) -> Result<ArchiveMetadata> {
        let bytes = store.get_object("metadata.yaml")?;
        let metadata: ArchiveMetadata =
            serde_yaml::from_slice(&bytes).map_err(|e| UbiblkError::MetadataError {
                description: format!("failed to parse archive metadata: {}", e),
            })?;
        Ok(metadata)
    }

    fn fetch_stripe_info(store: &Box<dyn ArchiveStore>) -> Result<HashMap<usize, String>> {
        let object_list = store.list_objects()?;
        let mut stripe_map = HashMap::new();
        for object_name in object_list {
            if object_name == "metadata.yaml" {
                continue;
            }
            if let Some((stripe_id, sha256)) = Self::parse_stripe_object_name(&object_name) {
                stripe_map.insert(stripe_id, sha256);
            } else {
                return Err(UbiblkError::ArchiveError {
                    description: format!("invalid stripe object name: {}", object_name),
                });
            }
        }
        Ok(stripe_map)
    }

    fn parse_stripe_object_name(object_name: &str) -> Option<(usize, String)> {
        let parts: Vec<&str> = object_name.split('_').collect();
        if parts.len() != 3 {
            return None;
        }
        let stripe_id = parts[1].parse::<usize>().ok()?;
        let sha256 = parts[2].to_string();
        Some((stripe_id, sha256))
    }

    fn fetch_stripe(&mut self, stripe_id: usize, sha256: &str, buffer: SharedBuffer) -> Result<()> {
        let object_name = format!("stripe_{}_{}", stripe_id, sha256);
        let data = self.store.get_object(&object_name)?;
        let mut buf_ref = buffer.borrow_mut();
        let buf = buf_ref.as_mut_slice();
        if data.len() > buf.len() {
            return Err(UbiblkError::ArchiveError {
                description: format!(
                    "Stripe {} data size {} exceeds buffer size {}",
                    stripe_id,
                    data.len(),
                    buf.len()
                ),
            });
        }
        buf[..data.len()].copy_from_slice(&data);

        if let Some(cipher) = self.xts_cipher.as_mut() {
            let sector_start = (stripe_id as u64) * self.stripe_sector_count;
            cipher.decrypt(buf, sector_start, self.stripe_sector_count);
        }

        if data.len() < buf.len() {
            buf[data.len()..].fill(0);
        }

        self.finished_requests.push((stripe_id, true));
        Ok(())
    }
}

impl StripeSource for ArchiveStripeSource {
    fn request(&mut self, stripe_id: usize, buffer: SharedBuffer) -> Result<()> {
        let maybe_sha256 = self.stripe_sha256.get(&stripe_id).map(|s| s.clone());
        match maybe_sha256 {
            Some(sha256) => self.fetch_stripe(stripe_id, &sha256, buffer),
            None => {
                buffer.borrow_mut().as_mut_slice().fill(0);
                self.finished_requests.push((stripe_id, true));
                Ok(())
            }
        }
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        self.finished_requests.drain(..).collect()
    }

    fn busy(&self) -> bool {
        !self.finished_requests.is_empty()
    }

    fn sector_count(&self) -> u64 {
        self.max_stripe_id as u64 * self.stripe_sector_count
    }
}
