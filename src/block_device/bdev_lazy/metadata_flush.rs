use std::{
    ptr::copy_nonoverlapping,
    sync::{
        atomic::{AtomicU64, Ordering},
        Arc,
    },
};

use crate::{vhost_backend::SECTOR_SIZE, Result, VhostUserBlockError};
use log::{debug, error};

use super::metadata::{StripeMetadataManager, UbiMetadata};
use super::metadata_init::{METADATA_FLUSH_ID, METADATA_WRITE_ID};

#[derive(Debug, Clone)]
pub struct MetadataFlushState {
    metadata_version: Arc<AtomicU64>,
    metadata_version_flushed: Arc<AtomicU64>,
}

impl MetadataFlushState {
    pub fn new() -> Self {
        Self {
            metadata_version: Arc::new(AtomicU64::new(1)),
            metadata_version_flushed: Arc::new(AtomicU64::new(0)),
        }
    }

    pub fn increment_version(&self) {
        self.metadata_version.fetch_add(1, Ordering::SeqCst);
    }

    pub fn set_flushed_version(&self, version: u64) {
        self.metadata_version_flushed
            .store(version, Ordering::Release);
    }

    pub fn flushed_version(&self) -> u64 {
        self.metadata_version_flushed.load(Ordering::Acquire)
    }

    pub fn current_version(&self) -> u64 {
        self.metadata_version.load(Ordering::Acquire)
    }

    pub fn needs_flush(&self) -> bool {
        let flushed = self.metadata_version_flushed.load(Ordering::Acquire);
        let current = self.metadata_version.load(Ordering::Acquire);
        current > flushed
    }
}

impl StripeMetadataManager {
    pub fn start_flush(&mut self) -> Result<super::metadata::StartFlushResult> {
        if !self.flush_state.needs_flush() {
            debug!("No changes to flush");
            return Ok(super::metadata::StartFlushResult::NoChanges);
        }

        if self.metadata_version_being_flushed.is_some() {
            return Err(VhostUserBlockError::MetadataError {
                description: "Flush already in progress".to_string(),
            });
        }

        let current_version = self.flush_state.current_version();

        debug!("Starting flush for metadata version {}", current_version);

        self.metadata_version_being_flushed = Some(current_version);

        let metadata_buf = self.metadata_buf.clone();
        let metadata_size = std::mem::size_of::<UbiMetadata>();
        unsafe {
            let src = &*self.metadata as *const UbiMetadata as *const u8;
            let dst = metadata_buf.borrow_mut().as_mut_ptr();
            copy_nonoverlapping(src, dst, metadata_size);
        }

        let sector_count = metadata_buf.borrow().len() / SECTOR_SIZE;
        self.channel
            .add_write(0, sector_count as u32, metadata_buf, METADATA_WRITE_ID);

        self.channel.submit()?;

        Ok(super::metadata::StartFlushResult::Started)
    }

    pub fn shared_flush_state(&self) -> MetadataFlushState {
        self.flush_state.clone()
    }

    pub fn poll_flush(&mut self) -> Option<bool> {
        for (id, success) in self.channel.poll() {
            if id == METADATA_WRITE_ID {
                if !success {
                    error!("Metadata write failed");
                    self.metadata_version_being_flushed = None;
                    return Some(false);
                }

                self.channel.add_flush(METADATA_FLUSH_ID);
                if let Err(e) = self.channel.submit() {
                    error!("Failed to submit flush: {}", e);
                    self.metadata_version_being_flushed = None;
                    return Some(false);
                }
                return None;
            } else if id == METADATA_FLUSH_ID {
                match (self.metadata_version_being_flushed, success) {
                    (None, _) => {
                        error!("Flush completion received without a pending flush");
                        return Some(false);
                    }
                    (Some(version), false) => {
                        error!("Metadata flush for version {} failed", version);
                        self.metadata_version_being_flushed = None;
                        return Some(false);
                    }
                    (Some(version), true) => {
                        debug!("Metadata flush completed for version {}", version);
                        self.flush_state.set_flushed_version(version);
                        self.metadata_version_being_flushed = None;
                        return Some(true);
                    }
                }
            }
        }
        None
    }
}
