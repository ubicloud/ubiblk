use std::collections::VecDeque;
use std::sync::mpsc::{Receiver, Sender};
use std::sync::{Arc, Mutex};
use std::{cell::RefCell, rc::Rc};

use super::super::*;
use super::stripe_metadata_manager::StartFlushResult;
pub use super::stripe_metadata_manager::{StripeMetadataManager, StripeStatus, StripeStatusVec};
use crate::block_device::bdev_lazy::stripe_metadata_manager::MetadataFlushState;
use crate::utils::aligned_buffer::AlignedBuf;
use crate::{vhost_backend::SECTOR_SIZE, Result, VhostUserBlockError};
use log::{debug, error, info};
use vmm_sys_util::eventfd::EventFd;

#[derive(Debug)]
pub enum StripeFetcherRequest {
    Fetch(usize),
    FlushMetadata,
}

const MAX_CONCURRENT_FETCHES: usize = 16;

pub type SharedStripeFetcher = Arc<Mutex<StripeFetcher>>;

#[derive(Clone)]
struct FetchBuffer {
    used_for: Option<usize>,
    buf: SharedBuffer,
}

pub struct StripeFetcher {
    fetch_source_channel: Box<dyn IoChannel>,
    fetch_target_channel: Box<dyn IoChannel>,
    source_sector_count: u64,
    target_sector_count: u64,
    metadata_manager: Box<StripeMetadataManager>,
    fetch_queue: VecDeque<usize>,
    req_receiver: Receiver<StripeFetcherRequest>,
    req_sender: Sender<StripeFetcherRequest>,
    fetch_buffers: Vec<FetchBuffer>,
    stripes_fetched: usize,
    pending_flush_requests: usize,
    inprogress_flush_requests: usize,
    killfd: EventFd,
}

impl StripeFetcher {
    pub fn new(
        source_dev: &dyn BlockDevice,
        target_dev: &dyn BlockDevice,
        metadata_dev: &dyn BlockDevice,
        killfd: EventFd,
        alignment: usize,
    ) -> Result<Self> {
        let fetch_source_channel = source_dev.create_channel()?;
        let fetch_target_channel = target_dev.create_channel()?;
        let metadata_manager = StripeMetadataManager::new(metadata_dev, source_dev.sector_count())?;

        let stripe_size_u64 = metadata_manager
            .stripe_sector_count()
            .checked_mul(SECTOR_SIZE as u64)
            .ok_or_else(|| VhostUserBlockError::InvalidParameter {
                description: "stripe size too large".to_string(),
            })?;

        let stripe_size = stripe_size_u64 as usize;

        let fetch_buffers = (0..MAX_CONCURRENT_FETCHES)
            .map(|_| FetchBuffer {
                used_for: None,
                buf: Rc::new(RefCell::new(AlignedBuf::new_with_alignment(
                    stripe_size,
                    alignment,
                ))),
            })
            .collect();
        let source_sector_count = source_dev.sector_count();
        let target_sector_count = target_dev.sector_count();
        if target_sector_count < source_sector_count {
            return Err(VhostUserBlockError::InvalidParameter {
                description: "target device too small".into(),
            });
        }
        let (req_sender, req_receiver) = std::sync::mpsc::channel();

        Ok(StripeFetcher {
            fetch_source_channel,
            fetch_target_channel,
            metadata_manager,
            fetch_queue: VecDeque::new(),
            req_receiver,
            req_sender,
            fetch_buffers,
            stripes_fetched: 0,
            pending_flush_requests: 0,
            inprogress_flush_requests: 0,
            killfd,
            source_sector_count,
            target_sector_count,
        })
    }

    pub fn req_sender(&self) -> Sender<StripeFetcherRequest> {
        self.req_sender.clone()
    }

    pub fn shared_flush_state(&self) -> MetadataFlushState {
        self.metadata_manager.shared_flush_state()
    }

    pub fn handle_fetch_request(&mut self, stripe_id: usize) {
        match self.metadata_manager.stripe_status(stripe_id) {
            StripeStatus::NotFetched | StripeStatus::Failed => {
                debug!("Enqueueing stripe {} for fetch", stripe_id);
                self.fetch_queue.push_back(stripe_id);
                self.metadata_manager
                    .set_stripe_status(stripe_id, StripeStatus::Queued);
            }
            StripeStatus::Fetched => {
                debug!("Stripe {} already fetched", stripe_id);
            }
            StripeStatus::Queued | StripeStatus::Fetching => {
                debug!("Stripe {} is already queued or fetching", stripe_id);
            }
        }
    }

    fn handle_flush_request(&mut self) {
        self.pending_flush_requests += 1;
    }

    fn receive_requests(&mut self) {
        let mut requests = Vec::new();
        while let Ok(request) = self.req_receiver.try_recv() {
            debug!("Received request: {:?}", request);
            requests.push(request);
        }

        for request in requests {
            match request {
                StripeFetcherRequest::Fetch(stripe_id) => {
                    self.handle_fetch_request(stripe_id);
                }
                StripeFetcherRequest::FlushMetadata => {
                    self.handle_flush_request();
                }
            }
        }
    }

    fn fetch_completed(&mut self, buffer_idx: usize, success: bool) {
        let fetch_buffer = &mut self.fetch_buffers[buffer_idx];
        let stripe_id = fetch_buffer.used_for.unwrap();
        fetch_buffer.used_for = None;

        debug!(
            "Fetch completed for stripe {}, success={}",
            stripe_id, success
        );

        if success {
            self.metadata_manager
                .set_stripe_status(stripe_id, StripeStatus::Fetched);
            self.stripes_fetched += 1;
        } else {
            self.metadata_manager
                .set_stripe_status(stripe_id, StripeStatus::Failed);
        }
    }

    fn start_write(&mut self, buffer_idx: usize) -> bool {
        let fetch_buffer = &mut self.fetch_buffers[buffer_idx];
        let stripe_id = fetch_buffer.used_for.unwrap();
        let buf = fetch_buffer.buf.clone();
        let stripe_sector_offset = self.metadata_manager.stripe_target_sector_offset(stripe_id);
        let stripe_sector_count = self
            .metadata_manager
            .stripe_sector_count()
            .min(self.target_sector_count - stripe_sector_offset);

        self.fetch_target_channel.add_write(
            stripe_sector_offset,
            stripe_sector_count as u32,
            buf,
            buffer_idx,
        );

        if let Err(e) = self.fetch_target_channel.submit() {
            error!("Failed to submit write for stripe {}: {:?}", stripe_id, e);
            false
        } else {
            true
        }
    }

    fn poll_fetches(&mut self) -> Vec<(usize, bool)> {
        let mut result = Vec::new();
        for (buffer_idx, success) in self.fetch_source_channel.poll() {
            let stripe_id = self.fetch_buffers[buffer_idx].used_for.unwrap();
            if !success || !self.start_write(buffer_idx) {
                self.fetch_completed(buffer_idx, false);
                result.push((stripe_id, false));
            }
        }

        for (buffer_idx, success) in self.fetch_target_channel.poll() {
            let stripe_id = self.fetch_buffers[buffer_idx].used_for.unwrap();
            self.fetch_completed(buffer_idx, success);
            result.push((stripe_id, success));
        }

        result
    }

    fn start_fetches(&mut self) -> Vec<(usize, bool)> {
        let mut result = Vec::new();

        while !self.fetch_queue.is_empty() {
            let maybe_buffer_idx = self
                .fetch_buffers
                .iter()
                .position(|buf| buf.used_for.is_none());
            if maybe_buffer_idx.is_none() {
                break;
            }

            let buffer_idx = maybe_buffer_idx.unwrap();
            let fetch_buffer = &mut self.fetch_buffers[buffer_idx];

            let stripe_id = self.fetch_queue.pop_front().unwrap();
            fetch_buffer.used_for = Some(stripe_id);

            let buf = fetch_buffer.buf.clone();
            let stripe_sector_offset = self.metadata_manager.stripe_source_sector_offset(stripe_id);
            let stripe_sector_count = self
                .metadata_manager
                .stripe_sector_count()
                .min(self.source_sector_count - stripe_sector_offset);

            self.fetch_source_channel.add_read(
                stripe_sector_offset,
                stripe_sector_count as u32,
                buf.clone(),
                buffer_idx,
            );

            if let Err(e) = self.fetch_source_channel.submit() {
                error!("Failed to submit read for stripe {}: {:?}", stripe_id, e);
                self.fetch_completed(buffer_idx, false);
                result.push((stripe_id, false));
                continue;
            }

            self.metadata_manager
                .set_stripe_status(stripe_id, StripeStatus::Fetching);
        }

        result
    }

    pub fn finish_flush(&mut self, success: bool) {
        debug!("Finishing flush, success={}", success);
        self.inprogress_flush_requests = 0;
    }

    pub fn update(&mut self) {
        self.receive_requests();

        let mut completed_fetches = self.start_fetches();
        completed_fetches.append(&mut self.poll_fetches());

        if let Some(success) = self.metadata_manager.poll_flush() {
            self.finish_flush(success);
        }

        if self.pending_flush_requests > 0 && self.inprogress_flush_requests == 0 {
            self.inprogress_flush_requests = self.pending_flush_requests;
            self.pending_flush_requests = 0;

            match self.metadata_manager.start_flush() {
                Ok(StartFlushResult::NoChanges) => {
                    self.finish_flush(true);
                }
                Ok(StartFlushResult::Started) => {
                    debug!("Flush started");
                }
                Err(e) => {
                    error!("Failed to start flush: {:?}", e);
                    self.finish_flush(false);
                }
            }
        }
    }

    pub fn run(&mut self) {
        loop {
            self.update();

            if self.killfd.read().is_ok() {
                info!("Received kill signal, shutting down");
                break;
            }

            std::thread::sleep(std::time::Duration::from_millis(1));
        }
    }

    pub fn stripe_status_vec(&self) -> StripeStatusVec {
        self.metadata_manager.stripe_status_vec()
    }
}

unsafe impl Send for StripeFetcher {}
unsafe impl Sync for StripeFetcher {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block_device::bdev_lazy::{init_metadata, stripe_metadata_manager::UbiMetadata};
    use crate::block_device::bdev_test::TestBlockDevice;
    use crate::vhost_backend::SECTOR_SIZE;
    use crate::VhostUserBlockError;
    #[test]
    fn test_stripe_fetcher() {
        let stripe_sector_count_shift = 12;
        let stripe_size = (1u64 << stripe_sector_count_shift) * SECTOR_SIZE as u64;
        let source_dev = TestBlockDevice::new(29 * stripe_size + 3 * 1024);
        let target_dev = TestBlockDevice::new(29 * stripe_size + 3 * 1024);
        let metadata_dev = TestBlockDevice::new(8 * 1024 * 1024);

        let mut ch = metadata_dev
            .create_channel()
            .expect("Failed to create channel");
        let metadata = UbiMetadata::new(stripe_sector_count_shift);
        init_metadata(&metadata, &mut ch).unwrap();

        let killfd = EventFd::new(0).unwrap();
        let mut stripe_fetcher =
            StripeFetcher::new(&source_dev, &target_dev, &metadata_dev, killfd, 512).unwrap();

        let req_sender = stripe_fetcher.req_sender();

        let buf1 = "some test data".as_bytes();
        let buf2 = "some more test data".as_bytes();
        let mut buf3 = vec![0u8; 64];

        {
            let metadata_manager = &stripe_fetcher.metadata_manager;

            source_dev.write(
                metadata_manager.stripe_source_sector_offset(0) as usize * SECTOR_SIZE,
                buf1,
                buf1.len(),
            );
            source_dev.write(
                metadata_manager.stripe_source_sector_offset(3) as usize * SECTOR_SIZE,
                buf2,
                buf2.len(),
            );

            // before fetch, contents shouldn't be the same
            target_dev.read(
                metadata_manager.stripe_target_sector_offset(0) as usize * SECTOR_SIZE,
                &mut buf3,
                64,
            );
            assert_ne!(&buf3[..buf1.len()], buf1);
            target_dev.read(
                metadata_manager.stripe_target_sector_offset(3) as usize * SECTOR_SIZE,
                &mut buf3,
                64,
            );
            assert_ne!(&buf3[..buf2.len()], buf2);
        }

        // request fetch
        req_sender.send(StripeFetcherRequest::Fetch(0)).unwrap();
        req_sender.send(StripeFetcherRequest::Fetch(3)).unwrap();

        while stripe_fetcher.metadata_manager.stripe_status(0) != StripeStatus::Fetched
            || stripe_fetcher.metadata_manager.stripe_status(3) != StripeStatus::Fetched
        {
            stripe_fetcher.update();
        }

        {
            let metadata_manager = &stripe_fetcher.metadata_manager;

            // after fetch, contents should be the same
            target_dev.read(
                metadata_manager.stripe_target_sector_offset(0) as usize * SECTOR_SIZE,
                &mut buf3,
                64,
            );
            assert_eq!(&buf3[..buf1.len()], buf1);
            target_dev.read(
                metadata_manager.stripe_target_sector_offset(3) as usize * SECTOR_SIZE,
                &mut buf3,
                64,
            );
            assert_eq!(&buf3[..buf2.len()], buf2);
        }

        // request flush
        req_sender
            .send(StripeFetcherRequest::FlushMetadata)
            .unwrap();

        while stripe_fetcher
            .metadata_manager
            .shared_flush_state()
            .needs_flush()
        {
            stripe_fetcher.update();
        }
    }

    #[test]
    fn test_target_device_too_small() {
        let source_dev = TestBlockDevice::new(4 * 1024 * 1024);
        let target_dev = TestBlockDevice::new(2 * 1024 * 1024);
        let metadata_dev = TestBlockDevice::new(8 * 1024 * 1024);

        let stripe_sector_count_shift = 11;
        let mut ch = metadata_dev
            .create_channel()
            .expect("Failed to create channel");
        let metadata = UbiMetadata::new(stripe_sector_count_shift);
        init_metadata(&metadata, &mut ch).unwrap();

        let killfd = EventFd::new(0).unwrap();
        let res = StripeFetcher::new(&source_dev, &target_dev, &metadata_dev, killfd, 512);
        match res {
            Err(VhostUserBlockError::InvalidParameter { description }) => {
                assert_eq!(description, "target device too small");
            }
            _ => panic!("Expected InvalidParameter error"),
        }
    }

    #[test]
    fn test_consecutive_flushes() {
        let stripe_shift = 12u8;
        let stripe_size = (1u64 << stripe_shift) * SECTOR_SIZE as u64;
        let source_dev = TestBlockDevice::new(4 * stripe_size);
        let target_dev = TestBlockDevice::new(4 * stripe_size);
        let metadata_dev = TestBlockDevice::new(8 * 1024 * 1024);

        let mut ch = metadata_dev
            .create_channel()
            .expect("Failed to create channel");
        let metadata = UbiMetadata::new(stripe_shift);
        init_metadata(&metadata, &mut ch).unwrap();

        let killfd = EventFd::new(0).unwrap();
        let mut stripe_fetcher =
            StripeFetcher::new(&source_dev, &target_dev, &metadata_dev, killfd, 512).unwrap();

        let req_sender = stripe_fetcher.req_sender();

        // First flush should persist initial metadata changes
        req_sender
            .send(StripeFetcherRequest::FlushMetadata)
            .unwrap();
        while stripe_fetcher
            .metadata_manager
            .shared_flush_state()
            .needs_flush()
        {
            stripe_fetcher.update();
        }
        assert!(stripe_fetcher.pending_flush_requests == 0);
        assert!(stripe_fetcher.inprogress_flush_requests == 0);

        // Second flush should succeed even with no changes
        req_sender
            .send(StripeFetcherRequest::FlushMetadata)
            .unwrap();
        stripe_fetcher.update();
        assert!(stripe_fetcher.pending_flush_requests == 0);
        assert!(stripe_fetcher.inprogress_flush_requests == 0);
        assert!(!stripe_fetcher
            .metadata_manager
            .shared_flush_state()
            .needs_flush());
    }
}
