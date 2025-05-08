use std::collections::{HashMap, VecDeque};
use std::sync::mpsc::{Receiver, Sender};
use std::sync::{Arc, Mutex};
use std::{cell::RefCell, rc::Rc};

use super::super::*;
pub use super::stripe_metadata_manager::{StripeMetadataManager, StripeStatus, StripeStatusVec};
use crate::Result;
use log::{debug, error, info};
use vmm_sys_util::eventfd::EventFd;

#[derive(Debug)]
pub enum StripeFetcherRequest {
    Fetch(usize),
    Flush(usize),
}

#[derive(Debug)]
pub enum StripeFetcherResponse {
    Fetch(usize, bool),
    Flush(usize, bool),
}

const MAX_CONCURRENT_FETCHES: usize = 16;
const STRIPE_SIZE: usize = 1024 * 1024; // 1MB

pub type SharedStripeFetcher = Arc<Mutex<StripeFetcher>>;

#[derive(Clone)]
struct FetchBuffer {
    used_for: Option<usize>,
    buf: SharedBuffer,
}

pub struct StripeFetcher {
    fetch_source_channel: Box<dyn IoChannel>,
    fetch_target_channel: Box<dyn IoChannel>,
    metadata_manager: Box<StripeMetadataManager>,
    fetch_queue: VecDeque<usize>,
    stripe_requesters: HashMap<usize, Vec<Sender<StripeFetcherResponse>>>,
    req_mpsc_pairs: Vec<(
        Sender<StripeFetcherResponse>,
        Receiver<StripeFetcherRequest>,
    )>,
    fetch_buffers: Vec<FetchBuffer>,
    stripes_fetched: usize,
    pending_flush_requests: Vec<(Sender<StripeFetcherResponse>, usize)>,
    inprogress_flush_requests: Vec<(Sender<StripeFetcherResponse>, usize)>,
    killfd: EventFd,
}

impl StripeFetcher {
    pub fn new(
        source: &dyn BlockDevice,
        target: &dyn BlockDevice,
        killfd: EventFd,
    ) -> Result<Self> {
        let fetch_source_channel = source.create_channel()?;
        let fetch_target_channel = target.create_channel()?;
        let metadata_manager = StripeMetadataManager::new(source, target)?;
        let fetch_buffers = (0..MAX_CONCURRENT_FETCHES)
            .map(|_| FetchBuffer {
                used_for: None,
                buf: Rc::new(RefCell::new(vec![0u8; STRIPE_SIZE])),
            })
            .collect();
        Ok(StripeFetcher {
            fetch_source_channel,
            fetch_target_channel,
            metadata_manager,
            fetch_queue: VecDeque::new(),
            stripe_requesters: HashMap::new(),
            req_mpsc_pairs: vec![],
            fetch_buffers: fetch_buffers,
            stripes_fetched: 0,
            pending_flush_requests: vec![],
            inprogress_flush_requests: vec![],
            killfd,
        })
    }

    pub fn add_req_mpsc_pair(
        &mut self,
        sender: Sender<StripeFetcherResponse>,
        receiver: Receiver<StripeFetcherRequest>,
    ) {
        self.req_mpsc_pairs.push((sender, receiver));
    }

    pub fn handle_fetch_request(
        &mut self,
        stripe_id: usize,
        sender: Sender<StripeFetcherResponse>,
    ) {
        match self.metadata_manager.stripe_status(stripe_id) {
            StripeStatus::NotFetched => {
                debug!("Enqueueing stripe {} for fetch", stripe_id);
                self.fetch_queue.push_back(stripe_id);
                self.metadata_manager
                    .set_stripe_status(stripe_id, StripeStatus::Queued);
                self.stripe_requesters
                    .insert(stripe_id, vec![sender.clone()]);
            }
            StripeStatus::Fetched => {
                debug!("Stripe {} already fetched", stripe_id);
                sender
                    .send(StripeFetcherResponse::Fetch(stripe_id, true))
                    .unwrap();
            }
            StripeStatus::Queued | StripeStatus::Fetching => {
                debug!("Stripe {} is already queued or fetching", stripe_id);
                self.stripe_requesters
                    .entry(stripe_id)
                    .or_insert_with(Vec::new)
                    .push(sender.clone());
            }
        }
    }

    fn handle_flush_request(&mut self, flush_id: usize, sender: Sender<StripeFetcherResponse>) {
        self.pending_flush_requests.push((sender.clone(), flush_id));
    }

    fn receive_requests(&mut self) {
        let mut requests = Vec::new();
        for (sender, receiver) in self.req_mpsc_pairs.iter() {
            if let Ok(request) = receiver.try_recv() {
                debug!("Received request: {:?}", request);
                requests.push((request, sender.clone()));
            }
        }

        for (request, sender) in requests {
            match request {
                StripeFetcherRequest::Fetch(stripe_id) => {
                    self.handle_fetch_request(stripe_id, sender);
                }
                StripeFetcherRequest::Flush(flush_id) => {
                    self.handle_flush_request(flush_id, sender);
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
                .set_stripe_status(stripe_id, StripeStatus::NotFetched);
        }
    }

    fn start_write(&mut self, buffer_idx: usize) -> bool {
        let fetch_buffer = &mut self.fetch_buffers[buffer_idx];
        let stripe_id = fetch_buffer.used_for.unwrap();
        let buf = fetch_buffer.buf.clone();
        let stripe_sector_count = self.metadata_manager.stripe_sector_count(stripe_id);
        let stripe_sector_offset = self.metadata_manager.stripe_target_sector_offset(stripe_id);

        self.fetch_target_channel.add_write(
            stripe_sector_offset as u64,
            stripe_sector_count,
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
            let stripe_sector_count = self.metadata_manager.stripe_sector_count(stripe_id);
            let stripe_sector_offset = self.metadata_manager.stripe_source_sector_offset(stripe_id);

            self.fetch_source_channel.add_read(
                stripe_sector_offset,
                stripe_sector_count,
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
        for (sender, flush_id) in self.inprogress_flush_requests.drain(..) {
            if let Err(e) = sender.send(StripeFetcherResponse::Flush(flush_id, success)) {
                error!("Failed to send flush response: {:?}", e);
            }
        }
    }

    pub fn update(&mut self) {
        self.receive_requests();

        let mut completed_fetches = self.start_fetches();
        completed_fetches.append(&mut self.poll_fetches());

        for (stripe_id, success) in completed_fetches {
            if let Some(requesters) = self.stripe_requesters.remove(&stripe_id) {
                for requester in requesters {
                    if let Err(e) = requester.send(StripeFetcherResponse::Fetch(stripe_id, success))
                    {
                        error!("Failed to send response for stripe {}: {:?}", stripe_id, e);
                    }
                }
            }
        }

        if let Some(success) = self.metadata_manager.poll_flush() {
            self.finish_flush(success);
        }

        if self.pending_flush_requests.len() > 0 && self.inprogress_flush_requests.is_empty() {
            self.inprogress_flush_requests = self.pending_flush_requests.clone();
            self.pending_flush_requests.clear();

            if let Err(e) = self.metadata_manager.start_flush() {
                error!("Failed to start flush: {:?}", e);
                self.finish_flush(false);
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

    pub fn metadata_sector_count(&self) -> u64 {
        self.metadata_manager.metadata_sector_count()
    }
}

unsafe impl Send for StripeFetcher {}
unsafe impl Sync for StripeFetcher {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block_device::bdev_test::TestBlockDevice;
    use crate::vhost_backend::SECTOR_SIZE;

    #[test]
    fn test_stripe_fetcher() {
        let source = TestBlockDevice::new(29 * 1024 * 1024 + 3 * 1024);
        let target = TestBlockDevice::new(40 * 1024 * 1024);

        let killfd = EventFd::new(0).unwrap();
        let mut stripe_fetcher = StripeFetcher::new(&source, &target, killfd).unwrap();

        let (req_sender, req_receiver) = std::sync::mpsc::channel();
        let (resp_sender, resp_receiver) = std::sync::mpsc::channel();

        stripe_fetcher.add_req_mpsc_pair(resp_sender, req_receiver);

        let buf1 = "some test data".as_bytes();
        let buf2 = "some more test data".as_bytes();
        let mut buf3 = vec![0u8; 64];

        {
            let metadata_manager = &stripe_fetcher.metadata_manager;

            source.write(
                metadata_manager.stripe_source_sector_offset(0) as usize * SECTOR_SIZE,
                buf1,
                buf1.len(),
            );
            source.write(
                metadata_manager.stripe_source_sector_offset(3) as usize * SECTOR_SIZE,
                buf2,
                buf2.len(),
            );

            // before fetch, contents shouldn't be the same
            target.read(
                metadata_manager.stripe_target_sector_offset(0) as usize * SECTOR_SIZE,
                &mut buf3,
                64,
            );
            assert_ne!(&buf3[..buf1.len()], buf1);
            target.read(
                metadata_manager.stripe_target_sector_offset(3) as usize * SECTOR_SIZE,
                &mut buf3,
                64,
            );
            assert_ne!(&buf3[..buf2.len()], buf2);
        }

        // request fetch
        req_sender.send(StripeFetcherRequest::Fetch(0)).unwrap();
        req_sender.send(StripeFetcherRequest::Fetch(3)).unwrap();

        let mut completed = 0;
        while completed < 2 {
            stripe_fetcher.update();
            if let Ok(resp) = resp_receiver.try_recv() {
                match resp {
                    StripeFetcherResponse::Fetch(stripe_id, success) => {
                        assert!(success);
                        assert!(stripe_id == 0 || stripe_id == 3);
                        completed += 1;
                    }
                    _ => {}
                }
            }
        }

        {
            let metadata_manager = &stripe_fetcher.metadata_manager;

            // after fetch, contents should be the same
            target.read(
                metadata_manager.stripe_target_sector_offset(0) as usize * SECTOR_SIZE,
                &mut buf3,
                64,
            );
            assert_eq!(&buf3[..buf1.len()], buf1);
            target.read(
                metadata_manager.stripe_target_sector_offset(3) as usize * SECTOR_SIZE,
                &mut buf3,
                64,
            );
            assert_eq!(&buf3[..buf2.len()], buf2);
        }

        // request flush
        const NUM_FLUSHES: usize = 10;
        for i in 0..NUM_FLUSHES {
            req_sender.send(StripeFetcherRequest::Flush(i)).unwrap();
        }

        let mut completed = [false; NUM_FLUSHES];
        let mut flush_count = 0;
        while flush_count < NUM_FLUSHES {
            stripe_fetcher.update();
            if let Ok(resp) = resp_receiver.try_recv() {
                match resp {
                    StripeFetcherResponse::Flush(flush_id, success) => {
                        assert!(success);
                        assert!(flush_id < NUM_FLUSHES);
                        completed[flush_id] = true;
                        flush_count += 1;
                    }
                    _ => {}
                }
            }
        }

        for i in 0..NUM_FLUSHES {
            assert!(completed[i], "Flush {} was not completed", i);
        }
    }
}
