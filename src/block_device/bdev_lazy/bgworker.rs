use super::{
    metadata::SharedMetadataState, metadata_flusher::MetadataFlusher, stripe_fetcher::StripeFetcher,
};
use crate::block_device::BlockDevice;
use crate::Result;
use log::{error, info};
use std::sync::{
    mpsc::{Receiver, Sender, TryRecvError},
    Arc, Mutex,
};

pub enum BgWorkerRequest {
    Fetch(usize),
    FlushMetadata,
    Shutdown,
}

pub struct BgWorker {
    stripe_fetcher: StripeFetcher,
    metadata_flusher: MetadataFlusher,
    stripe_sector_count: u64,
    req_receiver: Receiver<BgWorkerRequest>,
    req_sender: Sender<BgWorkerRequest>,
    done: bool,
}

pub type SharedBgWorker = Arc<Mutex<BgWorker>>;

impl BgWorker {
    pub fn new(
        source_dev: &dyn BlockDevice,
        target_dev: &dyn BlockDevice,
        metadata_dev: &dyn BlockDevice,
        alignment: usize,
    ) -> Result<Self> {
        let source_sector_count = source_dev.sector_count();
        let metadata_flusher = MetadataFlusher::new(metadata_dev, source_sector_count)?;
        let stripe_sector_count = metadata_flusher.stripe_sector_count();
        let shared_state = metadata_flusher.shared_state();
        let stripe_fetcher = StripeFetcher::new(
            source_dev,
            target_dev,
            stripe_sector_count,
            shared_state,
            alignment,
        )?;
        let (tx, rx) = std::sync::mpsc::channel();
        Ok(BgWorker {
            stripe_fetcher,
            metadata_flusher,
            stripe_sector_count,
            req_receiver: rx,
            req_sender: tx,
            done: false,
        })
    }

    pub fn stripe_sector_count(&self) -> u64 {
        self.stripe_sector_count
    }

    pub fn req_sender(&self) -> Sender<BgWorkerRequest> {
        self.req_sender.clone()
    }

    pub fn shared_state(&self) -> SharedMetadataState {
        self.metadata_flusher.shared_state()
    }

    pub fn process_request(&mut self, req: BgWorkerRequest) {
        match req {
            BgWorkerRequest::Fetch(id) => self.stripe_fetcher.handle_fetch_request(id),
            BgWorkerRequest::FlushMetadata => self.metadata_flusher.request_flush(),
            BgWorkerRequest::Shutdown => {
                info!("Received shutdown request, stopping worker");
                self.done = true;
            }
        }
    }

    pub fn receive_requests(&mut self, block: bool) {
        if block {
            match self.req_receiver.recv() {
                Ok(req) => self.process_request(req),
                Err(e) => {
                    error!("Failed to receive request: {e}, stopping worker");
                    self.done = true;
                    return;
                }
            }
        }

        loop {
            match self.req_receiver.try_recv() {
                Ok(req) => self.process_request(req),
                Err(TryRecvError::Disconnected) => {
                    error!("Request channel disconnected, stopping worker");
                    self.done = true;
                    return;
                }
                Err(TryRecvError::Empty) => break,
            }
        }
    }

    pub fn update(&mut self) {
        self.stripe_fetcher.update();
        self.metadata_flusher.update();
    }

    pub fn run(&mut self) {
        while !self.done {
            let busy = self.stripe_fetcher.busy() || self.metadata_flusher.busy();
            let block = !busy;
            self.receive_requests(block);
            self.update();
        }
    }
}

unsafe impl Send for BgWorker {}
unsafe impl Sync for BgWorker {}
