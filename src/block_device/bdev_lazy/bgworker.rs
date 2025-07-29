use super::{
    metadata_flusher::{MetadataFlushState, MetadataFlusher},
    stripe_fetcher::{StripeFetcher, StripeStatusVec},
};
use crate::block_device::BlockDevice;
use crate::Result;
use log::{error, info};
use std::sync::{
    mpsc::{Receiver, Sender},
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
        let metadata_flusher = MetadataFlusher::new(metadata_dev)?;
        let stripe_sector_count = metadata_flusher.stripe_sector_count();
        let stripe_status_vec =
            StripeStatusVec::new(metadata_flusher.metadata(), source_dev.sector_count())?;
        let stripe_fetcher = StripeFetcher::new(
            source_dev,
            target_dev,
            stripe_sector_count,
            stripe_status_vec,
            alignment,
        )?;
        let (tx, rx) = std::sync::mpsc::channel();
        Ok(BgWorker {
            stripe_fetcher,
            metadata_flusher,
            req_receiver: rx,
            req_sender: tx,
            done: false,
        })
    }

    pub fn req_sender(&self) -> Sender<BgWorkerRequest> {
        self.req_sender.clone()
    }

    pub fn stripe_status_vec(&self) -> StripeStatusVec {
        self.stripe_fetcher.stripe_status_vec()
    }

    pub fn shared_flush_state(&self) -> MetadataFlushState {
        self.metadata_flusher.shared_flush_state()
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

        while let Ok(req) = self.req_receiver.try_recv() {
            self.process_request(req);
        }
    }

    pub fn update(&mut self) {
        let completed = self.stripe_fetcher.update();
        for (stripe_id, success) in completed {
            if success {
                self.metadata_flusher.set_stripe_fetched(stripe_id);
            }
        }
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
