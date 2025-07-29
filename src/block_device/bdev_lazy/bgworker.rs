use super::{
    metadata_flusher::{MetadataFlushState, MetadataFlusher},
    stripe_fetcher::{StripeFetcher, StripeStatusVec},
};
use crate::block_device::BlockDevice;
use crate::Result;
use log::info;
use std::sync::{
    mpsc::{Receiver, Sender},
    Arc, Mutex,
};
use vmm_sys_util::eventfd::EventFd;

pub enum BgWorkerRequest {
    Fetch(usize),
    FlushMetadata,
}

pub struct BgWorker {
    stripe_fetcher: StripeFetcher,
    metadata_flusher: MetadataFlusher,
    req_receiver: Receiver<BgWorkerRequest>,
    req_sender: Sender<BgWorkerRequest>,
    killfd: EventFd,
}

pub type SharedBgWorker = Arc<Mutex<BgWorker>>;

impl BgWorker {
    pub fn new(
        source_dev: &dyn BlockDevice,
        target_dev: &dyn BlockDevice,
        metadata_dev: &dyn BlockDevice,
        killfd: EventFd,
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
            killfd,
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

    fn receive_requests(&mut self) {
        while let Ok(req) = self.req_receiver.try_recv() {
            match req {
                BgWorkerRequest::Fetch(id) => self.stripe_fetcher.handle_fetch_request(id),
                BgWorkerRequest::FlushMetadata => self.metadata_flusher.request_flush(),
            }
        }
    }

    pub fn update(&mut self) {
        self.receive_requests();
        let completed = self.stripe_fetcher.update();
        for (stripe_id, success) in completed {
            if success {
                self.metadata_flusher.set_stripe_fetched(stripe_id);
            }
        }
        self.metadata_flusher.update();
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
}

