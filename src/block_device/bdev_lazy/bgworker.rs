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
    Fetch { stripe_id: usize },
    SetWritten { stripe_id: usize },
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
        let source_sector_count = source_dev.sector_count();
        let metadata_flusher = MetadataFlusher::new(metadata_dev, source_sector_count)?;
        let stripe_fetcher = StripeFetcher::new(
            source_dev,
            target_dev,
            metadata_flusher.stripe_sector_count(),
            metadata_flusher.shared_state(),
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

    pub fn shared_state(&self) -> SharedMetadataState {
        self.metadata_flusher.shared_state()
    }

    pub fn process_request(&mut self, req: BgWorkerRequest) {
        match req {
            BgWorkerRequest::Fetch { stripe_id } => {
                self.stripe_fetcher.handle_fetch_request(stripe_id)
            }
            BgWorkerRequest::SetWritten { stripe_id } => {
                self.metadata_flusher.set_stripe_written(stripe_id)
            }
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
        for (stripe_id, success) in self.stripe_fetcher.take_finished_fetches() {
            if success {
                self.metadata_flusher.set_stripe_fetched(stripe_id);
            } else {
                error!("Stripe {stripe_id} fetch failed");
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block_device::{bdev_test::TestBlockDevice, init_metadata, UbiMetadata};

    fn build_bg_worker() -> BgWorker {
        let source_dev = TestBlockDevice::new(1024 * 1024);
        let target_dev = TestBlockDevice::new(1024 * 1024);
        let metadata_dev = TestBlockDevice::new(1024 * 1024);
        init_metadata(
            &UbiMetadata::new(11, 16, 16),
            &mut metadata_dev.create_channel().unwrap(),
        )
        .expect("Failed to initialize metadata");

        BgWorker::new(&source_dev, &target_dev, &metadata_dev, 4096).unwrap()
    }

    #[test]
    fn test_bg_worker_shutdown() {
        let mut bg_worker = build_bg_worker();
        let sender = bg_worker.req_sender();
        sender.send(BgWorkerRequest::Shutdown).unwrap();
        bg_worker.run();
    }
}
