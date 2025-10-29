use super::{
    metadata::SharedMetadataState, metadata_flusher::MetadataFlusher, stripe_fetcher::StripeFetcher,
};
use crate::block_device::BlockDevice;
use crate::Result;
use log::{error, info};
use serde::{Deserialize, Serialize};
use std::sync::mpsc::{Receiver, TryRecvError};

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
struct StripesRecord {
    total: u64,
    no_source: u64,
    fetched: u64,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct StatusReport {
    stripes: StripesRecord,
}

impl StatusReport {
    pub fn new(total: u64, no_source: u64, fetched: u64) -> Self {
        StatusReport {
            stripes: StripesRecord {
                total,
                no_source,
                fetched,
            },
        }
    }

    pub fn from_shared_state(shared_state: &SharedMetadataState) -> Self {
        StatusReport::new(
            shared_state.stripe_count() as u64,
            shared_state.no_source_stripes(),
            shared_state.fetched_stripes(),
        )
    }
}

pub enum BgWorkerRequest {
    Fetch { stripe_id: usize },
    SetWritten { stripe_id: usize },
    Shutdown,
}

pub struct BgWorker {
    stripe_fetcher: StripeFetcher,
    metadata_flusher: MetadataFlusher,
    req_receiver: Receiver<BgWorkerRequest>,
    metadata_state: SharedMetadataState,
    done: bool,
}

impl BgWorker {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        source_dev: &dyn BlockDevice,
        target_dev: &dyn BlockDevice,
        metadata_dev: &dyn BlockDevice,
        alignment: usize,
        autofetch: bool,
        metadata_state: SharedMetadataState,
        req_receiver: Receiver<BgWorkerRequest>,
    ) -> Result<Self> {
        let source_sector_count = source_dev.sector_count();
        let metadata_flusher =
            MetadataFlusher::new(metadata_dev, source_sector_count, metadata_state.clone())?;
        let stripe_fetcher = StripeFetcher::new(
            source_dev,
            target_dev,
            metadata_state.stripe_sector_count(),
            metadata_state.clone(),
            alignment,
            autofetch,
        )?;
        Ok(BgWorker {
            stripe_fetcher,
            metadata_flusher,
            req_receiver,
            done: false,
            metadata_state,
        })
    }

    pub fn shared_state(&self) -> SharedMetadataState {
        self.metadata_state.clone()
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block_device::{
        bdev_lazy::SharedMetadataState, bdev_test::TestBlockDevice, init_metadata, load_metadata,
        NullBlockDevice, UbiMetadata,
    };
    use std::sync::mpsc::channel;

    fn build_bg_worker() -> (BgWorker, std::sync::mpsc::Sender<BgWorkerRequest>) {
        let source_dev = TestBlockDevice::new(1024 * 1024);
        let target_dev = TestBlockDevice::new(1024 * 1024);
        let metadata_dev = TestBlockDevice::new(1024 * 1024);
        init_metadata(
            &UbiMetadata::new(11, 16, 16),
            &mut metadata_dev.create_channel().unwrap(),
        )
        .expect("Failed to initialize metadata");

        let metadata_state = {
            let mut channel = metadata_dev.create_channel().unwrap();
            let metadata = load_metadata(&mut channel, metadata_dev.sector_count()).unwrap();
            SharedMetadataState::new(&metadata)
        };

        let (tx, rx) = channel();

        (
            BgWorker::new(
                &source_dev,
                &target_dev,
                &metadata_dev,
                4096,
                false,
                metadata_state,
                rx,
            )
            .unwrap(),
            tx,
        )
    }

    #[test]
    fn test_bg_worker_shutdown() {
        let (mut bg_worker, sender) = build_bg_worker();
        sender.send(BgWorkerRequest::Shutdown).unwrap();
        bg_worker.run();
    }

    #[test]
    fn bg_worker_supports_null_source() {
        let source_dev = NullBlockDevice::new();
        let target_dev = TestBlockDevice::new(1024 * 1024);
        let metadata_dev = TestBlockDevice::new(1024 * 1024);
        init_metadata(
            &UbiMetadata::new(11, 16, 0),
            &mut metadata_dev.create_channel().unwrap(),
        )
        .expect("Failed to initialize metadata");

        let metadata_state = {
            let mut channel = metadata_dev.create_channel().unwrap();
            let metadata = load_metadata(&mut channel, metadata_dev.sector_count()).unwrap();
            SharedMetadataState::new(&metadata)
        };

        let (_tx, rx) = channel();

        BgWorker::new(
            &*source_dev,
            &target_dev,
            &metadata_dev,
            4096,
            false,
            metadata_state,
            rx,
        )
        .expect("BgWorker should support null source device");
    }
}
