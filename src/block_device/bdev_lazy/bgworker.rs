use super::{
    metadata::SharedMetadataState, metadata_flusher::MetadataFlusher, stripe_fetcher::StripeFetcher,
};
use crate::block_device::BlockDevice;
use crate::Result;
use log::{error, info};
use serde::{Deserialize, Serialize};
use std::{
    io::Write,
    path::{Path, PathBuf},
    sync::mpsc::{Receiver, TryRecvError},
};
use tempfile::NamedTempFile;

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
struct StripesRecord {
    total: u64,
    no_source: u64,
    fetched: u64,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
struct StatusReport {
    stripes: StripesRecord,
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
    written_status: Option<StatusReport>,
    status_path: Option<PathBuf>,
    done: bool,
}

impl BgWorker {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        source_dev: &dyn BlockDevice,
        target_dev: &dyn BlockDevice,
        metadata_dev: &dyn BlockDevice,
        alignment: usize,
        status_path: Option<PathBuf>,
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
            written_status: None,
            status_path,
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
        self.write_status_if_needed();
    }

    fn write_status_if_needed(&mut self) {
        let Some(path) = &self.status_path else {
            return;
        };
        let status = StatusReport {
            stripes: StripesRecord {
                total: self.stripe_fetcher.target_stripe_count(),
                no_source: self.metadata_state.no_source_stripes(),
                fetched: self.metadata_state.fetched_stripes(),
            },
        };
        if self.written_status == Some(status) {
            return;
        }
        if let Err(e) = Self::write_status(path, &status) {
            error!("Failed to write status file {path:?}: {e}");
        } else {
            self.written_status = Some(status);
        }
    }

    fn write_status(path: &Path, status: &StatusReport) -> std::io::Result<()> {
        let mut tmp = NamedTempFile::new()?;
        let content = serde_json::to_vec_pretty(status)?;
        tmp.write_all(&content)?;
        tmp.flush()?;
        tmp.persist(path).map_err(|e| e.error)?;
        Ok(())
    }

    pub fn run(&mut self) {
        self.write_status_if_needed();

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
                None,
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
            None,
            false,
            metadata_state,
            rx,
        )
        .expect("BgWorker should support null source device");
    }
}
