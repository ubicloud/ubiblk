use super::{
    metadata::shared_state::SharedMetadataState, metadata_flusher::MetadataFlusher,
    stripe_fetcher::StripeFetcher,
};

use crate::{block_device::BlockDevice, stripe_source::StripeSource, Result};
use log::{error, info};
use std::sync::mpsc::{Receiver, TryRecvError};

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
        stripe_source: Box<dyn StripeSource>,
        target_dev: &dyn BlockDevice,
        metadata_dev: &dyn BlockDevice,
        alignment: usize,
        autofetch: bool,
        metadata_state: SharedMetadataState,
        req_receiver: Receiver<BgWorkerRequest>,
    ) -> Result<Self> {
        let source_sector_count = stripe_source.sector_count();
        let metadata_flusher =
            MetadataFlusher::new(metadata_dev, source_sector_count, metadata_state.clone())?;
        let stripe_fetcher = StripeFetcher::new(
            stripe_source,
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
                #[cfg(feature = "tla-trace")]
                crate::tla_trace::log_action("Handoff", serde_json::json!({
                    "stripe": stripe_id,
                }));
                self.metadata_flusher.set_stripe_fetched(stripe_id);
            } else {
                error!("Stripe {stripe_id} fetch failed");
            }
        }
        self.metadata_flusher.update();
        self.stripe_fetcher.disconnect_from_source_if_all_fetched();
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
    use crate::{
        block_device::{
            bdev_lazy::SharedMetadataState, bdev_test::TestBlockDevice, NullBlockDevice,
            UbiMetadata,
        },
        stripe_source,
    };
    use std::sync::mpsc::channel;

    fn build_bg_worker_with_source(
        stripe_source: Box<dyn StripeSource>,
    ) -> (BgWorker, std::sync::mpsc::Sender<BgWorkerRequest>) {
        let stripe_sector_count_shift = 11;
        let target_dev = TestBlockDevice::new(1024 * 1024);
        let metadata_dev = TestBlockDevice::new(1024 * 1024);
        let metadata = UbiMetadata::new(stripe_sector_count_shift, 16, 16);
        metadata.save_to_bdev(&metadata_dev).unwrap();
        let metadata_state = {
            let metadata = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
            SharedMetadataState::new(&metadata)
        };

        let (tx, rx) = channel();

        (
            BgWorker::new(
                stripe_source,
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

    fn build_bg_worker() -> (BgWorker, std::sync::mpsc::Sender<BgWorkerRequest>) {
        let stripe_sector_count_shift = 11;
        let stripe_sector_count = 1u64 << stripe_sector_count_shift;
        let source_dev = TestBlockDevice::new(1024 * 1024);
        let stripe_source = Box::new(
            stripe_source::BlockDeviceStripeSource::new(source_dev.clone(), stripe_sector_count)
                .unwrap(),
        );
        build_bg_worker_with_source(stripe_source)
    }

    #[test]
    fn test_bg_worker_shutdown() {
        let (mut bg_worker, sender) = build_bg_worker();
        sender.send(BgWorkerRequest::Shutdown).unwrap();
        bg_worker.run();
    }

    #[test]
    fn bg_worker_supports_null_source() {
        let stripe_sector_count_shift = 11;
        let stripe_sector_count = 1u64 << stripe_sector_count_shift;
        let source_dev = NullBlockDevice::new();
        let target_dev = TestBlockDevice::new(1024 * 1024);
        let metadata_dev = TestBlockDevice::new(1024 * 1024);
        let stripe_source = Box::new(
            stripe_source::BlockDeviceStripeSource::new(source_dev, stripe_sector_count).unwrap(),
        );

        let metadata = UbiMetadata::new(stripe_sector_count_shift, 16, 0);
        metadata.save_to_bdev(&metadata_dev).unwrap();

        let metadata_state = {
            let metadata = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
            SharedMetadataState::new(&metadata)
        };

        let (_tx, rx) = channel();

        BgWorker::new(
            stripe_source,
            &target_dev,
            &metadata_dev,
            4096,
            false,
            metadata_state,
            rx,
        )
        .expect("BgWorker should support null source device");
    }

    #[test]
    #[cfg(feature = "tla-trace")]
    fn test_tla_trace_full_pipeline() {
        let trace_path = std::env::temp_dir().join("tla_trace_test.ndjson");
        crate::tla_trace::init(trace_path.to_str().unwrap());

        let (mut bg_worker, sender) = build_bg_worker();
        sender
            .send(BgWorkerRequest::Fetch { stripe_id: 0 })
            .unwrap();
        bg_worker.receive_requests(false);

        for _ in 0..100 {
            bg_worker.update();
        }

        assert!(bg_worker.shared_state().stripe_fetched(0));

        // Read and verify the trace
        let trace_content = std::fs::read_to_string(&trace_path).unwrap();
        let actions: Vec<serde_json::Value> = trace_content
            .lines()
            .map(|l| serde_json::from_str(l).unwrap())
            .collect();

        let action_names: Vec<&str> = actions
            .iter()
            .map(|a| a["action"].as_str().unwrap())
            .collect();

        // Verify the full pipeline sequence for stripe 0
        assert_eq!(
            action_names,
            vec![
                "SourceReadComplete",
                "TargetWriteComplete",
                "TargetFlushComplete",
                "Handoff",
                "MetadataWriteComplete",
                "MetadataFlushComplete",
                "AtomicPublish",
            ],
            "Expected full pipeline trace, got: {:?}",
            action_names
        );

        // Verify all actions reference stripe 0
        for action in &actions {
            assert_eq!(action["stripe"].as_u64().unwrap(), 0);
        }

        std::fs::remove_file(&trace_path).ok();
    }

    #[test]
    #[cfg(feature = "tla-trace")]
    fn test_tla_trace_failed_stripe() {
        let trace_path = std::env::temp_dir().join("tla_trace_failed_test.ndjson");
        crate::tla_trace::init(trace_path.to_str().unwrap());

        let stripe_sector_count_shift = 11;
        let stripe_sector_count = 1u64 << stripe_sector_count_shift;
        let source_dev = TestBlockDevice::new(1024 * 1024);
        let base_source =
            stripe_source::BlockDeviceStripeSource::new(source_dev.clone(), stripe_sector_count)
                .unwrap();
        let flaky_source =
            stripe_source::FlakyStripeSource::new(Box::new(base_source), vec![(0, 4)]);

        let (mut bg_worker, sender) = build_bg_worker_with_source(Box::new(flaky_source));
        sender
            .send(BgWorkerRequest::Fetch { stripe_id: 0 })
            .unwrap();
        bg_worker.receive_requests(false);

        for _ in 0..100 {
            bg_worker.update();
        }

        assert!(bg_worker.shared_state().is_stripe_failed(0));

        let trace_content = std::fs::read_to_string(&trace_path).unwrap();
        let actions: Vec<serde_json::Value> = trace_content
            .lines()
            .map(|l| serde_json::from_str(l).unwrap())
            .collect();

        let action_names: Vec<&str> = actions
            .iter()
            .map(|a| a["action"].as_str().unwrap())
            .collect();

        // Should end with SetFailed
        assert_eq!(
            *action_names.last().unwrap(),
            "SetFailed",
            "Expected SetFailed as last action, got: {:?}",
            action_names
        );

        std::fs::remove_file(&trace_path).ok();
    }

    #[test]
    fn bg_worker_marks_failed_stripes_with_flaky_source() {
        let stripe_sector_count_shift = 11;
        let stripe_sector_count = 1u64 << stripe_sector_count_shift;
        let source_dev = TestBlockDevice::new(1024 * 1024);
        let base_source =
            stripe_source::BlockDeviceStripeSource::new(source_dev.clone(), stripe_sector_count)
                .unwrap();
        let flaky_source =
            stripe_source::FlakyStripeSource::new(Box::new(base_source), vec![(0, 4)]);

        let (mut bg_worker, sender) = build_bg_worker_with_source(Box::new(flaky_source));
        sender
            .send(BgWorkerRequest::Fetch { stripe_id: 0 })
            .unwrap();
        bg_worker.receive_requests(false);

        for _ in 0..100 {
            bg_worker.update();
        }

        assert!(bg_worker.shared_state().is_stripe_failed(0));
    }
}
