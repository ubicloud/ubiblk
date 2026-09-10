use super::{
    metadata::shared_state::SharedMetadataState, metadata_flusher::MetadataFlusher,
    stripe_fetcher::StripeFetcher,
};

use crate::block_device::bgworker::BgTask;
use crate::{block_device::BlockDevice, stripe_source::StripeSource, Result};
use log::error;

pub enum LazyRequest {
    Fetch { stripe_id: usize },
    SetWritten { stripe_id: usize },
}

/// Fetching stripes and persisting what has been fetched, which is what a lazy
/// device has to do away from its I/O path.
pub struct LazyTask {
    stripe_fetcher: StripeFetcher,
    metadata_flusher: MetadataFlusher,
    metadata_state: SharedMetadataState,
}

impl BgTask for LazyTask {
    type Request = LazyRequest;

    fn handle(&mut self, request: LazyRequest) {
        match request {
            LazyRequest::Fetch { stripe_id } => self.stripe_fetcher.handle_fetch_request(stripe_id),
            LazyRequest::SetWritten { stripe_id } => {
                self.metadata_flusher.set_stripe_written(stripe_id)
            }
        }
    }

    fn update(&mut self) {
        self.stripe_fetcher.update();
        for (stripe_id, success) in self.stripe_fetcher.take_finished_fetches() {
            if success {
                self.metadata_flusher.set_stripe_fetched(stripe_id);
            } else {
                error!("Stripe {stripe_id} fetch failed");
            }
        }
        self.metadata_flusher.update();
        self.stripe_fetcher.disconnect_from_source_if_all_fetched();
    }

    fn busy(&self) -> bool {
        self.stripe_fetcher.busy() || self.metadata_flusher.busy()
    }
}

impl LazyTask {
    pub fn new(
        stripe_source: Box<dyn StripeSource>,
        target_dev: &dyn BlockDevice,
        metadata_dev: &dyn BlockDevice,
        alignment: usize,
        autofetch: bool,
        metadata_state: SharedMetadataState,
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
        Ok(LazyTask {
            stripe_fetcher,
            metadata_flusher,
            metadata_state,
        })
    }

    pub fn shared_state(&self) -> SharedMetadataState {
        self.metadata_state.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        block_device::{
            bdev_lazy::SharedMetadataState,
            bdev_test::TestBlockDevice,
            bgworker::{BgQueues, BgSender, BgStopper, BgWorker},
            NullBlockDevice, UbiMetadata,
        },
        stripe_source,
    };

    fn build_worker_with_source(
        stripe_source: Box<dyn StripeSource>,
    ) -> (
        BgWorker,
        BgStopper,
        BgSender<LazyRequest>,
        SharedMetadataState,
    ) {
        let stripe_sector_count_shift = 11;
        let target_dev = TestBlockDevice::new(1024 * 1024);
        let metadata_dev = TestBlockDevice::new(1024 * 1024);
        let metadata = UbiMetadata::new(stripe_sector_count_shift, 16, 16);
        metadata.save_to_bdev(&metadata_dev).unwrap();
        let metadata_state = {
            let metadata = UbiMetadata::load_from_bdev(&metadata_dev).expect("load metadata");
            SharedMetadataState::new(&metadata)
        };

        let task = LazyTask::new(
            stripe_source,
            &target_dev,
            &metadata_dev,
            4096,
            false,
            metadata_state.clone(),
        )
        .unwrap();

        let queues = BgQueues::new();
        let (sender, requests) = queues.queue();
        let stopper = queues.stopper();
        let mut worker = BgWorker::new(queues);
        worker.add(task, requests);

        (worker, stopper, sender, metadata_state)
    }

    fn build_worker() -> (
        BgWorker,
        BgStopper,
        BgSender<LazyRequest>,
        SharedMetadataState,
    ) {
        let stripe_sector_count_shift = 11;
        let stripe_sector_count = 1u64 << stripe_sector_count_shift;
        let source_dev = TestBlockDevice::new(1024 * 1024);
        let stripe_source = Box::new(
            stripe_source::BlockDeviceStripeSource::new(source_dev.clone(), stripe_sector_count)
                .unwrap(),
        );
        build_worker_with_source(stripe_source)
    }

    #[test]
    fn test_bg_worker_shutdown() {
        let (mut worker, stopper, sender, _) = build_worker();
        stopper.stop();
        // The worker stops because it was asked to, not because its queue ran
        // dry: the delayed drop is only there to keep a regression from
        // hanging the suite.
        std::thread::spawn(move || {
            std::thread::sleep(std::time::Duration::from_secs(2));
            drop(sender);
        });
        worker.run();
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

        LazyTask::new(
            stripe_source,
            &target_dev,
            &metadata_dev,
            4096,
            false,
            metadata_state,
        )
        .expect("LazyTask should support null source device");
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

        let (mut worker, _stopper, sender, metadata_state) =
            build_worker_with_source(Box::new(flaky_source));
        sender.send(LazyRequest::Fetch { stripe_id: 0 }).unwrap();
        worker.receive_requests(false);

        for _ in 0..100 {
            worker.update();
        }

        assert!(metadata_state.is_stripe_failed(0));
    }
}
