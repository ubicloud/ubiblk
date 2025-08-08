use std::{
    collections::{HashSet, VecDeque},
    sync::mpsc::Sender,
};

use super::super::*;
use super::bgworker::{BgWorkerRequest, SharedBgWorker};
use super::metadata::SharedMetadataState;
use crate::{block_device::SharedBuffer, Result, VhostUserBlockError};
use log::error;

#[derive(Debug)]
enum RequestType {
    In,
    Out,
}

struct RWRequest {
    id: usize,
    type_: RequestType,
    sector_offset: u64,
    sector_count: u32,
    buf: SharedBuffer,
    stripe_id_first: usize,
    stripe_id_last: usize,
}

struct FlushRequest {
    id: usize,
    pending_metadata_version: u64,
}

struct LazyIoChannel {
    base: Box<dyn IoChannel>,
    image: Option<Box<dyn IoChannel>>,
    queued_rw_requests: VecDeque<RWRequest>,
    queued_flush_requests: VecDeque<FlushRequest>,
    finished_requests: Vec<(usize, bool)>,
    bgworker_ch: Sender<BgWorkerRequest>,
    metadata_state: SharedMetadataState,
    stripe_fetches_requested: HashSet<usize>,
}

impl LazyIoChannel {
    fn new(
        base: Box<dyn IoChannel>,
        image: Option<Box<dyn IoChannel>>,
        bgworker_ch: Sender<BgWorkerRequest>,
        metadata_state: SharedMetadataState,
    ) -> Self {
        LazyIoChannel {
            base,
            image,
            queued_rw_requests: VecDeque::new(),
            queued_flush_requests: VecDeque::new(),
            finished_requests: Vec::new(),
            bgworker_ch,
            metadata_state,
            stripe_fetches_requested: HashSet::new(),
        }
    }
}

impl LazyIoChannel {
    fn request_stripes_fetched(&self, request: &RWRequest) -> bool {
        for stripe_id in request.stripe_id_first..=request.stripe_id_last {
            if !self.metadata_state.stripe_fetched(stripe_id) {
                return false;
            }
        }
        true
    }

    fn start_stripe_fetches(&mut self, request: &RWRequest) -> Result<()> {
        for stripe_id in request.stripe_id_first..=request.stripe_id_last {
            if !self.metadata_state.stripe_fetched(stripe_id)
                && !self.stripe_fetches_requested.contains(&stripe_id)
            {
                self.bgworker_ch
                    .send(BgWorkerRequest::Fetch(stripe_id))
                    .map_err(|e| {
                        error!("Failed to send fetch request for stripe {stripe_id}: {e}");
                        VhostUserBlockError::ChannelError
                    })?;
                self.stripe_fetches_requested.insert(stripe_id);
            }
        }
        Ok(())
    }

    fn process_queued_flush_requests(&mut self) {
        let flushed_version = self.metadata_state.flushed_version();
        while let Some(front) = self.queued_flush_requests.front() {
            if front.pending_metadata_version > flushed_version {
                break;
            }

            let id = front.id;
            self.queued_flush_requests.pop_front();
            self.base.add_flush(id);
        }
    }

    fn process_queued_rw_requests(&mut self) {
        let mut added_requests = Vec::new();

        while let Some(front) = self.queued_rw_requests.front() {
            if !self.request_stripes_fetched(front) {
                break;
            }

            for stripe_id in front.stripe_id_first..=front.stripe_id_last {
                self.stripe_fetches_requested.remove(&stripe_id);
            }

            let request = self.queued_rw_requests.pop_front().expect("front exists");
            let sector = request.sector_offset;
            match request.type_ {
                RequestType::In => {
                    self.base.add_read(
                        sector,
                        request.sector_count,
                        request.buf.clone(),
                        request.id,
                    );
                }
                RequestType::Out => {
                    self.base.add_write(
                        sector,
                        request.sector_count,
                        request.buf.clone(),
                        request.id,
                    );
                }
            }

            added_requests.push(request.id);
        }

        if !added_requests.is_empty() {
            if let Err(e) = self.base.submit() {
                error!(
                    "Failed to submit {} queued requests: {}",
                    added_requests.len(),
                    e
                );
                for id in added_requests {
                    self.finished_requests.push((id, false));
                }
            }
        }
    }
}

impl IoChannel for LazyIoChannel {
    fn add_read(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        let request = RWRequest {
            id,
            type_: RequestType::In,
            sector_offset,
            sector_count,
            buf: buf.clone(),
            stripe_id_first: self.metadata_state.sector_to_stripe_id(sector_offset),
            stripe_id_last: self
                .metadata_state
                .sector_to_stripe_id(sector_offset + sector_count as u64 - 1),
        };

        let fetched = self.request_stripes_fetched(&request);
        if fetched {
            self.base.add_read(sector_offset, sector_count, buf, id);
        } else if let Some(image_channel) = &mut self.image {
            image_channel.add_read(sector_offset, sector_count, buf, id);
        } else if let Err(e) = self.start_stripe_fetches(&request) {
            error!(
                "Failed to send fetch request for stripe range {}-{}: {}",
                request.stripe_id_first, request.stripe_id_last, e
            );
            self.finished_requests.push((id, false));
        } else {
            self.queued_rw_requests.push_back(request);
        }
    }

    fn add_write(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        let request = RWRequest {
            id,
            type_: RequestType::Out,
            sector_offset,
            sector_count,
            buf: buf.clone(),
            stripe_id_first: self.metadata_state.sector_to_stripe_id(sector_offset),
            stripe_id_last: self
                .metadata_state
                .sector_to_stripe_id(sector_offset + sector_count as u64 - 1),
        };

        let fetched = self.request_stripes_fetched(&request);
        if fetched {
            self.base
                .add_write(sector_offset, sector_count, buf.clone(), id);
        } else if let Err(e) = self.start_stripe_fetches(&request) {
            error!(
                "Failed to send fetch request for stripe range {}-{}: {}",
                request.stripe_id_first, request.stripe_id_last, e
            );
            self.finished_requests.push((id, false));
        } else {
            self.queued_rw_requests.push_back(request);
        }
    }

    fn add_flush(&mut self, id: usize) {
        if !self.metadata_state.needs_flush() {
            self.base.add_flush(id);
            return;
        }

        let current_metadata_version = self.metadata_state.current_version();

        if let Err(e) = self.bgworker_ch.send(BgWorkerRequest::FlushMetadata) {
            error!("Failed to send flush request: {e}");
            self.finished_requests.push((id, false));
        }

        self.queued_flush_requests.push_back(FlushRequest {
            id,
            pending_metadata_version: current_metadata_version,
        });
    }

    fn submit(&mut self) -> Result<()> {
        if let Some(image_channel) = &mut self.image {
            image_channel.submit()?;
        }
        self.base.submit()
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        self.process_queued_flush_requests();
        self.process_queued_rw_requests();

        let mut results = std::mem::take(&mut self.finished_requests);
        results.extend(self.base.poll());
        if let Some(image_channel) = &mut self.image {
            results.extend(image_channel.poll());
        }

        results
    }

    fn busy(&self) -> bool {
        self.base.busy()
            || self.image.as_ref().is_some_and(|ch| ch.busy())
            || !self.queued_rw_requests.is_empty()
            || !self.queued_flush_requests.is_empty()
    }
}

pub struct LazyBlockDevice {
    base: Box<dyn BlockDevice>,
    image: Option<Box<dyn BlockDevice>>,
    bgworker: SharedBgWorker,
}

impl LazyBlockDevice {
    pub fn new(
        base: Box<dyn BlockDevice>,
        image: Option<Box<dyn BlockDevice>>,
        bgworker: SharedBgWorker,
    ) -> Result<Box<Self>> {
        Ok(Box::new(LazyBlockDevice {
            base,
            image,
            bgworker,
        }))
    }
}

impl BlockDevice for LazyBlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>> {
        let base_channel = self.base.create_channel()?;
        let image_channel = if let Some(image) = &self.image {
            Some(image.create_channel()?)
        } else {
            None
        };

        let bgworker = self.bgworker.lock().map_err(|e| {
            error!("Failed to lock background worker: {e}");
            VhostUserBlockError::ChannelError
        })?;

        let bgworker_ch = bgworker.req_sender();

        Ok(Box::new(LazyIoChannel::new(
            base_channel,
            image_channel,
            bgworker_ch,
            bgworker.shared_state(),
        )))
    }

    fn sector_count(&self) -> u64 {
        self.base.sector_count()
    }
}
