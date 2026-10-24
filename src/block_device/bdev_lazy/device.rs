use crate::{
    block_device::{BgWorkerRequest, BlockDevice, IoChannel, SharedBuffer, SharedMetadataState},
    Result, ResultExt,
};

use super::metadata::{Failed, Fetched, NoSource, NotFetched};

use std::{
    collections::{HashSet, VecDeque},
    sync::mpsc::Sender,
};

use log::{debug, error};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RequestType {
    In,
    Out,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StripesFetchStatus {
    Pending,
    Complete,
    Failed { stripe_id: usize },
}

struct RWRequest {
    id: usize,
    kind: RequestType,
    sector_offset: u64,
    sector_count: u32,
    buf: SharedBuffer,
    stripe_id_first: usize,
    stripe_id_last: usize,
}

struct LazyIoChannel {
    base: Box<dyn IoChannel>,
    image: Option<Box<dyn IoChannel>>,
    queued_rw_requests: VecDeque<RWRequest>,
    finished_requests: Vec<(usize, bool)>,
    bgworker_ch: Sender<BgWorkerRequest>,
    metadata_state: SharedMetadataState,
    stripe_fetches_requested: HashSet<usize>,
    track_written: bool,
    skip_whole_stripe_fetch: bool,
    sector_count: u64,
}

impl LazyIoChannel {
    fn new(
        base: Box<dyn IoChannel>,
        image: Option<Box<dyn IoChannel>>,
        bgworker_ch: Sender<BgWorkerRequest>,
        metadata_state: SharedMetadataState,
        track_written: bool,
        skip_whole_stripe_fetch: bool,
        sector_count: u64,
    ) -> Self {
        LazyIoChannel {
            base,
            image,
            queued_rw_requests: VecDeque::new(),
            finished_requests: Vec::new(),
            bgworker_ch,
            metadata_state,
            stripe_fetches_requested: HashSet::new(),
            track_written,
            skip_whole_stripe_fetch,
            sector_count,
        }
    }
}

impl LazyIoChannel {
    fn request_stripes_fetch_status(&self, request: &RWRequest) -> StripesFetchStatus {
        for stripe_id in request.stripe_id_first..=request.stripe_id_last {
            let state = self.metadata_state.stripe_fetch_state(stripe_id);
            match state {
                Fetched | NoSource => {
                    continue;
                }
                NotFetched => {
                    return StripesFetchStatus::Pending;
                }
                Failed => {
                    return StripesFetchStatus::Failed { stripe_id };
                }
                _ => {}
            }
        }
        StripesFetchStatus::Complete
    }

    fn request_stripes_written(&self, request: &RWRequest) -> bool {
        for stripe_id in request.stripe_id_first..=request.stripe_id_last {
            if !self.metadata_state.stripe_written(stripe_id) {
                return false;
            }
        }
        true
    }

    /// Returns whether a write request replaces all of the stripe's data.
    fn write_covers_stripe(&self, request: &RWRequest, stripe_id: usize) -> bool {
        let stripe_sectors = self.metadata_state.stripe_sector_count();
        let stripe_start = stripe_id as u64 * stripe_sectors;
        let stripe_end = (stripe_start + stripe_sectors).min(self.sector_count);
        request.kind == RequestType::Out
            && request.sector_offset <= stripe_start
            && stripe_end <= request.sector_offset + request.sector_count as u64
    }

    fn start_stripe_fetches(&mut self, request: &RWRequest) -> Result<()> {
        for stripe_id in request.stripe_id_first..=request.stripe_id_last {
            if !self.metadata_state.stripe_fetched_if_needed(stripe_id)
                && !self.stripe_fetches_requested.contains(&stripe_id)
            {
                let whole_stripe_write =
                    self.skip_whole_stripe_fetch && self.write_covers_stripe(request, stripe_id);
                self.bgworker_ch
                    .send(BgWorkerRequest::Fetch {
                        stripe_id,
                        whole_stripe_write,
                    })
                    .with_context(|| {
                        format!("failed to send fetch request for stripe {stripe_id}")
                    })?;
                self.stripe_fetches_requested.insert(stripe_id);
            }
        }
        Ok(())
    }

    fn start_stripe_set_written(&mut self, request: &RWRequest) -> Result<()> {
        for stripe_id in request.stripe_id_first..=request.stripe_id_last {
            if !self.metadata_state.stripe_written(stripe_id) {
                self.bgworker_ch
                    .send(BgWorkerRequest::SetWritten { stripe_id })
                    .with_context(|| {
                        format!("failed to send set written request for stripe {stripe_id}")
                    })?;
            }
        }
        Ok(())
    }

    fn process_queued_rw_requests(&mut self) {
        let mut added_requests = Vec::new();

        while let Some(front) = self.queued_rw_requests.front() {
            match self.request_stripes_fetch_status(front) {
                StripesFetchStatus::Complete => {}
                StripesFetchStatus::Pending => break,
                StripesFetchStatus::Failed { stripe_id } => {
                    let front = self.queued_rw_requests.pop_front().expect("front exists");
                    self.finished_requests.push((front.id, false));
                    error!("Failed to fetch stripe: {stripe_id}");
                    continue;
                }
            }

            if self.track_written
                && front.kind == RequestType::Out
                && !self.request_stripes_written(front)
            {
                break;
            }

            for stripe_id in front.stripe_id_first..=front.stripe_id_last {
                self.stripe_fetches_requested.remove(&stripe_id);
            }

            let request = self.queued_rw_requests.pop_front().expect("front exists");
            let sector = request.sector_offset;
            match request.kind {
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
            kind: RequestType::In,
            sector_offset,
            sector_count,
            buf: buf.clone(),
            stripe_id_first: self.metadata_state.sector_to_stripe_id(sector_offset),
            stripe_id_last: self
                .metadata_state
                .sector_to_stripe_id(sector_offset + sector_count as u64 - 1),
        };

        match self.request_stripes_fetch_status(&request) {
            StripesFetchStatus::Complete => {
                self.base.add_read(sector_offset, sector_count, buf, id);
                return;
            }
            StripesFetchStatus::Pending => {}
            StripesFetchStatus::Failed { stripe_id } => {
                error!("Received a read request for a failed stripe: {stripe_id}");
                self.finished_requests.push((id, false));
                return;
            }
        }

        if request.stripe_id_first == request.stripe_id_last {
            if let Some(image_channel) = &mut self.image {
                image_channel.add_read(sector_offset, sector_count, buf, id);
                return;
            }
        } else {
            debug!(
                "cross_stripe_read: fetching stripes [{}..={}]: offset {} sectors, length {} sectors",
                request.stripe_id_first, request.stripe_id_last, sector_offset, sector_count
            );
        }

        if let Err(e) = self.start_stripe_fetches(&request) {
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
            kind: RequestType::Out,
            sector_offset,
            sector_count,
            buf: buf.clone(),
            stripe_id_first: self.metadata_state.sector_to_stripe_id(sector_offset),
            stripe_id_last: self
                .metadata_state
                .sector_to_stripe_id(sector_offset + sector_count as u64 - 1),
        };

        match self.request_stripes_fetch_status(&request) {
            StripesFetchStatus::Complete => {
                let can_start = !self.track_written || self.request_stripes_written(&request);
                if can_start {
                    self.base
                        .add_write(sector_offset, sector_count, buf.clone(), id);
                    return;
                }
            }
            StripesFetchStatus::Pending => {}
            StripesFetchStatus::Failed { stripe_id } => {
                error!("Received a write request for a failed stripe: {stripe_id}");
                self.finished_requests.push((id, false));
                return;
            }
        }

        if let Err(e) = self.start_stripe_fetches(&request) {
            error!(
                "Failed to send fetch request for stripe range {}-{}: {}",
                request.stripe_id_first, request.stripe_id_last, e
            );
            self.finished_requests.push((id, false));
            return;
        }

        if self.track_written {
            if let Err(e) = self.start_stripe_set_written(&request) {
                error!(
                    "Failed to send set written request for stripe range {}-{}: {}",
                    request.stripe_id_first, request.stripe_id_last, e
                );
                self.finished_requests.push((id, false));
                return;
            }
        }

        self.queued_rw_requests.push_back(request);
    }

    fn add_flush(&mut self, id: usize) {
        self.base.add_flush(id);
    }

    fn submit(&mut self) -> Result<()> {
        if let Some(image_channel) = &mut self.image {
            image_channel.submit()?;
        }
        self.base.submit()
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
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
    }
}

pub struct LazyBlockDevice {
    base: Box<dyn BlockDevice>,
    image: Option<Box<dyn BlockDevice>>,
    bgworker_ch: Sender<BgWorkerRequest>,
    metadata_state: SharedMetadataState,
    track_written: bool,
    skip_whole_stripe_fetch: bool,
}

impl LazyBlockDevice {
    /// With `skip_whole_stripe_fetch`, a write that replaces a whole unfetched
    /// stripe marks it fetched without reading the source. The stripe is
    /// marked fetched before the write reaches the disk, so until it does,
    /// concurrent reads and a crash expose the target's old contents instead
    /// of the source data.
    pub fn new(
        base: Box<dyn BlockDevice>,
        image: Option<Box<dyn BlockDevice>>,
        bgworker_ch: Sender<BgWorkerRequest>,
        metadata_state: SharedMetadataState,
        track_written: bool,
        skip_whole_stripe_fetch: bool,
    ) -> Result<Box<Self>> {
        Ok(Box::new(LazyBlockDevice {
            base,
            image,
            bgworker_ch,
            metadata_state,
            track_written,
            skip_whole_stripe_fetch,
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

        Ok(Box::new(LazyIoChannel::new(
            base_channel,
            image_channel,
            self.bgworker_ch.clone(),
            self.metadata_state.clone(),
            self.track_written,
            self.skip_whole_stripe_fetch,
            self.base.sector_count(),
        )))
    }

    fn sector_count(&self) -> u64 {
        self.base.sector_count()
    }

    fn clone(&self) -> Box<dyn BlockDevice> {
        Box::new(LazyBlockDevice {
            base: self.base.clone(),
            image: self.image.clone(),
            bgworker_ch: self.bgworker_ch.clone(),
            metadata_state: self.metadata_state.clone(),
            track_written: self.track_written,
            skip_whole_stripe_fetch: self.skip_whole_stripe_fetch,
        })
    }
}
