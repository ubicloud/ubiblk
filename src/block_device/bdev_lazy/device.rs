use crate::{
    backends::SECTOR_SIZE,
    block_device::{
        shared_buffer, BgWorkerRequest, BlockDevice, IoChannel, SharedBuffer, SharedMetadataState,
    },
    Result, ResultExt,
};

use super::metadata::{Failed, Fetched, NoSource, NotFetched, Zeroed};

use std::{
    collections::{HashMap, HashSet, VecDeque},
    sync::mpsc::Sender,
};

use log::{debug, error};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RequestType {
    In,
    Out,
    /// Marks whole stripes zeroed without writing them.
    Zero,
}

/// Tag the base ids of the zero writes at the ends of a write zeroes range.
const HEAD_WRITE: usize = 1 << (usize::BITS - 1);
const TAIL_WRITE: usize = 1 << (usize::BITS - 2);

/// A write zeroes request, done when all of its parts are.
struct PendingWriteZeroes {
    parts: usize,
    success: bool,
    /// Zero buffers the base channel writes from until the parts complete.
    bufs: Vec<SharedBuffer>,
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

/// The raw image that reads of unfetched stripes are served from.
struct ImageChannel {
    channel: Box<dyn IoChannel>,
    sector_count: u64,
}

struct LazyIoChannel {
    base: Box<dyn IoChannel>,
    image: Option<ImageChannel>,
    queued_rw_requests: VecDeque<RWRequest>,
    finished_requests: Vec<(usize, bool)>,
    bgworker_ch: Sender<BgWorkerRequest>,
    metadata_state: SharedMetadataState,
    stripe_fetches_requested: HashSet<usize>,
    track_written: bool,
    skip_whole_stripe_fetch: bool,
    sector_count: u64,
    pending_write_zeroes: HashMap<usize, PendingWriteZeroes>,
}

impl LazyIoChannel {
    fn new(
        base: Box<dyn IoChannel>,
        image: Option<ImageChannel>,
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
            pending_write_zeroes: HashMap::new(),
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
                Zeroed if request.kind == RequestType::Zero => {
                    continue;
                }
                NotFetched | Zeroed => {
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

    fn request_stripes_all_not_fetched(&self, request: &RWRequest) -> bool {
        (request.stripe_id_first..=request.stripe_id_last)
            .all(|stripe_id| self.metadata_state.stripe_fetch_state(stripe_id) == NotFetched)
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
        request.kind != RequestType::In
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

    fn rw_request(
        &self,
        id: usize,
        kind: RequestType,
        sector_offset: u64,
        sector_count: u32,
        buf: SharedBuffer,
    ) -> RWRequest {
        RWRequest {
            id,
            kind,
            sector_offset,
            sector_count,
            buf,
            stripe_id_first: self.metadata_state.sector_to_stripe_id(sector_offset),
            stripe_id_last: self
                .metadata_state
                .sector_to_stripe_id(sector_offset + sector_count as u64 - 1),
        }
    }

    /// Starts a request whose stripes are ready. Returns whether it was added
    /// to the base channel.
    fn start_request(&mut self, request: &RWRequest) -> bool {
        let (sector, count, buf, id) = (
            request.sector_offset,
            request.sector_count,
            request.buf.clone(),
            request.id,
        );
        match request.kind {
            RequestType::In => self.base.add_read(sector, count, buf, id),
            RequestType::Out => self.base.add_write(sector, count, buf, id),
            RequestType::Zero => {
                let zeroed = (request.stripe_id_first..=request.stripe_id_last)
                    .all(|stripe_id| self.metadata_state.set_stripe_zeroed(stripe_id));
                self.finished_requests.push((id, zeroed));
                return false;
            }
        }
        true
    }

    fn add_write_request(&mut self, request: RWRequest) {
        match self.request_stripes_fetch_status(&request) {
            StripesFetchStatus::Complete => {
                let can_start = !self.track_written || self.request_stripes_written(&request);
                if can_start {
                    self.start_request(&request);
                    return;
                }
            }
            StripesFetchStatus::Pending => {}
            StripesFetchStatus::Failed { stripe_id } => {
                error!("Received a write request for a failed stripe: {stripe_id}");
                self.finished_requests.push((request.id, false));
                return;
            }
        }

        if let Err(e) = self.start_stripe_fetches(&request) {
            error!(
                "Failed to send fetch request for stripe range {}-{}: {}",
                request.stripe_id_first, request.stripe_id_last, e
            );
            self.finished_requests.push((request.id, false));
            return;
        }

        if self.track_written {
            if let Err(e) = self.start_stripe_set_written(&request) {
                error!(
                    "Failed to send set written request for stripe range {}-{}: {}",
                    request.stripe_id_first, request.stripe_id_last, e
                );
                self.finished_requests.push((request.id, false));
                return;
            }
        }

        self.queued_rw_requests.push_back(request);
    }

    fn process_queued_rw_requests(&mut self) {
        let mut added_requests = Vec::new();

        while let Some(front) = self.queued_rw_requests.front() {
            match self.request_stripes_fetch_status(front) {
                StripesFetchStatus::Complete => {}
                StripesFetchStatus::Pending if front.kind == RequestType::Zero => break,
                StripesFetchStatus::Pending => {
                    // Asks for any stripe zeroed since the request was queued.
                    let front = self.queued_rw_requests.pop_front().expect("front exists");
                    if let Err(e) = self.start_stripe_fetches(&front) {
                        error!("Failed to send fetch request for request {}: {e}", front.id);
                    }
                    self.queued_rw_requests.push_front(front);
                    break;
                }
                StripesFetchStatus::Failed { stripe_id } => {
                    let front = self.queued_rw_requests.pop_front().expect("front exists");
                    self.finished_requests.push((front.id, false));
                    error!("Failed to fetch stripe: {stripe_id}");
                    continue;
                }
            }

            if self.track_written
                && front.kind != RequestType::In
                && !self.request_stripes_written(front)
            {
                break;
            }

            for stripe_id in front.stripe_id_first..=front.stripe_id_last {
                self.stripe_fetches_requested.remove(&stripe_id);
            }

            let request = self.queued_rw_requests.pop_front().expect("front exists");
            if self.start_request(&request) {
                added_requests.push(request.id);
            }
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
        let request = self.rw_request(
            id,
            RequestType::In,
            sector_offset,
            sector_count,
            buf.clone(),
        );

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

        if (request.stripe_id_first..=request.stripe_id_last)
            .all(|stripe_id| self.metadata_state.stripe_fetch_state(stripe_id) == Zeroed)
        {
            buf.borrow_mut().as_mut_slice()[..sector_count as usize * SECTOR_SIZE].fill(0);
            self.finished_requests.push((id, true));
            return;
        }

        if self.request_stripes_all_not_fetched(&request) {
            if let Some(image) = &mut self.image {
                // The disk can be larger than the image. What lies past the
                // image's end reads as zeros, as it does once fetched.
                let image_sectors = image
                    .sector_count
                    .saturating_sub(sector_offset)
                    .min(sector_count as u64) as u32;
                let past_image =
                    image_sectors as usize * SECTOR_SIZE..sector_count as usize * SECTOR_SIZE;
                if let Some(tail) = buf.borrow_mut().as_mut_slice().get_mut(past_image) {
                    tail.fill(0);
                }
                if image_sectors == 0 {
                    self.finished_requests.push((id, true));
                } else {
                    image
                        .channel
                        .add_read(sector_offset, image_sectors, buf, id);
                }
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
        let request = self.rw_request(id, RequestType::Out, sector_offset, sector_count, buf);
        self.add_write_request(request);
    }

    fn add_flush(&mut self, id: usize) {
        self.base.add_flush(id);
    }

    /// Whole stripes are marked zeroed, fetched first if needed but without
    /// their source data. The partial stripes at the ends are written.
    fn add_write_zeroes(&mut self, sector_offset: u64, sector_count: u32, id: usize) -> bool {
        if !self.skip_whole_stripe_fetch {
            return false;
        }

        let stripe_sectors = self.metadata_state.stripe_sector_count();
        let end = sector_offset + sector_count as u64;
        let whole_start = sector_offset.next_multiple_of(stripe_sectors).min(end);
        let whole_end = if end == self.sector_count {
            end
        } else {
            end / stripe_sectors * stripe_sectors
        }
        .max(whole_start);

        let mut pending = PendingWriteZeroes {
            parts: 0,
            success: true,
            bufs: Vec::new(),
        };
        for (start, end, tag) in [
            (sector_offset, whole_start, HEAD_WRITE),
            (whole_end, end, TAIL_WRITE),
        ] {
            if start < end {
                let count = (end - start) as u32;
                let buf = shared_buffer(count as usize * SECTOR_SIZE);
                pending.bufs.push(buf.clone());
                pending.parts += 1;
                self.add_write(start, count, buf, id | tag);
            }
        }
        if whole_start < whole_end {
            pending.parts += 1;
            let count = (whole_end - whole_start) as u32;
            let request =
                self.rw_request(id, RequestType::Zero, whole_start, count, shared_buffer(0));
            self.add_write_request(request);
        }
        self.pending_write_zeroes.insert(id, pending);
        true
    }

    fn submit(&mut self) -> Result<()> {
        if let Some(image) = &mut self.image {
            image.channel.submit()?;
        }
        self.base.submit()
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        self.process_queued_rw_requests();

        let mut results = std::mem::take(&mut self.finished_requests);
        results.extend(self.base.poll());
        if let Some(image) = &mut self.image {
            results.extend(image.channel.poll());
        }

        if self.pending_write_zeroes.is_empty() {
            return results;
        }
        results
            .into_iter()
            .filter_map(|(id, success)| {
                let request_id = id & !(HEAD_WRITE | TAIL_WRITE);
                let Some(pending) = self.pending_write_zeroes.get_mut(&request_id) else {
                    return Some((id, success));
                };
                pending.parts -= 1;
                pending.success &= success;
                if pending.parts > 0 {
                    return None;
                }
                let success = pending.success;
                self.pending_write_zeroes.remove(&request_id);
                Some((request_id, success))
            })
            .collect()
    }

    fn busy(&self) -> bool {
        self.base.busy()
            || self
                .image
                .as_ref()
                .is_some_and(|image| image.channel.busy())
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
    /// of the source data. It also enables write zeroes, which tracks zeroed
    /// stripes only in memory.
    pub fn new(
        base: Box<dyn BlockDevice>,
        image: Option<Box<dyn BlockDevice>>,
        bgworker_ch: Sender<BgWorkerRequest>,
        metadata_state: SharedMetadataState,
        track_written: bool,
        skip_whole_stripe_fetch: bool,
    ) -> Result<Box<Self>> {
        // Guest requests are aligned to the base's sectors and are passed to
        // the image as they are.
        let (base_sector_size, image_sector_size) = (
            base.logical_sector_size(),
            image.as_ref().map_or(base.logical_sector_size(), |image| {
                image.logical_sector_size()
            }),
        );
        if !base_sector_size.is_multiple_of(image_sector_size) {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: format!(
                    "Image has {image_sector_size}-byte sectors, larger than the disk's \
                     {base_sector_size}-byte sectors"
                ),
            }));
        }
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
            Some(ImageChannel {
                channel: image.create_channel()?,
                sector_count: image.sector_count(),
            })
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

    fn logical_sector_size(&self) -> usize {
        self.base.logical_sector_size()
    }

    fn supports_write_zeroes(&self) -> bool {
        self.skip_whole_stripe_fetch
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
