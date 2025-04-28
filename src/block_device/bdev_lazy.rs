use std::{
    collections::{HashSet, VecDeque},
    sync::mpsc::{Receiver, Sender},
};

use super::{
    stripe_fetcher::{
        SharedStripeFetcher, StripeFetcherRequest, StripeFetcherResponse, StripeStatus,
        StripeStatusVec,
    },
    *,
};
use crate::Result;
use log::error;

#[derive(Debug)]
enum RequestType {
    In,
    Out,
}

struct Request {
    id: usize,
    type_: RequestType,
    sector: u64,
    buf: SharedBuffer,
    len: usize,
    stripe_id_first: usize,
    stripe_id_last: usize,
}

struct LazyIoChannel {
    base: Box<dyn IoChannel>,
    queued_rw_requests: RefCell<VecDeque<Request>>,
    flush_requests: HashSet<usize>,
    finished_requests: Vec<(usize, bool)>,
    sender: Sender<StripeFetcherRequest>,
    receiver: Receiver<StripeFetcherResponse>,
    stripe_status_vec: RefCell<StripeStatusVec>,
}

impl LazyIoChannel {
    fn new(
        base: Box<dyn IoChannel>,
        sender: Sender<StripeFetcherRequest>,
        receiver: Receiver<StripeFetcherResponse>,
        stripe_status_vec: StripeStatusVec,
    ) -> Self {
        LazyIoChannel {
            base,
            queued_rw_requests: RefCell::new(VecDeque::new()),
            finished_requests: Vec::new(),
            flush_requests: HashSet::new(),
            sender,
            receiver,
            stripe_status_vec: RefCell::new(stripe_status_vec),
        }
    }
}

impl LazyIoChannel {
    fn stripe_status(&self, stripe_id: usize) -> StripeStatus {
        self.stripe_status_vec.borrow().stripe_status(stripe_id)
    }

    fn set_stripe_status(&self, stripe_id: usize, status: StripeStatus) {
        self.stripe_status_vec
            .borrow_mut()
            .set_stripe_status(stripe_id, status);
    }

    fn request_stripes_fetched(&self, request: &Request) -> bool {
        for stripe_id in request.stripe_id_first..=request.stripe_id_last {
            if self.stripe_status(stripe_id) != StripeStatus::Fetched {
                return false;
            }
        }
        true
    }

    fn start_stripe_fetches(&mut self, request: &Request) -> Result<()> {
        for stripe_id in request.stripe_id_first..=request.stripe_id_last {
            if self.stripe_status(stripe_id) == StripeStatus::NotFetched {
                self.set_stripe_status(stripe_id, StripeStatus::Fetching);
                self.sender
                    .send(StripeFetcherRequest::Fetch(stripe_id))
                    .map_err(|e| {
                        error!("Failed to send fetch request: {}", e);
                        crate::Error::IoError
                    })?;
            }
        }
        Ok(())
    }

    fn sector_to_stripe_id(&self, sector: u64) -> usize {
        self.stripe_status_vec.borrow().sector_to_stripe_id(sector)
    }

    fn poll_stripe_fetcher(&mut self) {
        while let Ok(resp) = self.receiver.try_recv() {
            match resp {
                StripeFetcherResponse::Fetch(stripe_id, success) => {
                    let status = if success {
                        StripeStatus::Fetched
                    } else {
                        StripeStatus::NotFetched
                    };

                    self.set_stripe_status(stripe_id, status);
                }
                StripeFetcherResponse::Flush(flush_id, success) => {
                    if success {
                        self.base.add_flush(flush_id);
                        if let Err(e) = self.base.submit() {
                            error!("Failed to submit flush request: {}", e);
                            self.finished_requests.push((flush_id, false));
                        }
                    } else {
                        self.finished_requests.push((flush_id, false));
                    }
                }
            }
        }
    }

    fn process_queued_requests(&mut self) {
        let mut queued_rw_requests = self.queued_rw_requests.borrow_mut();
        let mut added_requests = vec![];
        while let Some(request) = queued_rw_requests.pop_front() {
            if !self.request_stripes_fetched(&request) {
                queued_rw_requests.push_front(request);
                break;
            }
            let sector = self.translate_sector(request.sector);
            match request.type_ {
                RequestType::In => {
                    self.base
                        .add_read(sector, request.buf.clone(), request.len, request.id);
                }
                RequestType::Out => {
                    self.base
                        .add_write(sector, request.buf.clone(), request.len, request.id);
                }
            }

            added_requests.push(request.id);
        }

        if !added_requests.is_empty() {
            if let Err(e) = self.base.submit() {
                error!("Failed to submit queued requests: {}", e);
                for id in added_requests {
                    self.finished_requests.push((id, false));
                }
            }
        }
    }

    fn translate_sector(&self, sector: u64) -> u64 {
        self.stripe_status_vec.borrow().translate_sector(sector)
    }
}

impl IoChannel for LazyIoChannel {
    fn add_read(&mut self, sector: u64, buf: SharedBuffer, len: usize, id: usize) {
        let request = Request {
            id,
            type_: RequestType::In,
            sector,
            buf: buf.clone(),
            len,
            stripe_id_first: self.sector_to_stripe_id(sector),
            stripe_id_last: self.sector_to_stripe_id(sector + (len / 512) as u64 - 1),
        };

        let fetched = self.request_stripes_fetched(&request);
        if fetched {
            let sector = self.translate_sector(sector);
            self.base.add_read(sector, buf, len, id);
        } else {
            if let Err(e) = self.start_stripe_fetches(&request) {
                error!("Failed to send fetch request: {}", e);
                self.finished_requests.push((id, false));
            } else {
                self.queued_rw_requests.borrow_mut().push_back(request);
            }
        }
    }

    fn add_write(&mut self, sector: u64, buf: SharedBuffer, len: usize, id: usize) {
        let request = Request {
            id,
            type_: RequestType::Out,
            sector,
            buf: buf.clone(),
            len,
            stripe_id_first: self.sector_to_stripe_id(sector),
            stripe_id_last: self.sector_to_stripe_id(sector + (len / 512) as u64 - 1),
        };

        let fetched = self.request_stripes_fetched(&request);
        if fetched {
            self.base
                .add_write(self.translate_sector(sector), buf.clone(), len, id);
        } else {
            if let Err(e) = self.start_stripe_fetches(&request) {
                error!("Failed to send fetch request: {}", e);
                self.finished_requests.push((id, false));
            } else {
                self.queued_rw_requests.borrow_mut().push_back(request);
            }
        }
    }

    fn add_flush(&mut self, id: usize) {
        if let Err(e) = self.sender.send(StripeFetcherRequest::Flush(id)) {
            error!("Failed to send flush request: {}", e);
            self.finished_requests.push((id, false));
        }
        self.flush_requests.insert(id);
    }

    fn submit(&mut self) -> Result<()> {
        self.base.submit()
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        self.poll_stripe_fetcher();
        self.process_queued_requests();

        let mut results = self.finished_requests.clone();
        results.extend(self.base.poll());
        self.finished_requests.clear();

        for id in &results {
            if self.flush_requests.contains(&id.0) {
                self.flush_requests.remove(&id.0);
            }
        }

        results
    }

    fn busy(&mut self) -> bool {
        self.base.busy()
            || self.queued_rw_requests.borrow().len() > 0
            || self.flush_requests.len() > 0
    }
}

pub struct LazyBlockDevice {
    base: Box<dyn BlockDevice>,
    stripe_fetcher: SharedStripeFetcher,
    size: u64,
}

impl LazyBlockDevice {
    pub fn new(base: Box<dyn BlockDevice>, stripe_fetcher: SharedStripeFetcher) -> Box<Self> {
        let base_size = base.size();
        let metadata_size = stripe_fetcher.lock().unwrap().metadata_size() as u64;
        Box::new(LazyBlockDevice {
            base,
            stripe_fetcher,
            size: base_size - metadata_size,
        })
    }
}

impl BlockDevice for LazyBlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>> {
        let (req_sender, req_receiver) = std::sync::mpsc::channel();
        let (resp_sender, resp_receiver) = std::sync::mpsc::channel();
        let base_channel = self.base.create_channel()?;

        let mut stripe_fetcher = self.stripe_fetcher.lock().unwrap();
        stripe_fetcher.add_req_mpsc_pair(resp_sender, req_receiver);

        Ok(Box::new(LazyIoChannel::new(
            base_channel,
            req_sender,
            resp_receiver,
            stripe_fetcher.stripe_status_vec(),
        )))
    }

    fn size(&self) -> u64 {
        self.size
    }
}
