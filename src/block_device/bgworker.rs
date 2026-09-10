use std::sync::mpsc::{Receiver, TryRecvError};

use log::{error, info};

use super::bdev_lazy::bgworker::{BgWorkerRequest, LazyTask};

pub struct BgWorker {
    lazy: LazyTask,
    requests: Receiver<BgWorkerRequest>,
    done: bool,
}

impl BgWorker {
    pub fn new(lazy: LazyTask, requests: Receiver<BgWorkerRequest>) -> Self {
        BgWorker {
            lazy,
            requests,
            done: false,
        }
    }

    pub fn process_request(&mut self, req: BgWorkerRequest) {
        match req {
            BgWorkerRequest::Fetch { stripe_id } => self.lazy.fetch_stripe(stripe_id),
            BgWorkerRequest::SetWritten { stripe_id } => self.lazy.set_stripe_written(stripe_id),
            BgWorkerRequest::Shutdown => {
                info!("Received shutdown request, stopping worker");
                self.done = true;
            }
        }
    }

    pub fn receive_requests(&mut self, block: bool) {
        if block {
            match self.requests.recv() {
                Ok(req) => self.process_request(req),
                Err(e) => {
                    error!("Failed to receive request: {e}, stopping worker");
                    self.done = true;
                    return;
                }
            }
        }

        loop {
            match self.requests.try_recv() {
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
        self.lazy.update();
    }

    pub fn run(&mut self) {
        while !self.done {
            let block = !self.lazy.busy();
            self.receive_requests(block);
            self.update();
        }
    }
}
