use std::sync::mpsc::{Receiver, TryRecvError};

use log::{error, info};

use super::bdev_lazy::bgworker::LazyTask;

pub enum BgWorkerRequest {
    Fetch { stripe_id: usize },
    SetWritten { stripe_id: usize },
    Shutdown,
}

pub struct BgWorker {
    lazy: Option<LazyTask>,
    requests: Receiver<BgWorkerRequest>,
    done: bool,
}

impl BgWorker {
    pub fn new(requests: Receiver<BgWorkerRequest>) -> Self {
        BgWorker {
            lazy: None,
            requests,
            done: false,
        }
    }

    pub fn set_lazy_task(&mut self, lazy: LazyTask) {
        self.lazy = Some(lazy);
    }

    fn lazy(&mut self) -> Option<&mut LazyTask> {
        if self.lazy.is_none() {
            error!("Request for a lazy task the worker does not have");
        }
        self.lazy.as_mut()
    }

    fn process_request(&mut self, req: BgWorkerRequest) {
        match req {
            BgWorkerRequest::Fetch { stripe_id } => {
                if let Some(lazy) = self.lazy() {
                    lazy.fetch_stripe(stripe_id);
                }
            }
            BgWorkerRequest::SetWritten { stripe_id } => {
                if let Some(lazy) = self.lazy() {
                    lazy.set_stripe_written(stripe_id);
                }
            }
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
        if let Some(lazy) = &mut self.lazy {
            lazy.update();
        }
    }

    fn busy(&self) -> bool {
        self.lazy.as_ref().is_some_and(|lazy| lazy.busy())
    }

    pub fn run(&mut self) {
        while !self.done {
            let block = !self.busy();
            self.receive_requests(block);
            self.update();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::mpsc::channel;

    #[test]
    fn a_shutdown_request_stops_the_worker() {
        let (sender, requests) = channel();
        let mut worker = BgWorker::new(requests);
        sender.send(BgWorkerRequest::Shutdown).unwrap();

        worker.run();

        assert!(worker.done);
    }

    /// Otherwise the thread waits for a request that cannot arrive.
    #[test]
    fn a_channel_with_no_senders_stops_the_worker() {
        let (sender, requests) = channel::<BgWorkerRequest>();
        let mut worker = BgWorker::new(requests);
        drop(sender);

        worker.run();

        assert!(worker.done);
    }
}
