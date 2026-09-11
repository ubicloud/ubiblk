use std::sync::mpsc::{Receiver, TryRecvError};

use log::{error, info};

use super::bdev_lazy::bgworker::LazyTask;
use super::bdev_spill::task::{FlushReply, SpillRequest, SpillTask};

pub enum BgWorkerRequest {
    Fetch { stripe_id: usize },
    SetWritten { stripe_id: usize },
    SpillFetch { chunk: usize },
    SpillMakeRoom,
    SpillFlush { reply: FlushReply },
    SpillWrote { chunk: usize },
    SpillPoison { chunk: usize },
    Shutdown,
}

pub struct BgWorker {
    lazy: Option<LazyTask>,
    spill: Option<SpillTask>,
    requests: Receiver<BgWorkerRequest>,
    done: bool,
}

impl BgWorker {
    pub fn new(requests: Receiver<BgWorkerRequest>) -> Self {
        BgWorker {
            lazy: None,
            spill: None,
            requests,
            done: false,
        }
    }

    pub fn set_lazy_task(&mut self, lazy: LazyTask) {
        self.lazy = Some(lazy);
    }

    pub fn set_spill_task(&mut self, spill: SpillTask) {
        self.spill = Some(spill);
    }

    fn spill(&mut self) -> Option<&mut SpillTask> {
        if self.spill.is_none() {
            error!("Request for a spill task the worker does not have");
        }
        self.spill.as_mut()
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
            BgWorkerRequest::SpillFetch { chunk } => {
                if let Some(spill) = self.spill() {
                    spill.handle(SpillRequest::Fetch { chunk });
                }
            }
            BgWorkerRequest::SpillMakeRoom => {
                if let Some(spill) = self.spill() {
                    spill.handle(SpillRequest::MakeRoom);
                }
            }
            BgWorkerRequest::SpillFlush { reply } => {
                if let Some(spill) = self.spill() {
                    spill.handle(SpillRequest::Flush { reply });
                }
            }
            BgWorkerRequest::SpillWrote { chunk } => {
                if let Some(spill) = self.spill() {
                    spill.handle(SpillRequest::Wrote { chunk });
                }
            }
            BgWorkerRequest::SpillPoison { chunk } => {
                if let Some(spill) = self.spill() {
                    spill.handle(SpillRequest::Poison { chunk });
                }
            }
            BgWorkerRequest::Shutdown => {
                info!("Received shutdown request, stopping worker");
                if let Some(spill) = &mut self.spill {
                    spill.finish();
                }
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
        if let Some(spill) = &mut self.spill {
            spill.update();
        }
    }

    fn busy(&self) -> bool {
        self.lazy.as_ref().is_some_and(|lazy| lazy.busy())
            || self.spill.as_ref().is_some_and(|spill| spill.busy())
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
