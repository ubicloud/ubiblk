//! The thread a block device does its background work on.
//!
//! The loop is the same wherever it is used: take requests from a channel,
//! block when there is nothing in flight and poll when there is, and stop on
//! shutdown or when the channel goes away. What the requests mean, and what
//! there is to make progress on, belongs to the device.

use std::ops::ControlFlow;
use std::sync::mpsc::{Receiver, TryRecvError};

use log::error;

/// One device's background work.
pub trait BgTask {
    type Request;

    /// Act on a request. `Break` stops the worker.
    fn handle(&mut self, request: Self::Request) -> ControlFlow<()>;

    /// Make progress on whatever is in flight.
    fn update(&mut self);

    /// Whether there is anything in flight to poll for. A worker with nothing
    /// to do waits on its channel rather than spinning.
    fn busy(&self) -> bool;
}

pub struct BgWorker<T: BgTask> {
    task: T,
    requests: Receiver<T::Request>,
    done: bool,
}

impl<T: BgTask> BgWorker<T> {
    pub fn with_task(task: T, requests: Receiver<T::Request>) -> Self {
        BgWorker {
            task,
            requests,
            done: false,
        }
    }

    pub fn task(&self) -> &T {
        &self.task
    }

    pub fn task_mut(&mut self) -> &mut T {
        &mut self.task
    }

    pub fn done(&self) -> bool {
        self.done
    }

    pub fn process_request(&mut self, request: T::Request) {
        if self.task.handle(request).is_break() {
            self.done = true;
        }
    }

    pub fn receive_requests(&mut self, block: bool) {
        if block {
            match self.requests.recv() {
                Ok(request) => self.process_request(request),
                Err(e) => {
                    error!("Failed to receive request: {e}, stopping worker");
                    self.done = true;
                    return;
                }
            }
        }

        loop {
            match self.requests.try_recv() {
                Ok(request) => self.process_request(request),
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
        self.task.update();
    }

    pub fn run(&mut self) {
        while !self.done {
            let block = !self.task.busy();
            self.receive_requests(block);
            self.update();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::mpsc::channel;

    enum Request {
        Note(u32),
        Stop,
    }

    #[derive(Default)]
    struct Recorder {
        handled: Vec<u32>,
        updates: usize,
        busy: bool,
    }

    impl BgTask for Recorder {
        type Request = Request;

        fn handle(&mut self, request: Request) -> ControlFlow<()> {
            match request {
                Request::Note(n) => {
                    self.handled.push(n);
                    ControlFlow::Continue(())
                }
                Request::Stop => ControlFlow::Break(()),
            }
        }

        fn update(&mut self) {
            self.updates += 1;
            // One update's worth of work, so `run` has a reason to stop looping.
            self.busy = false;
        }

        fn busy(&self) -> bool {
            self.busy
        }
    }

    #[test]
    fn requests_reach_the_task_in_order() {
        let (sender, receiver) = channel();
        let mut worker = BgWorker::with_task(Recorder::default(), receiver);
        sender.send(Request::Note(1)).unwrap();
        sender.send(Request::Note(2)).unwrap();

        worker.receive_requests(false);

        assert_eq!(worker.task().handled, vec![1, 2]);
        assert!(!worker.done());
    }

    #[test]
    fn a_task_that_asks_to_stop_stops_the_worker() {
        let (sender, receiver) = channel();
        let mut worker = BgWorker::with_task(Recorder::default(), receiver);
        sender.send(Request::Stop).unwrap();

        // Returns rather than waiting for a request that is not coming.
        worker.run();

        assert!(worker.done());
    }

    /// Nobody is left to send: waiting for a request that cannot arrive would
    /// hang the thread for the life of the process.
    #[test]
    fn a_channel_with_no_senders_stops_the_worker() {
        let (sender, receiver) = channel::<Request>();
        let mut worker = BgWorker::with_task(Recorder::default(), receiver);
        drop(sender);

        worker.run();

        assert!(worker.done());
    }

    #[test]
    fn a_busy_task_is_polled_rather_than_waited_on() {
        let (sender, receiver) = channel();
        let mut worker = BgWorker::with_task(Recorder::default(), receiver);
        worker.task_mut().busy = true;
        drop(sender);

        // Would block for ever on an empty channel if `busy` were ignored.
        worker.run();

        assert!(worker.task().updates >= 1);
    }
}
