//! The thread block devices do their background work on.
//!
//! One thread serves them all. A device registers a task and gets a queue to
//! send it work on; the loop waits while nothing is in flight and polls while
//! something is, so an idle task costs nothing and a busy one keeps its
//! neighbours from sleeping.

use std::ops::ControlFlow;
use std::sync::mpsc::{channel, Receiver, SendError, Sender, TryRecvError};

use log::error;

/// One device's background work.
pub trait BgTask {
    type Request;

    /// Act on a request. `Break` retires the task.
    fn handle(&mut self, request: Self::Request) -> ControlFlow<()>;

    /// Make progress on whatever is in flight.
    fn update(&mut self);

    /// Whether there is anything in flight to poll for.
    fn busy(&self) -> bool;
}

/// The device end of a task's queue.
pub struct BgSender<R> {
    requests: Sender<R>,
    wakeup: Sender<()>,
}

impl<R> BgSender<R> {
    pub fn send(&self, request: R) -> std::result::Result<(), SendError<R>> {
        self.requests.send(request)?;
        // After the request, so a waiting worker never misses it.
        let _ = self.wakeup.send(());
        Ok(())
    }
}

impl<R> Clone for BgSender<R> {
    fn clone(&self) -> Self {
        BgSender {
            requests: self.requests.clone(),
            wakeup: self.wakeup.clone(),
        }
    }
}

/// A task and its queue with the request type hidden, so that one worker can
/// hold tasks that take different requests.
trait Queued {
    fn drain(&mut self) -> ControlFlow<()>;
    fn update(&mut self);
    fn busy(&self) -> bool;
}

struct TaskQueue<T: BgTask> {
    task: T,
    requests: Receiver<T::Request>,
}

impl<T: BgTask> Queued for TaskQueue<T> {
    fn drain(&mut self) -> ControlFlow<()> {
        loop {
            match self.requests.try_recv() {
                Ok(request) => self.task.handle(request)?,
                Err(TryRecvError::Empty) => return ControlFlow::Continue(()),
                Err(TryRecvError::Disconnected) => {
                    error!("Request channel disconnected, retiring task");
                    return ControlFlow::Break(());
                }
            }
        }
    }

    fn update(&mut self) {
        self.task.update();
    }

    fn busy(&self) -> bool {
        self.task.busy()
    }
}

/// Hands out queues before the worker exists: a device needs its sender at
/// build time, while the tasks are built on the worker's own thread.
pub struct BgQueues {
    wakeup_sender: Sender<()>,
    wakeup: Receiver<()>,
}

impl Default for BgQueues {
    fn default() -> Self {
        Self::new()
    }
}

impl BgQueues {
    pub fn new() -> Self {
        let (wakeup_sender, wakeup) = channel();
        BgQueues {
            wakeup_sender,
            wakeup,
        }
    }

    pub fn queue<R>(&self) -> (BgSender<R>, Receiver<R>) {
        let (requests, receiver) = channel();
        let sender = BgSender {
            requests,
            wakeup: self.wakeup_sender.clone(),
        };
        (sender, receiver)
    }
}

pub struct BgWorker {
    tasks: Vec<Box<dyn Queued>>,
    wakeup: Receiver<()>,
    /// The queues' side of the wakeup channel, dropped once the worker runs so
    /// that a wait ends when the last sender goes away.
    wakeup_sender: Option<Sender<()>>,
}

impl BgWorker {
    pub fn new(queues: BgQueues) -> Self {
        BgWorker {
            tasks: Vec::new(),
            wakeup: queues.wakeup,
            wakeup_sender: Some(queues.wakeup_sender),
        }
    }

    pub fn add<T: BgTask + 'static>(&mut self, task: T, requests: Receiver<T::Request>) {
        self.tasks.push(Box::new(TaskQueue { task, requests }));
    }

    pub fn busy(&self) -> bool {
        self.tasks.iter().any(|task| task.busy())
    }

    pub fn receive_requests(&mut self, block: bool) {
        if block {
            self.wait();
        }
        self.tasks.retain_mut(|task| task.drain().is_continue());
    }

    pub fn update(&mut self) {
        for task in &mut self.tasks {
            task.update();
        }
    }

    pub fn run(&mut self) {
        self.wakeup_sender = None;
        while !self.tasks.is_empty() {
            let block = !self.busy();
            self.receive_requests(block);
            self.update();
        }
    }

    fn wait(&self) {
        if self.wakeup.recv().is_err() {
            return;
        }
        // Every queue is drained afterwards, so the rest of the tokens say
        // nothing new.
        while self.wakeup.try_recv().is_ok() {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::time::Duration;

    enum Request {
        Note(u32),
        Stop,
    }

    type Log = Rc<RefCell<Vec<u32>>>;

    #[derive(Default)]
    struct Recorder {
        handled: Log,
        updates: Rc<RefCell<usize>>,
        busy: bool,
    }

    impl BgTask for Recorder {
        type Request = Request;

        fn handle(&mut self, request: Request) -> ControlFlow<()> {
            match request {
                Request::Note(n) => {
                    self.handled.borrow_mut().push(n);
                    ControlFlow::Continue(())
                }
                Request::Stop => ControlFlow::Break(()),
            }
        }

        fn update(&mut self) {
            *self.updates.borrow_mut() += 1;
            // One update's worth of work, so `run` has a reason to stop looping.
            self.busy = false;
        }

        fn busy(&self) -> bool {
            self.busy
        }
    }

    fn recorder(handled: &Log) -> Recorder {
        Recorder {
            handled: handled.clone(),
            ..Default::default()
        }
    }

    #[test]
    fn each_task_gets_its_own_requests_in_order() {
        let queues = BgQueues::new();
        let (to_first, first_requests) = queues.queue();
        let (to_second, second_requests) = queues.queue();
        let (first, second) = (Log::default(), Log::default());
        let mut worker = BgWorker::new(queues);
        worker.add(recorder(&first), first_requests);
        worker.add(recorder(&second), second_requests);

        to_first.send(Request::Note(1)).unwrap();
        to_second.send(Request::Note(2)).unwrap();
        to_first.send(Request::Note(3)).unwrap();
        worker.receive_requests(false);

        assert_eq!(*first.borrow(), vec![1, 3]);
        assert_eq!(*second.borrow(), vec![2]);
    }

    #[test]
    fn a_task_that_asks_to_stop_leaves_the_others_running() {
        let queues = BgQueues::new();
        let (to_quitter, quitter_requests) = queues.queue();
        let (to_survivor, survivor_requests) = queues.queue();
        let survived = Log::default();
        let mut worker = BgWorker::new(queues);
        worker.add(Recorder::default(), quitter_requests);
        worker.add(recorder(&survived), survivor_requests);

        to_quitter.send(Request::Stop).unwrap();
        worker.receive_requests(false);
        to_survivor.send(Request::Note(1)).unwrap();
        worker.receive_requests(false);

        assert_eq!(*survived.borrow(), vec![1]);
    }

    /// Nobody is left to send: waiting for a request that cannot arrive would
    /// keep the thread alive for the life of the process.
    #[test]
    fn a_queue_with_no_senders_retires_its_task() {
        let queues = BgQueues::new();
        let (sender, requests) = queues.queue::<Request>();
        let mut worker = BgWorker::new(queues);
        worker.add(Recorder::default(), requests);
        drop(sender);

        worker.run();

        assert!(worker.tasks.is_empty());
    }

    #[test]
    fn a_busy_task_is_polled_rather_than_waited_on() {
        let queues = BgQueues::new();
        let (sender, requests) = queues.queue();
        let updates = Rc::new(RefCell::new(0));
        let mut worker = BgWorker::new(queues);
        worker.add(
            Recorder {
                updates: updates.clone(),
                busy: true,
                ..Default::default()
            },
            requests,
        );

        // Nothing is queued yet, so a worker that waits before looking at what
        // is in flight reaches the stop request without having updated the task.
        std::thread::spawn(move || {
            std::thread::sleep(Duration::from_millis(50));
            let _ = sender.send(Request::Stop);
        });
        worker.run();

        assert!(*updates.borrow() >= 1);
    }
}
