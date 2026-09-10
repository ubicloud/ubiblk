//! The thread block devices do their background work on.
//!
//! One thread serves them all. A device registers a task and gets a queue to
//! send it work on; the loop waits while nothing is in flight and polls while
//! something is, so an idle task costs nothing and a busy one keeps its
//! neighbours from sleeping.

use std::ops::ControlFlow;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{channel, Receiver, SendError, Sender, TryRecvError};
use std::sync::Arc;

use log::error;

/// One device's background work.
pub trait BgTask {
    type Request;

    /// Act on a request.
    fn handle(&mut self, request: Self::Request);

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
                Ok(request) => self.task.handle(request),
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

/// Ends the run, whatever the tasks are up to.
#[derive(Clone)]
pub struct BgStopper {
    stopped: Arc<AtomicBool>,
    wakeup: Sender<()>,
}

impl BgStopper {
    pub fn stop(&self) {
        self.stopped.store(true, Ordering::SeqCst);
        let _ = self.wakeup.send(());
    }
}

/// Hands out queues before the worker exists: a device needs its sender at
/// build time, while the tasks are built on the worker's own thread.
pub struct BgQueues {
    stopped: Arc<AtomicBool>,
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
            stopped: Arc::new(AtomicBool::new(false)),
            wakeup_sender,
            wakeup,
        }
    }

    pub fn stopper(&self) -> BgStopper {
        BgStopper {
            stopped: self.stopped.clone(),
            wakeup: self.wakeup_sender.clone(),
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
    stopped: Arc<AtomicBool>,
    wakeup: Receiver<()>,
    /// The queues' side of the wakeup channel, dropped once the worker runs so
    /// that a wait ends when the last sender goes away.
    wakeup_sender: Option<Sender<()>>,
}

impl BgWorker {
    pub fn new(queues: BgQueues) -> Self {
        BgWorker {
            tasks: Vec::new(),
            stopped: queues.stopped,
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
        while !self.tasks.is_empty() && !self.stopped.load(Ordering::SeqCst) {
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

    struct Note(u32);

    type Log = Rc<RefCell<Vec<u32>>>;

    #[derive(Default)]
    struct Recorder {
        handled: Log,
        updates: Rc<RefCell<usize>>,
        busy: bool,
    }

    impl BgTask for Recorder {
        type Request = Note;

        fn handle(&mut self, Note(n): Note) {
            self.handled.borrow_mut().push(n);
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

        to_first.send(Note(1)).unwrap();
        to_second.send(Note(2)).unwrap();
        to_first.send(Note(3)).unwrap();
        worker.receive_requests(false);

        assert_eq!(*first.borrow(), vec![1, 3]);
        assert_eq!(*second.borrow(), vec![2]);
    }

    /// Nobody is left to send to that task, and waiting for a request that
    /// cannot arrive would keep the thread alive for the life of the process.
    /// The tasks that still have senders carry on.
    #[test]
    fn a_queue_with_no_senders_retires_only_its_own_task() {
        let queues = BgQueues::new();
        let (to_quitter, quitter_requests) = queues.queue::<Note>();
        let (to_survivor, survivor_requests) = queues.queue();
        let survived = Log::default();
        let mut worker = BgWorker::new(queues);
        worker.add(Recorder::default(), quitter_requests);
        worker.add(recorder(&survived), survivor_requests);

        drop(to_quitter);
        worker.receive_requests(false);
        to_survivor.send(Note(1)).unwrap();
        worker.receive_requests(false);

        assert_eq!(worker.tasks.len(), 1);
        assert_eq!(*survived.borrow(), vec![1]);
    }

    #[test]
    fn a_stopper_ends_the_run_with_its_tasks_still_queued() {
        let queues = BgQueues::new();
        let (sender, requests) = queues.queue::<Note>();
        // Held no longer than the call: a live stopper is a live wakeup sender.
        queues.stopper().stop();
        let mut worker = BgWorker::new(queues);
        worker.add(Recorder::default(), requests);

        // A worker that ignores the stop waits here for a request that is not
        // coming; retiring the task frees it, and the count below then fails
        // rather than the test hanging.
        std::thread::spawn(move || {
            std::thread::sleep(Duration::from_secs(1));
            drop(sender);
        });
        worker.run();

        assert_eq!(worker.tasks.len(), 1);
    }

    /// Without this the worker would sit in `wait` until something unrelated
    /// happened to send it a request.
    #[test]
    fn stopping_wakes_a_waiting_worker() {
        let queues = BgQueues::new();
        let stopper = queues.stopper();

        stopper.stop();

        assert!(queues.wakeup.try_recv().is_ok());
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

        // Nothing is queued, so a worker that waits before looking at what is
        // in flight is still waiting when its queue is dropped, having never
        // updated the task.
        std::thread::spawn(move || {
            std::thread::sleep(Duration::from_millis(50));
            drop(sender);
        });
        worker.run();

        assert!(*updates.borrow() >= 1);
    }
}
