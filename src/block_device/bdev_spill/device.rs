//! The device a spill layer presents, and the channel that serves it.
//!
//! Every request addresses one stripe. A request whose stripe is in a slot runs
//! against that slot; any other waits in the channel, which asks the worker to
//! bring the stripe in and looks again each time it is polled.

use std::collections::{HashMap, VecDeque};
use std::sync::mpsc::Sender;

use log::error;

use super::metadata::{Decision, SpillSharedMetadata};
use crate::backends::SECTOR_SIZE;
use crate::block_device::{BgWorkerRequest, BlockDevice, IoChannel, SharedBuffer};
use crate::Result;

pub struct SpillBlockDevice {
    base: Box<dyn BlockDevice>,
    metadata: SpillSharedMetadata,
    stripe_sectors: u64,
    sector_count: u64,
    worker: Sender<BgWorkerRequest>,
}

impl SpillBlockDevice {
    pub fn new(
        base: Box<dyn BlockDevice>,
        metadata: SpillSharedMetadata,
        stripe_sectors: u64,
        sector_count: u64,
        worker: Sender<BgWorkerRequest>,
    ) -> Box<Self> {
        Box::new(SpillBlockDevice {
            base,
            metadata,
            stripe_sectors,
            sector_count,
            worker,
        })
    }
}

impl BlockDevice for SpillBlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>> {
        Ok(Box::new(SpillIoChannel {
            base: self.base.create_channel()?,
            metadata: self.metadata.clone(),
            stripe_sectors: self.stripe_sectors,
            sector_count: self.sector_count,
            worker: self.worker.clone(),
            waiting: VecDeque::new(),
            in_flight: HashMap::new(),
            finished: Vec::new(),
        }))
    }

    fn sector_count(&self) -> u64 {
        self.sector_count
    }

    fn clone(&self) -> Box<dyn BlockDevice> {
        Box::new(SpillBlockDevice {
            base: self.base.clone(),
            metadata: self.metadata.clone(),
            stripe_sectors: self.stripe_sectors,
            sector_count: self.sector_count,
            worker: self.worker.clone(),
        })
    }
}

struct Request {
    id: usize,
    write: bool,
    sector: u64,
    sectors: u32,
    buf: SharedBuffer,
    stripe: usize,
    /// The fetch attempt this request is waiting on, if any.
    joined: Option<u64>,
}

struct SpillIoChannel {
    base: Box<dyn IoChannel>,
    metadata: SpillSharedMetadata,
    stripe_sectors: u64,
    sector_count: u64,
    worker: Sender<BgWorkerRequest>,
    waiting: VecDeque<Request>,
    in_flight: HashMap<usize, Request>,
    finished: Vec<(usize, bool)>,
}

impl SpillIoChannel {
    fn add(&mut self, write: bool, sector: u64, sectors: u32, buf: SharedBuffer, id: usize) {
        let end = sector.checked_add(sectors as u64);
        let valid = sectors > 0
            && end.is_some_and(|end| {
                end <= self.sector_count
                    && sector / self.stripe_sectors == (end - 1) / self.stripe_sectors
            })
            && buf.borrow().len() >= sectors as usize * SECTOR_SIZE;
        if !valid {
            error!("Spill refused request {id}: sectors {sector}+{sectors} are not within one stripe of the device");
            self.finished.push((id, false));
            return;
        }

        let mut request = Request {
            id,
            write,
            sector,
            sectors,
            buf,
            stripe: (sector / self.stripe_sectors) as usize,
            joined: None,
        };
        let decision = self.metadata.admit(request.stripe, &mut request.joined);
        self.act(request, decision);
    }

    fn act(&mut self, request: Request, decision: Decision) {
        match decision {
            Decision::Ready { slot } => {
                let sector =
                    slot as u64 * self.stripe_sectors + request.sector % self.stripe_sectors;
                if request.write {
                    self.base
                        .add_write(sector, request.sectors, request.buf.clone(), request.id);
                } else {
                    self.base
                        .add_read(sector, request.sectors, request.buf.clone(), request.id);
                }
                self.in_flight.insert(request.id, request);
            }
            Decision::Wait { fetch } => {
                if let Some(attempt) = fetch {
                    let asked = self.worker.send(BgWorkerRequest::SpillFetch {
                        stripe: request.stripe,
                        attempt,
                    });
                    if asked.is_err() {
                        error!(
                            "The spill worker is gone; failing stripe {}",
                            request.stripe
                        );
                        self.metadata.fail_attempt(request.stripe, attempt);
                    }
                }
                self.waiting.push_back(request);
            }
            Decision::Fail => self.finished.push((request.id, false)),
        }
    }

    fn retry_waiting(&mut self) {
        for _ in 0..self.waiting.len() {
            let Some(mut request) = self.waiting.pop_front() else {
                break;
            };
            let decision = self.metadata.retry(request.stripe, &mut request.joined);
            self.act(request, decision);
        }
    }

    fn submit_base(&mut self) {
        // What was added stays in flight either way: a failed submit does not
        // say the kernel took none of it, so the requests keep their slots
        // until they complete.
        if let Err(e) = self.base.submit() {
            error!("Failed to submit spill I/O: {e}");
        }
    }
}

impl IoChannel for SpillIoChannel {
    fn add_read(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        self.add(false, sector_offset, sector_count, buf, id);
    }

    fn add_write(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        self.add(true, sector_offset, sector_count, buf, id);
    }

    /// Nothing here is durable yet, so a flush has nothing to promise.
    fn add_flush(&mut self, id: usize) {
        self.finished.push((id, true));
    }

    fn submit(&mut self) -> Result<()> {
        self.submit_base();
        Ok(())
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        for (id, ok) in self.base.poll() {
            let Some(request) = self.in_flight.remove(&id) else {
                error!("Spill channel saw a completion for {id}, which it never sent");
                continue;
            };
            self.metadata.finish(request.stripe, request.write, ok);
            self.finished.push((id, ok));
        }
        if !self.waiting.is_empty() {
            self.retry_waiting();
            self.submit_base();
        }
        std::mem::take(&mut self.finished)
    }

    fn busy(&self) -> bool {
        !self.waiting.is_empty()
            || !self.in_flight.is_empty()
            || !self.finished.is_empty()
            || self.base.busy()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::archive::MemStore;
    use crate::block_device::bdev_spill::metadata::StripeState;
    use crate::block_device::bdev_spill::task::SpillTask;
    use crate::block_device::bdev_test::TestBlockDevice;
    use crate::block_device::shared_buffer;
    use std::sync::mpsc::{channel, Receiver};

    const STRIPE_SECTORS: u64 = 8;

    struct Stack {
        metadata: SpillSharedMetadata,
        disk: TestBlockDevice,
        channel: Box<dyn IoChannel>,
        task: SpillTask,
        requests: Receiver<BgWorkerRequest>,
        fetches_asked: usize,
        next_id: usize,
    }

    fn stack(sector_count: u64, slots: u32) -> Stack {
        let stripes = sector_count.div_ceil(STRIPE_SECTORS) as usize;
        let metadata = SpillSharedMetadata::new(stripes);
        let disk = TestBlockDevice::new(slots as u64 * STRIPE_SECTORS * SECTOR_SIZE as u64);
        let (sender, requests) = channel();
        let device = SpillBlockDevice::new(
            BlockDevice::clone(&disk),
            metadata.clone(),
            STRIPE_SECTORS,
            sector_count,
            sender,
        );
        let task = SpillTask::new(
            metadata.clone(),
            Box::new(MemStore::new()),
            disk.create_channel().unwrap(),
            STRIPE_SECTORS,
            slots,
            4,
            1,
        );
        Stack {
            metadata,
            channel: device.create_channel().unwrap(),
            disk,
            task,
            requests,
            fetches_asked: 0,
            next_id: 0,
        }
    }

    impl Stack {
        /// Poll the channel and run the worker, as the queue thread and the
        /// worker thread would, until the channel has nothing outstanding.
        fn run(&mut self) -> Vec<(usize, bool)> {
            let mut done = Vec::new();
            self.channel.submit().unwrap();
            for _ in 0..1000 {
                while let Ok(request) = self.requests.try_recv() {
                    if let BgWorkerRequest::SpillFetch { stripe, attempt } = request {
                        self.fetches_asked += 1;
                        self.task.handle_fetch_request(stripe, attempt);
                    }
                }
                self.task.update();
                done.extend(self.channel.poll());
                if !self.channel.busy() {
                    return done;
                }
            }
            panic!("the channel never settled");
        }

        fn id(&mut self) -> usize {
            self.next_id += 1;
            self.next_id
        }

        fn write(&mut self, sector: u64, sectors: u32, byte: u8) -> bool {
            let buf = shared_buffer(sectors as usize * SECTOR_SIZE);
            buf.borrow_mut().as_mut_slice().fill(byte);
            let id = self.id();
            self.channel.add_write(sector, sectors, buf, id);
            self.run() == vec![(id, true)]
        }

        fn read(&mut self, sector: u64, sectors: u32) -> Option<Vec<u8>> {
            let buf = shared_buffer(sectors as usize * SECTOR_SIZE);
            let id = self.id();
            self.channel.add_read(sector, sectors, buf.clone(), id);
            if self.run() == vec![(id, true)] {
                let data = buf.borrow().as_slice().to_vec();
                Some(data)
            } else {
                None
            }
        }
    }

    #[test]
    fn what_is_written_reads_back() {
        let mut s = stack(64, 2);
        assert!(s.write(19, 3, 0x5A));

        let data = s.read(16, 8).expect("read");
        assert!(data[..3 * SECTOR_SIZE].iter().all(|b| *b == 0));
        assert!(data[3 * SECTOR_SIZE..6 * SECTOR_SIZE]
            .iter()
            .all(|b| *b == 0x5A));
        assert!(data[6 * SECTOR_SIZE..].iter().all(|b| *b == 0));
    }

    /// The whole point: a device much larger than its slots keeps everything.
    #[test]
    fn more_stripes_than_slots_keep_their_contents() {
        let mut s = stack(80, 2);
        for stripe in 0..10u64 {
            assert!(s.write(stripe * STRIPE_SECTORS + 1, 1, 0x10 + stripe as u8));
        }
        for stripe in 0..10u64 {
            let data = s.read(stripe * STRIPE_SECTORS + 1, 1).expect("read");
            assert!(
                data.iter().all(|b| *b == 0x10 + stripe as u8),
                "stripe {stripe} came back as something else"
            );
        }
    }

    #[test]
    fn requests_the_device_cannot_serve_are_refused() {
        let mut s = stack(20, 2);
        let cases = [
            ("crossing a stripe", 6, 4, 4),
            ("past the end", 19, 2, 2),
            ("wrapping around", u64::MAX, 1, 1),
            ("empty", 0, 0, 1),
            ("a short buffer", 0, 4, 2),
        ];
        for (what, sector, sectors, buffer_sectors) in cases {
            let id = s.id();
            let buf = shared_buffer(buffer_sectors * SECTOR_SIZE);
            s.channel.add_read(sector, sectors, buf, id);
            assert_eq!(s.run(), vec![(id, false)], "{what} was accepted");
        }
        assert_eq!(s.metadata.get(0).active_requests, 0);
        assert_eq!(s.fetches_asked, 0);
    }

    /// The last stripe of a device that does not end on a stripe boundary is
    /// usable up to the end, and no further.
    #[test]
    fn a_short_final_stripe_serves_up_to_the_end() {
        let mut s = stack(20, 1);
        assert!(s.write(19, 1, 0x77));
        assert!(s.write(0, 1, 0x11));
        assert_eq!(s.read(19, 1).expect("read"), vec![0x77; SECTOR_SIZE]);
        assert!(s.read(19, 2).is_none());
    }

    #[test]
    fn requests_waiting_on_one_stripe_ask_for_it_once() {
        let mut s = stack(64, 2);
        let (first, second) = (s.id(), s.id());
        s.channel.add_read(0, 1, shared_buffer(SECTOR_SIZE), first);
        s.channel.add_read(1, 1, shared_buffer(SECTOR_SIZE), second);

        let mut done = s.run();
        done.sort();
        assert_eq!(done, vec![(first, true), (second, true)]);
        assert_eq!(s.fetches_asked, 1);
        assert_eq!(s.metadata.get(0).active_requests, 0);
    }

    #[test]
    fn a_flush_completes_without_touching_any_stripe() {
        let mut s = stack(64, 2);
        let id = s.id();
        s.channel.add_flush(id);
        assert_eq!(s.run(), vec![(id, true)]);
        assert_eq!(s.fetches_asked, 0);
    }

    #[test]
    fn a_failed_write_fails_the_stripe() {
        let mut s = stack(64, 2);
        assert!(s.write(0, 1, 0x22));
        s.disk
            .fail_next
            .store(true, std::sync::atomic::Ordering::SeqCst);

        assert!(!s.write(1, 1, 0x33));

        assert!(matches!(
            s.metadata.get(0).state,
            StripeState::Failed { .. }
        ));
        assert!(s.read(0, 1).is_none());
        assert!(s.read(8, 1).is_some(), "another stripe was affected");
    }

    #[test]
    fn a_request_fails_rather_than_waits_when_the_worker_is_gone() {
        let mut s = stack(64, 2);
        let (sender, requests) = channel();
        drop(requests);
        s.channel = SpillBlockDevice::new(
            BlockDevice::clone(&s.disk),
            s.metadata.clone(),
            STRIPE_SECTORS,
            64,
            sender,
        )
        .create_channel()
        .unwrap();

        assert!(s.read(0, 1).is_none());
        assert_eq!(s.metadata.get(0).active_requests, 0);
    }
}
