use super::Geometry;
use crate::{
    archive::ArchiveStore,
    block_device::{shared_buffer, IoChannel, SharedBuffer},
    Result,
};
use log::error;
use sha2::{Digest, Sha256};
use std::{
    collections::{HashMap, VecDeque},
    time::{Duration, Instant},
};

const WORK_PER_POLL: usize = 64;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum State {
    Absent,
    Resident(usize),
    Loading,
    Evicting(usize),
    Failed(Option<usize>),
}
#[derive(Clone)]
enum Source {
    Zero,
    Object { name: String, digest: [u8; 32] },
}
pub(super) struct Stripe {
    state: State,
    source: Source,
    active: u32,
    dirty: bool,
    accessed: u64,
}
struct Request {
    id: usize,
    stripe: usize,
    within: u64,
    sectors: u32,
    write: bool,
    buffer: SharedBuffer,
}
enum LocalIo {
    Guest(Request),
    ReadVictim,
    Fill,
}
enum Phase {
    NeedSlot,
    Reading,
    Uploading { name: String, digest: [u8; 32] },
    Fetching { name: String },
    Writing,
}
struct Transfer {
    stripe: usize,
    slot: Option<usize>,
    victim: Option<usize>,
    phase: Phase,
    started: Instant,
}

pub(crate) struct SpillIoChannel {
    // Drop the kernel channel before any memory it may still be accessing.
    base: Box<dyn IoChannel>,
    store: Box<dyn ArchiveStore + Send>,
    geometry: Geometry,
    stripes: Vec<Stripe>,
    free: Vec<usize>,
    queue: VecDeque<Request>,
    local: HashMap<usize, LocalIo>,
    transfer: Option<Transfer>,
    buffer: SharedBuffer,
    finished: Vec<(usize, bool)>,
    next_io: usize,
    access: u64,
    next_object: u64,
    run: String,
    timeout: Duration,
    halted: bool,
    store_disabled: bool,
    victim_cursor: usize,
    slot_owners: Vec<Option<usize>>,
}

impl SpillIoChannel {
    pub(super) fn new(
        base: Box<dyn IoChannel>,
        store: Box<dyn ArchiveStore + Send>,
        geometry: Geometry,
        run: String,
        timeout: Duration,
    ) -> Self {
        Self {
            base,
            store,
            geometry,
            stripes: (0..geometry.stripes())
                .map(|_| Stripe {
                    state: State::Absent,
                    source: Source::Zero,
                    active: 0,
                    dirty: false,
                    accessed: 0,
                })
                .collect(),
            free: (0..geometry.slots).rev().collect(),
            queue: VecDeque::new(),
            local: HashMap::new(),
            transfer: None,
            buffer: shared_buffer(geometry.bytes()),
            finished: Vec::new(),
            next_io: 0,
            access: 0,
            next_object: 0,
            run,
            timeout,
            halted: false,
            store_disabled: false,
            victim_cursor: 0,
            slot_owners: vec![None; geometry.slots],
        }
    }

    fn add(&mut self, sector: u64, sectors: u32, buffer: SharedBuffer, id: usize, write: bool) {
        let valid = sector
            .checked_add(u64::from(sectors))
            .is_some_and(|end| end <= self.geometry.device_sectors)
            && (sector % self.geometry.stripe_sectors) + u64::from(sectors)
                <= self.geometry.stripe_sectors
            && sectors as usize * 512 <= buffer.borrow().len();
        if !valid || self.halted {
            self.finished.push((id, false));
            return;
        }
        if sectors == 0 {
            self.finished.push((id, true));
            return;
        }
        let stripe = (sector / self.geometry.stripe_sectors) as usize;
        let Some(access) = self.access.checked_add(1) else {
            self.finished.push((id, false));
            return;
        };
        self.access = access;
        let entry = &mut self.stripes[stripe];
        let Some(active) = entry.active.checked_add(1) else {
            self.finished.push((id, false));
            return;
        };
        entry.active = active;
        entry.accessed = access;
        self.queue.push_back(Request {
            id,
            stripe,
            within: sector % self.geometry.stripe_sectors,
            sectors,
            write,
            buffer,
        });
    }

    fn finish(&mut self, request: Request, success: bool) {
        let stripe = &mut self.stripes[request.stripe];
        stripe.active -= 1;
        if stripe.active == 0 {
            if let State::Failed(Some(slot)) = stripe.state {
                stripe.state = State::Failed(None);
                self.slot_owners[slot] = None;
                self.free.push(slot);
            }
        }
        self.finished.push((request.id, success));
    }

    fn local_id(&mut self, op: LocalIo) -> usize {
        let id = self.next_io;
        self.next_io = self.next_io.checked_add(1).expect("spill I/O ID exhausted");
        self.local.insert(id, op);
        id
    }

    fn advance_requests(&mut self) {
        for _ in 0..self.queue.len().min(WORK_PER_POLL) {
            let request = self.queue.pop_front().expect("counted queue");
            match self.stripes[request.stripe].state {
                _ if self.halted => self.finish(request, false),
                State::Failed(_) => self.finish(request, false),
                State::Resident(slot) => {
                    let sector = slot as u64 * self.geometry.stripe_sectors + request.within;
                    let (sectors, write, buffer) =
                        (request.sectors, request.write, request.buffer.clone());
                    let id = self.local_id(LocalIo::Guest(request));
                    if write {
                        self.base.add_write(sector, sectors, buffer, id);
                    } else {
                        self.base.add_read(sector, sectors, buffer, id);
                    }
                }
                _ => self.queue.push_back(request),
            }
        }
    }

    fn submit_base(&mut self) {
        if let Err(e) = self.base.submit() {
            error!("Spill submission failed; retaining outstanding buffers and slots: {e}");
            self.halted = true;
        }
    }

    fn poll_local(&mut self) {
        for (id, success) in self.base.poll() {
            let Some(op) = self.local.remove(&id) else {
                error!("Unexpected spill completion {id}");
                continue;
            };
            let success = success && !self.halted;
            match op {
                LocalIo::Guest(request) => {
                    if request.write {
                        let stripe = &mut self.stripes[request.stripe];
                        if success {
                            stripe.dirty = true;
                        } else if let State::Resident(slot) = stripe.state {
                            stripe.state = State::Failed(Some(slot));
                        }
                    }
                    self.finish(request, success);
                }
                LocalIo::ReadVictim => {
                    if !success {
                        self.fail_transfer();
                        continue;
                    }
                    let Some(generation) = self.next_object.checked_add(1) else {
                        self.fail_transfer();
                        continue;
                    };
                    self.next_object = generation;
                    let transfer = self.transfer.as_ref().expect("victim transfer");
                    let victim = transfer.victim.expect("victim");
                    let name = format!("{}/stripe-{victim}/{generation}", self.run);
                    let data = self.buffer.borrow().as_slice().to_vec();
                    let digest = Sha256::digest(&data).into();
                    self.store.start_put_object(&name, data);
                    let transfer = self.transfer.as_mut().unwrap();
                    transfer.phase = Phase::Uploading { name, digest };
                    transfer.started = Instant::now();
                }
                LocalIo::Fill => {
                    if !success {
                        self.fail_transfer();
                        continue;
                    }
                    let transfer = self.transfer.take().expect("fill transfer");
                    self.stripes[transfer.stripe].state = State::Resident(transfer.slot.unwrap());
                    self.stripes[transfer.stripe].dirty = false;
                }
            }
        }
    }

    fn start_transfer(&mut self) {
        if self.transfer.is_some() || self.halted {
            return;
        }
        // Queue order is enough here; retries rotate only a bounded batch.
        let Some(stripe) = self
            .queue
            .iter()
            .take(WORK_PER_POLL)
            .find(|r| self.stripes[r.stripe].state == State::Absent)
            .map(|r| r.stripe)
        else {
            return;
        };
        self.stripes[stripe].state = State::Loading;
        self.transfer = Some(Transfer {
            stripe,
            slot: None,
            victim: None,
            phase: Phase::NeedSlot,
            started: Instant::now(),
        });
    }

    fn advance_transfer(&mut self) {
        let Some(transfer) = self.transfer.as_ref() else {
            return;
        };
        if !matches!(transfer.phase, Phase::NeedSlot) || self.halted {
            return;
        }
        let stripe = transfer.stripe;
        if self.store_disabled {
            self.fail_transfer();
            return;
        }
        let slot = if let Some(slot) = self.free.pop() {
            slot
        } else {
            // Sample slots, not the entire logical address space, each pass.
            let mut victim: Option<(usize, usize)> = None;
            for _ in 0..WORK_PER_POLL.min(self.geometry.slots) {
                let slot = self.victim_cursor;
                self.victim_cursor = (self.victim_cursor + 1) % self.geometry.slots;
                let Some(candidate) = self.slot_owners[slot] else {
                    continue;
                };
                let entry = &self.stripes[candidate];
                if entry.state == State::Resident(slot)
                    && entry.active == 0
                    && victim.is_none_or(|(_, old)| entry.accessed < self.stripes[old].accessed)
                {
                    victim = Some((slot, candidate));
                }
            }
            let Some((slot, victim)) = victim else {
                return;
            };
            self.stripes[victim].state = State::Evicting(slot);
            if self.stripes[victim].dirty {
                let transfer = self.transfer.as_mut().unwrap();
                transfer.slot = Some(slot);
                transfer.victim = Some(victim);
                transfer.phase = Phase::Reading;
                let id = self.local_id(LocalIo::ReadVictim);
                self.base.add_read(
                    slot as u64 * self.geometry.stripe_sectors,
                    self.geometry.stripe_sectors as u32,
                    self.buffer.clone(),
                    id,
                );
                return;
            }
            self.stripes[victim].state = State::Absent;
            slot
        };
        self.transfer.as_mut().unwrap().slot = Some(slot);
        self.slot_owners[slot] = Some(stripe);
        self.fetch_source();
    }

    fn fetch_source(&mut self) {
        let stripe = self.transfer.as_ref().unwrap().stripe;
        match self.stripes[stripe].source.clone() {
            Source::Zero => {
                self.buffer.borrow_mut().as_mut_slice().fill(0);
                self.write_fill();
            }
            Source::Object { name, .. } => {
                self.store.start_get_object(&name);
                let transfer = self.transfer.as_mut().unwrap();
                transfer.phase = Phase::Fetching { name };
                transfer.started = Instant::now();
            }
        }
    }

    fn write_fill(&mut self) {
        let transfer = self.transfer.as_mut().unwrap();
        transfer.phase = Phase::Writing;
        let slot = transfer.slot.unwrap();
        let id = self.local_id(LocalIo::Fill);
        self.base.add_write(
            slot as u64 * self.geometry.stripe_sectors,
            self.geometry.stripe_sectors as u32,
            self.buffer.clone(),
            id,
        );
    }

    fn poll_store(&mut self) {
        for (name, result) in self.store.poll_puts() {
            let Some(transfer) = self.transfer.as_ref() else {
                continue;
            };
            let Phase::Uploading {
                name: expected,
                digest,
            } = &transfer.phase
            else {
                continue;
            };
            if *expected != name {
                continue;
            }
            if let Err(e) = result {
                error!("Spill upload failed: {e}");
                self.fail_transfer();
                continue;
            }
            let (stripe, slot, victim, digest) = (
                transfer.stripe,
                transfer.slot.unwrap(),
                transfer.victim.unwrap(),
                *digest,
            );
            self.stripes[victim].source = Source::Object { name, digest };
            self.stripes[victim].dirty = false;
            self.stripes[victim].state = State::Absent;
            self.slot_owners[slot] = Some(stripe);
            self.transfer.as_mut().unwrap().victim = None;
            self.fetch_source();
        }
        for (name, result) in self.store.poll_gets() {
            let Some(transfer) = self.transfer.as_ref() else {
                continue;
            };
            if !matches!(&transfer.phase,Phase::Fetching{name:expected} if *expected==name) {
                continue;
            }
            let Source::Object { digest, .. } = self.stripes[transfer.stripe].source else {
                unreachable!()
            };
            match result {
                Ok(data)
                    if data.len() == self.geometry.bytes()
                        && <[u8; 32]>::from(Sha256::digest(&data)) == digest =>
                {
                    self.buffer
                        .borrow_mut()
                        .as_mut_slice()
                        .copy_from_slice(&data);
                    self.write_fill();
                }
                _ => {
                    error!("Spill fetch failed or returned an invalid stripe");
                    self.fail_transfer();
                }
            }
        }
        if self.transfer.as_ref().is_some_and(|t| {
            matches!(t.phase, Phase::Fetching { .. } | Phase::Uploading { .. })
                && t.started.elapsed() >= self.timeout
        }) {
            // The adapter has no cancellation. Do not accumulate abandoned store jobs.
            self.store_disabled = true;
            self.fail_transfer();
        }
    }

    fn fail_transfer(&mut self) {
        let Some(transfer) = self.transfer.take() else {
            return;
        };
        if let Some(victim) = transfer.victim {
            self.stripes[victim].state = State::Resident(transfer.slot.unwrap());
        } else if let Some(slot) = transfer.slot {
            self.free.push(slot);
            self.slot_owners[slot] = None;
        }
        self.stripes[transfer.stripe].state = State::Absent;
        // One owner: drain this attempt's waiters before another request can join.
        let mut waiting = std::mem::take(&mut self.queue);
        while let Some(request) = waiting.pop_front() {
            if request.stripe == transfer.stripe {
                self.finish(request, false);
            } else {
                self.queue.push_back(request);
            }
        }
    }

    fn settle_halted_transfer(&mut self) {
        if self.halted
            && self
                .transfer
                .as_ref()
                .is_some_and(|t| !matches!(t.phase, Phase::Reading | Phase::Writing))
        {
            self.fail_transfer();
        }
    }

    fn advance(&mut self) {
        self.settle_halted_transfer();
        self.advance_requests();
        self.start_transfer();
        self.advance_transfer();
        if !self.halted {
            self.submit_base();
        }
    }
}

impl IoChannel for SpillIoChannel {
    fn add_read(&mut self, sector: u64, sectors: u32, buffer: SharedBuffer, id: usize) {
        self.add(sector, sectors, buffer, id, false);
    }
    fn add_write(&mut self, sector: u64, sectors: u32, buffer: SharedBuffer, id: usize) {
        self.add(sector, sectors, buffer, id, true);
    }
    fn add_flush(&mut self, id: usize) {
        self.finished.push((id, !self.halted));
    }
    fn submit(&mut self) -> Result<()> {
        self.advance();
        Ok(())
    }
    fn poll(&mut self) -> Vec<(usize, bool)> {
        self.poll_local();
        self.settle_halted_transfer();
        self.poll_store();
        self.advance();
        std::mem::take(&mut self.finished)
    }
    fn busy(&self) -> bool {
        !self.queue.is_empty()
            || !self.local.is_empty()
            || self.transfer.is_some()
            || !self.finished.is_empty()
    }
}

#[cfg(test)]
#[path = "tests.rs"]
mod tests;
