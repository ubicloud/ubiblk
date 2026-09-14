//! Guest request admission, local I/O dispatch, and frontend completions.
//!
//! StripeCache owns placement and transfer progress. The channel owns the one
//! local I/O stream and keeps guest buffers alive until their completions arrive.
use super::{
    cache::{StripeCache, StripeState, TransferIo},
    Geometry, WORK_PER_POLL,
};
use crate::{
    archive::ArchiveStore,
    block_device::{IoChannel, SharedBuffer},
    Result,
};
use log::error;
use std::{
    collections::{HashMap, VecDeque},
    time::Duration,
};

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
    Transfer(TransferIo),
}

pub(crate) struct SpillIoChannel {
    // Drop the kernel channel before any memory it may still be accessing.
    base: Box<dyn IoChannel>,
    cache: StripeCache,
    geometry: Geometry,
    queue: VecDeque<Request>,
    local: HashMap<usize, LocalIo>,
    finished: Vec<(usize, bool)>,
    next_io: usize,
    halted: bool,
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
            cache: StripeCache::new(store, geometry, run, timeout),
            geometry,
            queue: VecDeque::new(),
            local: HashMap::new(),
            finished: Vec::new(),
            next_io: 0,
            halted: false,
        }
    }

    fn add(&mut self, sector: u64, sectors: u32, buffer: SharedBuffer, id: usize, write: bool) {
        let valid = sector
            .checked_add(u64::from(sectors))
            .is_some_and(|end| end <= self.geometry.device_sectors)
            && sector % self.geometry.stripe_sectors + u64::from(sectors)
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
        if !self.cache.admit(stripe) {
            self.finished.push((id, false));
            return;
        }
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
        self.cache.release(request.stripe);
        self.finished.push((request.id, success));
    }

    fn local_id(&mut self, operation: LocalIo) -> usize {
        let id = self.next_io;
        self.next_io = self.next_io.checked_add(1).expect("spill I/O ID exhausted");
        self.local.insert(id, operation);
        id
    }

    fn advance_requests(&mut self) {
        for _ in 0..self.queue.len().min(WORK_PER_POLL) {
            let request = self.queue.pop_front().expect("counted queue");
            match self.cache.state(request.stripe) {
                _ if self.halted => self.finish(request, false),
                StripeState::Failed(_) => self.finish(request, false),
                StripeState::Resident(slot) => self.submit_request(request, slot),
                _ => self.queue.push_back(request),
            }
        }
    }

    fn submit_request(&mut self, request: Request, slot: usize) {
        let sector = slot as u64 * self.geometry.stripe_sectors + request.within;
        let (sectors, write, buffer) = (request.sectors, request.write, request.buffer.clone());
        let id = self.local_id(LocalIo::Guest(request));
        if write {
            self.base.add_write(sector, sectors, buffer, id);
        } else {
            self.base.add_read(sector, sectors, buffer, id);
        }
    }

    fn submit_transfer_io(&mut self) {
        let Some(operation) = self.cache.take_io() else {
            return;
        };
        let id = self.local_id(LocalIo::Transfer(operation));
        let buffer = self.cache.io_buffer();
        let sectors = self.geometry.stripe_sectors as u32;
        match operation {
            TransferIo::ReadVictim { slot } => self.base.add_read(
                slot as u64 * self.geometry.stripe_sectors,
                sectors,
                buffer,
                id,
            ),
            TransferIo::WriteSlot { slot } => self.base.add_write(
                slot as u64 * self.geometry.stripe_sectors,
                sectors,
                buffer,
                id,
            ),
        }
    }

    fn submit_base(&mut self) {
        if let Err(error) = self.base.submit() {
            error!("Spill submission failed; retaining outstanding buffers and slots: {error}");
            self.halted = true;
        }
    }

    fn poll_local(&mut self) {
        for (id, success) in self.base.poll() {
            let Some(operation) = self.local.remove(&id) else {
                error!("Unexpected spill completion {id}");
                continue;
            };
            let success = success && !self.halted;
            match operation {
                LocalIo::Guest(request) => {
                    if request.write {
                        self.cache.write_completed(request.stripe, success);
                    }
                    self.finish(request, success);
                }
                LocalIo::Transfer(operation) => {
                    self.cache.complete_io(operation, success);
                    self.complete_failed_loads();
                }
            }
        }
    }

    fn start_load(&mut self) {
        if self.cache.busy() || self.halted {
            return;
        }
        if let Some(stripe) = self
            .queue
            .iter()
            .take(WORK_PER_POLL)
            .find(|request| self.cache.state(request.stripe) == StripeState::Absent)
            .map(|request| request.stripe)
        {
            self.cache.start_load(stripe);
        }
    }

    fn complete_failed_loads(&mut self) {
        for stripe in self.cache.take_failed_loads() {
            // Drain this attempt's waiters before another frontend request can
            // join. The cache does not need to know about guest request IDs.
            let mut waiting = std::mem::take(&mut self.queue);
            while let Some(request) = waiting.pop_front() {
                if request.stripe == stripe {
                    self.finish(request, false);
                } else {
                    self.queue.push_back(request);
                }
            }
        }
    }

    fn settle_halted_transfer(&mut self) {
        if self.halted {
            self.cache.abort_without_local_io();
            self.complete_failed_loads();
        }
    }

    fn advance(&mut self) {
        self.settle_halted_transfer();
        self.advance_requests();
        self.start_load();
        if !self.halted {
            self.cache.advance();
        }
        self.complete_failed_loads();
        self.submit_transfer_io();
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
        self.cache.poll_store();
        self.complete_failed_loads();
        self.submit_transfer_io();
        self.advance();
        std::mem::take(&mut self.finished)
    }
    fn busy(&self) -> bool {
        !self.queue.is_empty()
            || !self.local.is_empty()
            || self.cache.busy()
            || !self.finished.is_empty()
    }
}

#[cfg(test)]
#[path = "tests.rs"]
mod tests;
