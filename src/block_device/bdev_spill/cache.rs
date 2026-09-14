//! Stripe residency and the single eviction/fetch operation.
//!
//! The cache owns placement and transfer buffers, but never guest requests or
//! the local I/O channel. It asks its caller to dispatch transfer I/O and receives
//! the corresponding completion. Everything runs on the same queue thread.
use super::{Geometry, WORK_PER_POLL};
use crate::{
    archive::ArchiveStore,
    block_device::{shared_buffer, SharedBuffer},
};
use log::error;
use sha2::{Digest, Sha256};
use std::time::{Duration, Instant};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum StripeState {
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
    state: StripeState,
    source: Source,
    active: u32,
    dirty: bool,
    accessed: u64,
}

/// Exactly one transfer I/O can be outstanding. The channel assigns its ID and
/// retains this operation until completion, just as it does for guest I/O.
#[derive(Clone, Copy)]
pub(super) enum TransferIo {
    ReadVictim { slot: usize },
    WriteSlot { slot: usize },
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

pub(super) struct StripeCache {
    store: Box<dyn ArchiveStore + Send>,
    geometry: Geometry,
    stripes: Vec<Stripe>,
    free: Vec<usize>,
    slot_owners: Vec<Option<usize>>,
    victim_cursor: usize,
    access: u64,
    transfer: Option<Transfer>,
    pending_io: Option<TransferIo>,
    failed_loads: Vec<usize>,
    buffer: SharedBuffer,
    next_object: u64,
    run: String,
    timeout: Duration,
    store_disabled: bool,
}

impl StripeCache {
    pub(super) fn new(
        store: Box<dyn ArchiveStore + Send>,
        geometry: Geometry,
        run: String,
        timeout: Duration,
    ) -> Self {
        Self {
            store,
            geometry,
            stripes: (0..geometry.stripes())
                .map(|_| Stripe {
                    state: StripeState::Absent,
                    source: Source::Zero,
                    active: 0,
                    dirty: false,
                    accessed: 0,
                })
                .collect(),
            free: (0..geometry.slots).rev().collect(),
            slot_owners: vec![None; geometry.slots],
            victim_cursor: 0,
            access: 0,
            transfer: None,
            pending_io: None,
            failed_loads: Vec::new(),
            buffer: shared_buffer(geometry.bytes()),
            next_object: 0,
            run,
            timeout,
            store_disabled: false,
        }
    }

    pub(super) fn state(&self, stripe: usize) -> StripeState {
        self.stripes[stripe].state
    }

    /// Admission counts delayed requests too, protecting a newly loaded slot
    /// until the channel has submitted and completed all of its waiting users.
    pub(super) fn admit(&mut self, stripe: usize) -> bool {
        let Some(access) = self.access.checked_add(1) else {
            return false;
        };
        self.access = access;
        let entry = &mut self.stripes[stripe];
        let Some(active) = entry.active.checked_add(1) else {
            return false;
        };
        entry.active = active;
        entry.accessed = access;
        true
    }

    pub(super) fn release(&mut self, stripe: usize) {
        let entry = &mut self.stripes[stripe];
        entry.active -= 1;
        if entry.active == 0 {
            if let StripeState::Failed(Some(slot)) = entry.state {
                entry.state = StripeState::Failed(None);
                self.slot_owners[slot] = None;
                self.free.push(slot);
            }
        }
    }

    pub(super) fn write_completed(&mut self, stripe: usize, success: bool) {
        let entry = &mut self.stripes[stripe];
        if success {
            entry.dirty = true;
        } else if let StripeState::Resident(slot) = entry.state {
            entry.state = StripeState::Failed(Some(slot));
        }
    }

    pub(super) fn busy(&self) -> bool {
        self.transfer.is_some()
    }

    pub(super) fn start_load(&mut self, stripe: usize) {
        debug_assert!(!self.busy());
        debug_assert_eq!(self.state(stripe), StripeState::Absent);
        self.stripes[stripe].state = StripeState::Loading;
        self.transfer = Some(Transfer {
            stripe,
            slot: None,
            victim: None,
            phase: Phase::NeedSlot,
            started: Instant::now(),
        });
    }

    pub(super) fn take_io(&mut self) -> Option<TransferIo> {
        self.pending_io.take()
    }

    pub(super) fn io_buffer(&self) -> SharedBuffer {
        self.buffer.clone()
    }

    pub(super) fn take_failed_loads(&mut self) -> Vec<usize> {
        std::mem::take(&mut self.failed_loads)
    }

    pub(super) fn complete_io(&mut self, operation: TransferIo, success: bool) {
        if !success {
            self.fail_transfer();
            return;
        }
        match operation {
            TransferIo::ReadVictim { .. } => self.victim_read(),
            TransferIo::WriteSlot { .. } => {
                let transfer = self.transfer.take().expect("fill transfer");
                self.stripes[transfer.stripe].state = StripeState::Resident(transfer.slot.unwrap());
                self.stripes[transfer.stripe].dirty = false;
            }
        }
    }

    fn victim_read(&mut self) {
        let Some(generation) = self.next_object.checked_add(1) else {
            self.fail_transfer();
            return;
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

    pub(super) fn advance(&mut self) {
        let Some(transfer) = self.transfer.as_ref() else {
            return;
        };
        if !matches!(transfer.phase, Phase::NeedSlot) {
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
            let Some((slot, victim)) = self.choose_victim() else {
                return;
            };
            self.stripes[victim].state = StripeState::Evicting(slot);
            if self.stripes[victim].dirty {
                let transfer = self.transfer.as_mut().unwrap();
                transfer.slot = Some(slot);
                transfer.victim = Some(victim);
                transfer.phase = Phase::Reading;
                self.pending_io = Some(TransferIo::ReadVictim { slot });
                return;
            }
            self.stripes[victim].state = StripeState::Absent;
            slot
        };
        self.transfer.as_mut().unwrap().slot = Some(slot);
        self.slot_owners[slot] = Some(stripe);
        self.fetch_source();
    }

    fn choose_victim(&mut self) -> Option<(usize, usize)> {
        // Sample slots, not the entire logical address space, each pass.
        let mut victim: Option<(usize, usize)> = None;
        for _ in 0..WORK_PER_POLL.min(self.geometry.slots) {
            let slot = self.victim_cursor;
            self.victim_cursor = (self.victim_cursor + 1) % self.geometry.slots;
            let Some(candidate) = self.slot_owners[slot] else {
                continue;
            };
            let entry = &self.stripes[candidate];
            if entry.state == StripeState::Resident(slot)
                && entry.active == 0
                && victim.is_none_or(|(_, old)| entry.accessed < self.stripes[old].accessed)
            {
                victim = Some((slot, candidate));
            }
        }
        victim
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
        self.pending_io = Some(TransferIo::WriteSlot {
            slot: transfer.slot.unwrap(),
        });
    }

    pub(super) fn poll_store(&mut self) {
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
            self.stripes[victim].state = StripeState::Absent;
            self.slot_owners[slot] = Some(stripe);
            self.transfer.as_mut().unwrap().victim = None;
            self.fetch_source();
        }
        for (name, result) in self.store.poll_gets() {
            let Some(transfer) = self.transfer.as_ref() else {
                continue;
            };
            if !matches!(&transfer.phase, Phase::Fetching { name: expected } if *expected == name) {
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
            self.stripes[victim].state = StripeState::Resident(transfer.slot.unwrap());
        } else if let Some(slot) = transfer.slot {
            self.free.push(slot);
            self.slot_owners[slot] = None;
        }
        self.stripes[transfer.stripe].state = StripeState::Absent;
        self.failed_loads.push(transfer.stripe);
    }

    /// Local I/O may still access the slot and buffer after submit fails.
    /// Cancel only phases that have no outstanding local operation.
    pub(super) fn abort_without_local_io(&mut self) {
        if self
            .transfer
            .as_ref()
            .is_some_and(|t| !matches!(t.phase, Phase::Reading | Phase::Writing))
        {
            self.fail_transfer();
        }
    }

    #[cfg(test)]
    pub(super) fn active_requests(&self, stripe: usize) -> u32 {
        self.stripes[stripe].active
    }

    #[cfg(test)]
    pub(super) fn all_requests_finished(&self) -> bool {
        self.stripes.iter().all(|s| s.active == 0)
    }

    #[cfg(test)]
    pub(super) fn free_slots(&self) -> usize {
        self.free.len()
    }

    #[cfg(test)]
    pub(super) fn dirty(&self, stripe: usize) -> bool {
        self.stripes[stripe].dirty
    }

    #[cfg(test)]
    pub(super) fn set_timeout(&mut self, timeout: Duration) {
        self.timeout = timeout;
    }
}
