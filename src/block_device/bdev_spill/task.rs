//! The background work of a spill device: bringing stripes into slots and
//! moving them out to the object store.

use std::collections::{HashMap, VecDeque};
use std::time::{Duration, Instant};

use log::{error, warn};

use super::metadata::{SlotId, SpillSharedMetadata};
use crate::archive::ArchiveStore;
use crate::backends::SECTOR_SIZE;
use crate::block_device::{IoChannel, SharedBuffer};
use crate::utils::{aligned_buffer_pool::AlignedBufferPool, hash::sha256_bytes};

/// How long a round trip to the store may take before its transfer fails.
const STORE_DEADLINE: Duration = Duration::from_secs(120);

/// Evictions that may fail in a row before fetches waiting for a slot fail.
const MAX_EVICTION_FAILURES: u32 = 3;

/// Slots looked at per pass when choosing a victim.
const VICTIM_BATCH: usize = 64;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Slot {
    Free,
    Filling(usize),
    Held(usize),
    Draining(usize),
}

/// Where an evicted stripe's bytes are. A stripe with none has never been
/// uploaded, and reads as zeroes.
struct Object {
    name: String,
    digest: [u8; 32],
}

enum FetchState {
    Queued,
    Fetching {
        name: String,
        digest: [u8; 32],
        since: Instant,
    },
    WritingSlot,
}

struct Fetch {
    attempt: u64,
    slot: Option<SlotId>,
    buffer: Option<SharedBuffer>,
    state: FetchState,
}

enum EvictState {
    ReadingSlot,
    Uploading {
        name: String,
        digest: [u8; 32],
        since: Instant,
    },
}

struct Evict {
    slot: SlotId,
    buffer: SharedBuffer,
    state: EvictState,
}

pub struct SpillTask {
    metadata: SpillSharedMetadata,
    store: Box<dyn ArchiveStore>,
    channel: Box<dyn IoChannel>,
    stripe_sectors: u64,
    run_id: String,
    buffers: AlignedBufferPool,
    slots: Vec<Slot>,
    free_slots: Vec<SlotId>,
    objects: HashMap<usize, Object>,
    fetch_queue: VecDeque<usize>,
    fetches: HashMap<usize, Fetch>,
    evictions: HashMap<usize, Evict>,
    next_object: u64,
    eviction_failures: u32,
    cursor: usize,
    deadline: Duration,
}

impl SpillTask {
    pub fn new(
        metadata: SpillSharedMetadata,
        store: Box<dyn ArchiveStore>,
        channel: Box<dyn IoChannel>,
        stripe_sectors: u64,
        slot_count: u32,
        max_transfers: usize,
        alignment: usize,
    ) -> Self {
        let mut run_id = [0u8; 8];
        if let Err(e) = openssl::rand::rand_bytes(&mut run_id) {
            warn!("Failed to pick a random run id, using the time instead: {e}");
            let now = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default();
            run_id = (now.as_nanos() as u64).to_le_bytes();
        }
        SpillTask {
            metadata,
            store,
            channel,
            stripe_sectors,
            run_id: hex::encode(run_id),
            buffers: AlignedBufferPool::new(
                alignment,
                max_transfers,
                stripe_sectors as usize * SECTOR_SIZE,
            ),
            slots: vec![Slot::Free; slot_count as usize],
            free_slots: (0..slot_count).rev().collect(),
            objects: HashMap::new(),
            fetch_queue: VecDeque::new(),
            fetches: HashMap::new(),
            evictions: HashMap::new(),
            next_object: 0,
            eviction_failures: 0,
            cursor: 0,
            deadline: STORE_DEADLINE,
        }
    }

    pub fn busy(&self) -> bool {
        !self.fetches.is_empty() || !self.evictions.is_empty() || self.channel.busy()
    }

    pub fn handle_fetch_request(&mut self, stripe: usize, attempt: u64) {
        if self.fetches.contains_key(&stripe) {
            return;
        }
        self.fetches.insert(
            stripe,
            Fetch {
                attempt,
                slot: None,
                buffer: None,
                state: FetchState::Queued,
            },
        );
        self.fetch_queue.push_back(stripe);
    }

    pub fn update(&mut self) {
        self.poll_channel();
        self.poll_store();
        self.check_deadlines();
        self.start_fetches();
        self.make_room();
    }

    fn slot_sector(&self, slot: SlotId) -> u64 {
        slot as u64 * self.stripe_sectors
    }

    fn release_slot(&mut self, slot: SlotId) {
        self.slots[slot as usize] = Slot::Free;
        self.free_slots.push(slot);
    }

    fn start_fetches(&mut self) {
        let mut waiting = VecDeque::new();
        while let Some(stripe) = self.fetch_queue.pop_front() {
            let Some(fetch) = self.fetches.get(&stripe) else {
                continue;
            };
            if !self.metadata.is_loading(stripe, fetch.attempt) {
                if let Some(slot) = self.fetches.remove(&stripe).and_then(|fetch| fetch.slot) {
                    self.release_slot(slot);
                }
                continue;
            }

            // A slot first, then a buffer: a fetch never holds a buffer while
            // it waits for an eviction to free a slot.
            if fetch.slot.is_none() {
                let Some(slot) = self.free_slots.pop() else {
                    waiting.push_back(stripe);
                    continue;
                };
                self.slots[slot as usize] = Slot::Filling(stripe);
                self.fetches.get_mut(&stripe).expect("fetch").slot = Some(slot);
            }
            let Some(buffer) = self.buffers.get_buffer() else {
                waiting.push_back(stripe);
                continue;
            };

            let fetch = self.fetches.get_mut(&stripe).expect("fetch");
            fetch.buffer = Some(buffer.clone());
            match self.objects.get(&stripe) {
                None => {
                    buffer.borrow_mut().as_mut_slice().fill(0);
                    self.write_slot(stripe);
                }
                Some(Object { name, digest }) => {
                    fetch.state = FetchState::Fetching {
                        name: name.clone(),
                        digest: *digest,
                        since: Instant::now(),
                    };
                    self.store.start_get_object(name);
                }
            }
        }
        self.fetch_queue = waiting;
    }

    fn write_slot(&mut self, stripe: usize) {
        let fetch = self.fetches.get_mut(&stripe).expect("fetch");
        fetch.state = FetchState::WritingSlot;
        let slot = fetch.slot.expect("a fetch writing has a slot");
        let buffer = fetch.buffer.clone().expect("a fetch writing has a buffer");
        let sector = self.slot_sector(slot);
        self.channel
            .add_write(sector, self.stripe_sectors as u32, buffer, stripe * 2);
        if let Err(e) = self.channel.submit() {
            error!("Failed to submit the fill of stripe {stripe}: {e}");
        }
    }

    fn poll_channel(&mut self) {
        for (id, ok) in self.channel.poll() {
            let stripe = id / 2;
            if id % 2 == 0 {
                self.slot_written(stripe, ok);
            } else {
                self.slot_read(stripe, ok);
            }
        }
    }

    fn slot_written(&mut self, stripe: usize, ok: bool) {
        let Some(fetch) = self.fetches.remove(&stripe) else {
            return;
        };
        let slot = fetch.slot.expect("a fetch writing has a slot");
        if let Some(buffer) = &fetch.buffer {
            self.buffers.return_buffer(buffer);
        }
        if ok && self.metadata.publish_resident(stripe, fetch.attempt, slot) {
            self.slots[slot as usize] = Slot::Held(stripe);
            return;
        }
        if !ok {
            error!("Failed to fill a slot for stripe {stripe}");
            self.metadata.fail_attempt(stripe, fetch.attempt);
        }
        self.release_slot(slot);
    }

    fn poll_store(&mut self) {
        for (name, result) in self.store.poll_gets() {
            let stripe = self
                .fetches
                .iter()
                .find_map(|(stripe, fetch)| match &fetch.state {
                    FetchState::Fetching { name: waiting, .. } if *waiting == name => Some(*stripe),
                    _ => None,
                });
            if let Some(stripe) = stripe {
                self.fetched(stripe, result);
            }
        }
        for (name, result) in self.store.poll_puts() {
            let stripe = self
                .evictions
                .iter()
                .find_map(|(stripe, evict)| match &evict.state {
                    EvictState::Uploading { name: waiting, .. } if *waiting == name => {
                        Some(*stripe)
                    }
                    _ => None,
                });
            if let Some(stripe) = stripe {
                self.uploaded(stripe, result);
            }
        }
    }

    fn fetched(&mut self, stripe: usize, result: crate::Result<Vec<u8>>) {
        let fetch = self.fetches.get(&stripe).expect("fetch");
        let FetchState::Fetching { name, digest, .. } = &fetch.state else {
            return;
        };
        let stripe_bytes = self.stripe_sectors as usize * SECTOR_SIZE;
        match result {
            Ok(data) if data.len() == stripe_bytes && sha256_bytes(&data) == *digest => {
                let buffer = fetch.buffer.clone().expect("a fetch fetching has a buffer");
                buffer.borrow_mut().as_mut_slice()[..stripe_bytes].copy_from_slice(&data);
                self.write_slot(stripe);
            }
            Ok(data) => {
                error!(
                    "Object {name} for stripe {stripe} is not what was uploaded ({} bytes)",
                    data.len()
                );
                self.fail_fetch(stripe);
            }
            Err(e) => {
                error!("Failed to fetch stripe {stripe}: {e}");
                self.fail_fetch(stripe);
            }
        }
    }

    /// Give up on a fetch with no local I/O outstanding.
    fn fail_fetch(&mut self, stripe: usize) {
        let Some(fetch) = self.fetches.remove(&stripe) else {
            return;
        };
        if let Some(buffer) = &fetch.buffer {
            self.buffers.return_buffer(buffer);
        }
        if let Some(slot) = fetch.slot {
            self.release_slot(slot);
        }
        self.metadata.fail_attempt(stripe, fetch.attempt);
    }

    /// Find room for fetches that have no slot: reclaim slots of failed
    /// stripes, and evict the least recently accessed idle stripe.
    fn make_room(&mut self) {
        let waiting = self
            .fetch_queue
            .iter()
            .filter(|stripe| self.fetches[*stripe].slot.is_none())
            .count();
        let mut needed = waiting.saturating_sub(self.evictions.len());
        if needed == 0 || self.slots.is_empty() {
            return;
        }

        let mut candidates = Vec::new();
        for _ in 0..VICTIM_BATCH.min(self.slots.len()) {
            let slot = self.cursor;
            self.cursor = (self.cursor + 1) % self.slots.len();
            let Slot::Held(stripe) = self.slots[slot] else {
                continue;
            };
            if self.metadata.reclaim_failed(stripe).is_some() {
                self.release_slot(slot as SlotId);
                needed -= 1;
                if needed == 0 {
                    return;
                }
                continue;
            }
            candidates.push((self.metadata.last_accessed(stripe), slot as SlotId, stripe));
        }

        candidates.sort_unstable();
        for (_, slot, stripe) in candidates {
            if needed == 0 {
                return;
            }
            let Some((reserved, dirty)) = self.metadata.reserve_victim(stripe) else {
                continue;
            };
            debug_assert_eq!(reserved, slot);
            if !dirty {
                self.metadata.finish_eviction(stripe);
                self.release_slot(slot);
                needed -= 1;
                continue;
            }
            let Some(buffer) = self.buffers.get_buffer() else {
                self.metadata.abort_eviction(stripe);
                return;
            };
            self.slots[slot as usize] = Slot::Draining(stripe);
            self.channel.add_read(
                self.slot_sector(slot),
                self.stripe_sectors as u32,
                buffer.clone(),
                stripe * 2 + 1,
            );
            if let Err(e) = self.channel.submit() {
                error!("Failed to submit the eviction read of stripe {stripe}: {e}");
            }
            self.evictions.insert(
                stripe,
                Evict {
                    slot,
                    buffer,
                    state: EvictState::ReadingSlot,
                },
            );
            needed -= 1;
        }
    }

    fn slot_read(&mut self, stripe: usize, ok: bool) {
        if !ok {
            error!("Failed to read stripe {stripe} out of its slot");
            self.fail_eviction(stripe);
            return;
        }
        let Some(evict) = self.evictions.get_mut(&stripe) else {
            return;
        };
        let data = evict.buffer.borrow().as_slice().to_vec();
        let digest = sha256_bytes(&data);
        let name = format!("{}/stripe-{stripe}/{}", self.run_id, self.next_object);
        self.next_object += 1;
        self.store.start_put_object(&name, data);
        evict.state = EvictState::Uploading {
            name,
            digest,
            since: Instant::now(),
        };
    }

    fn uploaded(&mut self, stripe: usize, result: crate::Result<()>) {
        if let Err(e) = result {
            error!("Failed to upload stripe {stripe}: {e}");
            self.fail_eviction(stripe);
            return;
        }
        let evict = self.evictions.remove(&stripe).expect("eviction");
        let EvictState::Uploading { name, digest, .. } = evict.state else {
            return;
        };
        self.buffers.return_buffer(&evict.buffer);
        // The new source first, so the slot is only reused once the stripe can
        // be brought back from somewhere else.
        self.objects.insert(stripe, Object { name, digest });
        self.metadata.finish_eviction(stripe);
        self.release_slot(evict.slot);
        self.eviction_failures = 0;
    }

    /// Give up on an eviction with no local I/O outstanding. The stripe keeps
    /// its slot; if the store keeps failing, fetches waiting for room fail
    /// rather than wait for an eviction that is not going to succeed.
    fn fail_eviction(&mut self, stripe: usize) {
        let Some(evict) = self.evictions.remove(&stripe) else {
            return;
        };
        self.buffers.return_buffer(&evict.buffer);
        self.slots[evict.slot as usize] = Slot::Held(stripe);
        self.metadata.abort_eviction(stripe);

        self.eviction_failures += 1;
        if self.eviction_failures < MAX_EVICTION_FAILURES {
            return;
        }
        self.eviction_failures = 0;
        let waiting: Vec<usize> = self
            .fetch_queue
            .iter()
            .copied()
            .filter(|stripe| self.fetches[stripe].slot.is_none())
            .collect();
        self.fetch_queue.retain(|stripe| !waiting.contains(stripe));
        for stripe in waiting {
            let fetch = self.fetches.remove(&stripe).expect("fetch");
            warn!("No room for stripe {stripe}: evictions keep failing");
            self.metadata.fail_attempt(stripe, fetch.attempt);
        }
    }

    fn check_deadlines(&mut self) {
        let now = Instant::now();
        let late_fetches: Vec<usize> = self
            .fetches
            .iter()
            .filter_map(|(stripe, fetch)| match fetch.state {
                FetchState::Fetching { since, .. } if now - since > self.deadline => Some(*stripe),
                _ => None,
            })
            .collect();
        for stripe in late_fetches {
            error!("Fetching stripe {stripe} took too long");
            self.fail_fetch(stripe);
        }

        let late_uploads: Vec<usize> = self
            .evictions
            .iter()
            .filter_map(|(stripe, evict)| match evict.state {
                EvictState::Uploading { since, .. } if now - since > self.deadline => Some(*stripe),
                _ => None,
            })
            .collect();
        for stripe in late_uploads {
            error!("Uploading stripe {stripe} took too long");
            self.fail_eviction(stripe);
        }
    }

    #[cfg(test)]
    pub fn set_deadline(&mut self, deadline: Duration) {
        self.deadline = deadline;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::archive::MemStore;
    use crate::block_device::bdev_spill::metadata::{Decision, StripeState};
    use crate::block_device::bdev_test::TestBlockDevice;
    use crate::block_device::BlockDevice;
    use std::cell::Cell;
    use std::rc::Rc;

    const STRIPE_SECTORS: u64 = 8;
    const STRIPE_BYTES: usize = STRIPE_SECTORS as usize * SECTOR_SIZE;

    /// A store that can be told to fail uploads or to never answer fetches.
    struct TestStore {
        inner: MemStore,
        fail_puts: Rc<Cell<bool>>,
        hang_gets: Rc<Cell<bool>>,
    }

    impl ArchiveStore for TestStore {
        fn start_put_object(&mut self, name: &str, data: Vec<u8>) {
            self.inner.start_put_object(name, data);
        }

        fn start_get_object(&mut self, name: &str) {
            if !self.hang_gets.get() {
                self.inner.start_get_object(name);
            }
        }

        fn poll_puts(&mut self) -> Vec<(String, crate::Result<()>)> {
            let fail = self.fail_puts.get();
            self.inner
                .poll_puts()
                .into_iter()
                .map(|(name, result)| {
                    if fail {
                        self.inner.objects.borrow_mut().remove(&name);
                        let error = crate::ubiblk_error!(ArchiveError {
                            description: "the store is down".to_string(),
                        });
                        (name, Err(error))
                    } else {
                        (name, result)
                    }
                })
                .collect()
        }

        fn poll_gets(&mut self) -> Vec<(String, crate::Result<Vec<u8>>)> {
            self.inner.poll_gets()
        }
    }

    struct Harness {
        metadata: SpillSharedMetadata,
        task: SpillTask,
        disk: TestBlockDevice,
        objects: Rc<std::cell::RefCell<HashMap<String, Vec<u8>>>>,
        fail_puts: Rc<Cell<bool>>,
        hang_gets: Rc<Cell<bool>>,
    }

    fn harness(stripes: usize, slots: u32) -> Harness {
        let metadata = SpillSharedMetadata::new(stripes);
        let disk = TestBlockDevice::new(slots as u64 * STRIPE_BYTES as u64);
        let inner = MemStore::new();
        let objects = inner.objects.clone();
        let fail_puts = Rc::new(Cell::new(false));
        let hang_gets = Rc::new(Cell::new(false));
        let store = TestStore {
            inner,
            fail_puts: fail_puts.clone(),
            hang_gets: hang_gets.clone(),
        };
        let task = SpillTask::new(
            metadata.clone(),
            Box::new(store),
            disk.create_channel().unwrap(),
            STRIPE_SECTORS,
            slots,
            4,
            1,
        );
        Harness {
            metadata,
            task,
            disk,
            objects,
            fail_puts,
            hang_gets,
        }
    }

    impl Harness {
        fn run(&mut self, passes: usize) {
            for _ in 0..passes {
                self.task.update();
            }
        }

        /// Admit a request for `stripe`, doing what a channel does, and run the
        /// worker until the request can go ahead or has failed.
        fn admit(&mut self, stripe: usize) -> Decision {
            let mut joined = None;
            let mut decision = self.metadata.admit(stripe, &mut joined);
            for _ in 0..100 {
                match decision {
                    Decision::Wait { fetch } => {
                        if let Some(attempt) = fetch {
                            self.task.handle_fetch_request(stripe, attempt);
                        }
                        self.task.update();
                        decision = self.metadata.retry(stripe, &mut joined);
                    }
                    _ => return decision,
                }
            }
            decision
        }

        fn read(&mut self, stripe: usize) -> Option<Vec<u8>> {
            let Decision::Ready { slot } = self.admit(stripe) else {
                return None;
            };
            let mut data = vec![0u8; STRIPE_BYTES];
            self.disk
                .read(slot as usize * STRIPE_BYTES, &mut data, STRIPE_BYTES);
            self.metadata.finish(stripe, false, true);
            Some(data)
        }

        fn write(&mut self, stripe: usize, byte: u8) {
            let Decision::Ready { slot } = self.admit(stripe) else {
                panic!("stripe {stripe} could not be written");
            };
            self.disk.write(
                slot as usize * STRIPE_BYTES,
                &vec![byte; STRIPE_BYTES],
                STRIPE_BYTES,
            );
            self.metadata.finish(stripe, true, true);
        }

        fn state(&self, stripe: usize) -> StripeState {
            self.metadata.get(stripe).state
        }
    }

    #[test]
    fn a_never_written_stripe_comes_in_as_zeroes() {
        let mut h = harness(4, 2);
        h.disk
            .write(0, &vec![0xFF; 2 * STRIPE_BYTES], 2 * STRIPE_BYTES);

        let data = h.read(3).expect("read");

        assert!(data.iter().all(|b| *b == 0));
        assert!(matches!(h.state(3), StripeState::Resident { .. }));
    }

    #[test]
    fn a_clean_stripe_is_evicted_without_an_upload() {
        let mut h = harness(4, 2);
        h.read(0);
        h.read(1);

        h.read(2).expect("read");

        assert!(h.objects.borrow().is_empty(), "a clean stripe was uploaded");
        assert_eq!(h.state(0), StripeState::Absent);
    }

    #[test]
    fn a_written_stripe_is_uploaded_and_comes_back() {
        let mut h = harness(4, 1);
        h.write(0, 0xAB);

        h.read(1).expect("read");
        assert_eq!(h.state(0), StripeState::Absent);
        assert_eq!(h.objects.borrow().len(), 1);

        let data = h.read(0).expect("read");
        assert!(data.iter().all(|b| *b == 0xAB));
        assert!(!h.metadata.get(0).dirty);
    }

    #[test]
    fn the_least_recently_accessed_stripe_goes_first() {
        let mut h = harness(4, 2);
        h.read(0);
        h.read(1);
        h.read(0);

        h.read(2);

        assert!(matches!(h.state(0), StripeState::Resident { .. }));
        assert_eq!(h.state(1), StripeState::Absent);
    }

    #[test]
    fn a_stripe_in_use_is_not_evicted() {
        let mut h = harness(4, 1);
        h.read(0);
        let mut held = None;
        assert!(matches!(
            h.metadata.admit(0, &mut held),
            Decision::Ready { .. }
        ));

        let mut joined = None;
        let Decision::Wait {
            fetch: Some(attempt),
        } = h.metadata.admit(1, &mut joined)
        else {
            panic!("no fetch");
        };
        h.task.handle_fetch_request(1, attempt);
        h.run(20);
        assert!(matches!(h.state(0), StripeState::Resident { .. }));
        assert_eq!(h.state(1), StripeState::Loading { attempt });

        h.metadata.finish(0, false, true);
        h.run(20);
        assert!(matches!(h.state(1), StripeState::Resident { .. }));
    }

    #[test]
    fn a_missing_object_fails_the_attempt_and_frees_the_slot() {
        let mut h = harness(4, 1);
        h.write(0, 0xAB);
        h.read(1);
        h.objects.borrow_mut().clear();

        assert_eq!(h.admit(0), Decision::Fail);
        assert_eq!(h.state(0), StripeState::Absent);
        assert!(h.read(1).is_some(), "the slot was not given back");
    }

    #[test]
    fn an_object_that_is_not_what_was_uploaded_is_refused() {
        let mut h = harness(4, 1);
        h.write(0, 0xAB);
        h.read(1);
        for data in h.objects.borrow_mut().values_mut() {
            data[0] ^= 1;
        }

        assert_eq!(h.admit(0), Decision::Fail);
    }

    #[test]
    fn a_fill_that_fails_fails_the_attempt_and_frees_the_slot() {
        let mut h = harness(4, 1);
        h.disk
            .fail_next
            .store(true, std::sync::atomic::Ordering::SeqCst);

        assert_eq!(h.admit(0), Decision::Fail);
        assert_eq!(h.state(0), StripeState::Absent);
        assert!(h.read(1).is_some(), "the slot was not given back");
    }

    #[test]
    fn a_store_that_keeps_failing_fails_the_fetches_waiting_for_room() {
        let mut h = harness(4, 1);
        h.write(0, 0xAB);
        h.fail_puts.set(true);

        assert_eq!(h.admit(1), Decision::Fail);

        // The stripe that could not be uploaded is still where it was.
        assert!(matches!(h.state(0), StripeState::Resident { .. }));
        assert!(h.metadata.get(0).dirty);
        assert!(h.objects.borrow().is_empty());
        let data = h.read(0).expect("read");
        assert!(data.iter().all(|b| *b == 0xAB));
    }

    #[test]
    fn a_failed_stripe_gives_its_slot_back_when_room_is_needed() {
        let mut h = harness(4, 1);
        h.read(0);
        let Decision::Ready { .. } = h.admit(0) else {
            panic!("not ready");
        };
        h.metadata.finish(0, true, false);
        assert!(matches!(h.state(0), StripeState::Failed { slot: Some(_) }));

        h.read(1).expect("read");

        assert_eq!(h.state(0), StripeState::Failed { slot: None });
        assert!(
            h.objects.borrow().is_empty(),
            "a failed stripe was uploaded"
        );
        assert_eq!(h.admit(0), Decision::Fail);
    }

    #[test]
    fn a_fetch_that_takes_too_long_fails() {
        let mut h = harness(4, 1);
        h.write(0, 0xAB);
        h.read(1);
        h.hang_gets.set(true);
        h.task.set_deadline(Duration::ZERO);

        assert_eq!(h.admit(0), Decision::Fail);
        assert!(!h.task.busy());
    }
}
