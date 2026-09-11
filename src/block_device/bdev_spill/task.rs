//! The spill layer's background work: fetching chunks in, moving them out, and
//! keeping the map honest.
//!
//! Channels never talk to the object store and never move data between tiers.
//! They ask, and retry. Every transition happens here, which is what makes two
//! channels missing the same chunk produce one fetch and two waiters.

use std::collections::{HashMap, HashSet};

use log::error;
use sha2::{Digest, Sha256};

use crate::archive::ArchiveStore;
use crate::backends::SECTOR_SIZE;
use crate::block_device::{IoChannel, SharedBuffer};
use crate::utils::aligned_buffer_pool::AlignedBufferPool;
use crate::Result;

use super::map::format::Authority;
use super::map::storage::MapStorage;
use super::map::Map;
use super::slots::SlotPool;
use super::state::{ChunkState, SharedState};

/// How long shutting down waits for what is in flight, before leaving it to
/// recovery.
const FINISH_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(30);

/// How many slots to try in one pass when looking for room. The hand keeps its
/// place, so the next pass carries on where this one stopped.
const VICTIMS_PER_UPDATE: u32 = 16;

/// What a channel asks the task for. Nothing here carries data: the task reads
/// the state and the map to work out what is needed.
pub enum SpillRequest {
    /// This chunk is needed in a slot.
    Fetch { chunk: usize },
    /// A slot is needed and none is free.
    MakeRoom,
    /// Everything completed before now must be recoverable.
    Flush { reply: FlushReply },
    /// A write landed in this chunk's slot, so the slot now holds more than
    /// the map says.
    Wrote { chunk: usize },
    /// A write into this chunk's slot failed and its contents are uncertain.
    Poison { chunk: usize },
}

/// Where a flush's answer goes. The channel that asked drains it in `poll`.
#[derive(Clone)]
pub struct FlushReply {
    inbox: std::sync::Arc<std::sync::Mutex<Vec<(usize, bool)>>>,
    id: usize,
}

impl FlushReply {
    pub fn new(inbox: std::sync::Arc<std::sync::Mutex<Vec<(usize, bool)>>>, id: usize) -> Self {
        FlushReply { inbox, id }
    }

    fn answer(&self, ok: bool) {
        self.inbox.lock().expect("flush inbox").push((self.id, ok));
    }
}

#[derive(Clone, Copy)]
pub struct Geometry {
    pub chunk_sectors: u64,
    pub device_sectors: u64,
    pub slot_count: u32,
}

impl Geometry {
    pub fn chunk_bytes(&self) -> usize {
        self.chunk_sectors as usize * SECTOR_SIZE
    }

    pub fn chunk_count(&self) -> u64 {
        self.device_sectors.div_ceil(self.chunk_sectors)
    }

    pub fn slot_sector(&self, slot: u32) -> u64 {
        slot as u64 * self.chunk_sectors
    }
}

enum Fill {
    Fetching {
        slot: u32,
        name: String,
        buffer: SharedBuffer,
    },
    Writing {
        slot: u32,
        buffer: SharedBuffer,
    },
}

enum Evict {
    Reading {
        slot: u32,
        buffer: SharedBuffer,
    },
    Uploading {
        slot: u32,
        name: String,
        generation: u64,
        digest: u64,
    },
}

enum Io {
    Fill(usize),
    Evict(usize),
    Flush,
}

struct PendingFlush {
    replies: Vec<FlushReply>,
    /// Chunk and the slot it was in when the flush was admitted. A chunk that
    /// has moved since is not published from here: whatever moved it made it
    /// recoverable its own way.
    chunks: Vec<(usize, u32)>,
}

pub struct SpillTask {
    state: SharedState,
    slots: SlotPool,
    map: Map<Box<dyn MapStorage>>,
    store: Box<dyn ArchiveStore>,
    base: Box<dyn IoChannel>,
    geometry: Geometry,
    prefix: String,
    open_id: u64,
    next_generation: u64,
    buffers: AlignedBufferPool,
    fills: HashMap<usize, Fill>,
    evicts: HashMap<usize, Evict>,
    io: HashMap<usize, Io>,
    next_io: usize,
    /// Chunks whose slot holds more than the map's authority does.
    dirty: HashSet<usize>,
    waiting_flushes: Vec<FlushReply>,
    running_flush: Option<PendingFlush>,
    wanted: HashSet<usize>,
}

impl SpillTask {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        state: SharedState,
        map: Map<Box<dyn MapStorage>>,
        store: Box<dyn ArchiveStore>,
        base: Box<dyn IoChannel>,
        geometry: Geometry,
        prefix: String,
        open_id: u64,
        concurrency: usize,
    ) -> Result<Self> {
        let mut slots = SlotPool::new(geometry.slot_count);
        let mut next_generation = 1;

        // What the map already knows: which chunks own a slot, which have
        // content somewhere, and how far the generations have gone.
        for chunk in 0..map.chunk_count() as usize {
            match map.authority(chunk as u64) {
                Authority::Zero => {}
                Authority::Local { slot } => {
                    slots.claim(slot, chunk)?;
                    state.mark_content(chunk);
                    if !state.begin_fill(chunk, slot) || !state.finish_fill(chunk, false) {
                        return Err(crate::ubiblk_error!(InvalidParameter {
                            description: format!("chunk {chunk} is in two places at once"),
                        }));
                    }
                }
                Authority::Remote {
                    open, generation, ..
                } => {
                    state.mark_content(chunk);
                    if open == open_id {
                        next_generation = next_generation.max(generation + 1);
                    }
                }
                Authority::Unreadable => {
                    state.mark_content(chunk);
                    state.poison(chunk);
                }
            }
        }

        Ok(SpillTask {
            state,
            slots,
            map,
            store,
            base,
            geometry,
            prefix,
            open_id,
            next_generation,
            buffers: AlignedBufferPool::new(
                crate::utils::aligned_buffer::BUFFER_ALIGNMENT,
                concurrency,
                geometry.chunk_bytes(),
            ),
            fills: HashMap::new(),
            evicts: HashMap::new(),
            io: HashMap::new(),
            next_io: 0,
            dirty: HashSet::new(),
            waiting_flushes: Vec::new(),
            running_flush: None,
            wanted: HashSet::new(),
        })
    }

    fn object_name(&self, chunk: usize, open: u64, generation: u64) -> String {
        format!("{}/chunk-{chunk:012}/{open}.{generation}", self.prefix)
    }

    fn digest_of(data: &[u8]) -> u64 {
        let hash = Sha256::digest(data);
        u64::from_le_bytes(hash[..8].try_into().expect("sha256 is longer than 8 bytes"))
    }

    fn next_io_id(&mut self, what: Io) -> usize {
        let id = self.next_io;
        self.next_io += 1;
        self.io.insert(id, what);
        id
    }

    pub fn handle(&mut self, request: SpillRequest) {
        match request {
            SpillRequest::Fetch { chunk } => {
                self.wanted.insert(chunk);
            }
            SpillRequest::MakeRoom => {}
            SpillRequest::Flush { reply } => self.waiting_flushes.push(reply),
            SpillRequest::Wrote { chunk } => {
                self.dirty.insert(chunk);
            }
            SpillRequest::Poison { chunk } => self.poison(chunk),
        }
    }

    /// A failed write leaves a slot nobody can trust. The chunk is out of
    /// service until it is repaired, and the record says so, so a restart does
    /// not hand the bytes back as though they were the chunk.
    fn poison(&mut self, chunk: usize) {
        self.state.poison(chunk);
        self.dirty.remove(&chunk);
        self.wanted.remove(&chunk);
        if let Err(e) = self
            .map
            .stage(chunk as u64, Authority::Unreadable)
            .and_then(|()| self.map.commit())
        {
            error!("Recording chunk {chunk} as unreadable failed: {e}");
        }
    }

    pub fn busy(&self) -> bool {
        !self.fills.is_empty()
            || !self.evicts.is_empty()
            || !self.wanted.is_empty()
            || !self.waiting_flushes.is_empty()
            || self.running_flush.is_some()
            || self.base.busy()
    }

    pub fn update(&mut self) {
        self.poll_base();
        self.poll_store();
        self.start_fills();
        self.make_room();
        self.start_flush();
    }

    /// Bring chunks that somebody is waiting for into slots.
    fn start_fills(&mut self) {
        if self.wanted.is_empty() {
            return;
        }
        let wanted: Vec<usize> = self.wanted.iter().copied().collect();
        for chunk in wanted {
            if self.fills.contains_key(&chunk) {
                continue;
            }
            let seen = self.state.get(chunk);
            if seen.state != ChunkState::Idle {
                // It is here, or it never will be, or something else is
                // already moving it. Only the first two stop us wanting it:
                // the channel that asked will not ask twice, so a fill that
                // fails has to leave the wanting behind.
                if matches!(seen.state, ChunkState::Resident | ChunkState::Poisoned) {
                    self.wanted.remove(&chunk);
                }
                continue;
            }
            if !self.buffers.has_available() {
                break;
            }
            let Some(slot) = self.slots.allocate(chunk) else {
                break;
            };
            if !self.state.begin_fill(chunk, slot) {
                self.slots.release(slot);
                self.wanted.remove(&chunk);
                continue;
            }

            match self.map.authority(chunk as u64) {
                Authority::Remote {
                    open, generation, ..
                } => {
                    // Taken now rather than when the object arrives: a fetch
                    // that finds no buffer at the end has spent a round trip
                    // for nothing.
                    let buffer = self.buffers.get_buffer().expect("checked above");
                    let name = self.object_name(chunk, open, generation);
                    self.store.start_get_object(&name);
                    self.fills
                        .insert(chunk, Fill::Fetching { slot, name, buffer });
                }
                Authority::Zero => {
                    let buffer = self.buffers.get_buffer().expect("checked above");
                    buffer.borrow_mut().as_mut_slice().fill(0);
                    let id = self.next_io_id(Io::Fill(chunk));
                    self.base.add_write(
                        self.geometry.slot_sector(slot),
                        self.geometry.chunk_sectors as u32,
                        buffer.clone(),
                        id,
                    );
                    self.fills.insert(chunk, Fill::Writing { slot, buffer });
                }
                Authority::Local { .. } | Authority::Unreadable => {
                    // Local is already resident, and an unreadable chunk is not
                    // served until it is repaired.
                    self.state.abandon_fill(chunk);
                    self.slots.release(slot);
                    self.wanted.remove(&chunk);
                }
            }
        }

        if let Err(e) = self.base.submit() {
            error!("Failed to submit spill fills: {e}");
        }
    }

    /// Free a slot if anything is waiting for one. A chunk that is already
    /// being filled has its slot, so wanting it is not a reason to take one
    /// away from somebody else.
    fn make_room(&mut self) {
        let waiting = self
            .wanted
            .iter()
            .any(|chunk| !self.fills.contains_key(chunk));
        if self.slots.free_count() > 0
            || !waiting
            || !self.evicts.is_empty()
            || !self.buffers.has_available()
        {
            return;
        }

        // Bounded, because this runs on every update: if the slots the hand
        // passes are all held, looking at the rest of them now would only burn
        // the thread that has to run the I/O releasing them.
        for _ in 0..VICTIMS_PER_UPDATE.min(self.slots.slot_count()) {
            let Some((slot, chunk)) = self.slots.next_occupied() else {
                return;
            };
            let Some((evicting_slot, modified)) = self.state.begin_evict(chunk) else {
                continue;
            };
            debug_assert_eq!(evicting_slot, slot);

            let keeps_its_contents = modified
                || matches!(self.map.authority(chunk as u64), Authority::Local { .. })
                || self.dirty.contains(&chunk);
            if !keeps_its_contents {
                self.state.finish_evict(chunk);
                self.slots.release(slot);
                return;
            }

            let buffer = self.buffers.get_buffer().expect("checked above");
            let id = self.next_io_id(Io::Evict(chunk));
            self.base.add_read(
                self.geometry.slot_sector(slot),
                self.geometry.chunk_sectors as u32,
                buffer.clone(),
                id,
            );
            self.evicts.insert(chunk, Evict::Reading { slot, buffer });
            if let Err(e) = self.base.submit() {
                error!("Failed to submit spill eviction read: {e}");
            }
            return;
        }
    }

    fn poll_base(&mut self) {
        for (id, ok) in self.base.poll() {
            match self.io.remove(&id) {
                Some(Io::Fill(chunk)) => self.fill_written(chunk, ok),
                Some(Io::Evict(chunk)) => self.evict_read(chunk, ok),
                Some(Io::Flush) => self.base_flushed(ok),
                None => error!("Spill task saw a completion for request {id}, which it never sent"),
            }
        }
    }

    fn fill_written(&mut self, chunk: usize, ok: bool) {
        let Some(fill) = self.fills.remove(&chunk) else {
            return;
        };
        let Fill::Writing { slot, buffer } = fill else {
            return;
        };
        self.buffers.return_buffer(&buffer);
        if ok {
            self.state.finish_fill(chunk, false);
            self.wanted.remove(&chunk);
        } else {
            error!("Filling chunk {chunk} failed");
            self.state.abandon_fill(chunk);
            self.state.mark_fetch_failed(chunk);
            self.wanted.remove(&chunk);
            self.slots.release(slot);
        }
    }

    fn evict_read(&mut self, chunk: usize, ok: bool) {
        let Some(evict) = self.evicts.remove(&chunk) else {
            return;
        };
        let Evict::Reading { slot, buffer } = evict else {
            return;
        };
        if !ok {
            error!("Reading chunk {chunk} out of slot {slot} failed");
            self.buffers.return_buffer(&buffer);
            self.state.keep(chunk);
            return;
        }

        let generation = self.next_generation;
        self.next_generation += 1;
        let (name, digest) = {
            let data = buffer.borrow();
            (
                self.object_name(chunk, self.open_id, generation),
                Self::digest_of(data.as_slice()),
            )
        };
        self.store
            .start_put_object(&name, buffer.borrow().as_slice().to_vec());
        self.buffers.return_buffer(&buffer);
        self.evicts.insert(
            chunk,
            Evict::Uploading {
                slot,
                name,
                generation,
                digest,
            },
        );
    }

    fn poll_store(&mut self) {
        for (name, result) in self.store.poll_gets() {
            let Some((&chunk, _)) = self
                .fills
                .iter()
                .find(|(_, fill)| matches!(fill, Fill::Fetching { name: n, .. } if *n == name))
            else {
                continue;
            };
            self.fetched(chunk, result);
        }

        for (name, result) in self.store.poll_puts() {
            let Some((&chunk, _)) = self
                .evicts
                .iter()
                .find(|(_, evict)| matches!(evict, Evict::Uploading { name: n, .. } if *n == name))
            else {
                continue;
            };
            self.uploaded(chunk, result);
        }
    }

    fn fetched(&mut self, chunk: usize, result: Result<Vec<u8>>) {
        let Some(Fill::Fetching { slot, buffer, .. }) = self.fills.remove(&chunk) else {
            return;
        };
        let give_up = |task: &mut Self, buffer: &SharedBuffer| {
            task.buffers.return_buffer(buffer);
            task.state.abandon_fill(chunk);
            task.state.mark_fetch_failed(chunk);
            task.wanted.remove(&chunk);
            task.slots.release(slot);
        };

        let expected_digest = match self.map.authority(chunk as u64) {
            Authority::Remote { digest, .. } => digest,
            _ => {
                give_up(self, &buffer);
                return;
            }
        };

        let data = match result {
            Ok(data) => data,
            Err(e) => {
                error!("Fetching chunk {chunk} failed: {e}");
                give_up(self, &buffer);
                return;
            }
        };
        if data.len() != self.geometry.chunk_bytes() || Self::digest_of(&data) != expected_digest {
            error!(
                "The object for chunk {chunk} is not what the map describes: {} bytes",
                data.len()
            );
            give_up(self, &buffer);
            return;
        }

        buffer.borrow_mut().as_mut_slice().copy_from_slice(&data);
        let id = self.next_io_id(Io::Fill(chunk));
        self.base.add_write(
            self.geometry.slot_sector(slot),
            self.geometry.chunk_sectors as u32,
            buffer.clone(),
            id,
        );
        self.fills.insert(chunk, Fill::Writing { slot, buffer });
        if let Err(e) = self.base.submit() {
            error!("Failed to submit the write bringing chunk {chunk} in: {e}");
        }
    }

    fn uploaded(&mut self, chunk: usize, result: Result<()>) {
        let Some(Evict::Uploading {
            slot,
            generation,
            digest,
            ..
        }) = self.evicts.remove(&chunk)
        else {
            return;
        };

        if let Err(e) = result {
            error!("Uploading chunk {chunk} failed: {e}");
            self.state.keep(chunk);
            return;
        }

        let authority = Authority::Remote {
            open: self.open_id,
            generation,
            digest,
        };
        if let Err(e) = self
            .map
            .stage(chunk as u64, authority)
            .and_then(|()| self.map.commit())
        {
            error!("Recording chunk {chunk} as uploaded failed: {e}");
            self.state.keep(chunk);
            return;
        }

        self.dirty.remove(&chunk);
        self.state.finish_evict(chunk);
        self.slots.release(slot);
    }

    fn start_flush(&mut self) {
        if self.running_flush.is_some() || self.waiting_flushes.is_empty() {
            return;
        }
        // Fixed here, so a write that lands after this point waits for the next
        // flush rather than being published before its bytes are durable.
        let chunks: Vec<(usize, u32)> = self
            .dirty
            .iter()
            .filter_map(|chunk| {
                let seen = self.state.get(*chunk);
                (seen.state == ChunkState::Resident).then_some((*chunk, seen.slot))
            })
            .collect();
        let replies = std::mem::take(&mut self.waiting_flushes);
        let id = self.next_io_id(Io::Flush);
        self.base.add_flush(id);
        if let Err(e) = self.base.submit() {
            error!("Failed to submit the spill flush: {e}");
        }
        self.running_flush = Some(PendingFlush { replies, chunks });
    }

    fn base_flushed(&mut self, ok: bool) {
        let Some(flush) = self.running_flush.take() else {
            return;
        };
        let mut answer = ok;

        if ok {
            for (chunk, slot) in &flush.chunks {
                let seen = self.state.get(*chunk);
                // A chunk that left its slot while the flush was in flight was
                // made recoverable by whatever moved it, and the slot it is in
                // now may hold bytes this flush did not cover.
                if seen.state != ChunkState::Resident || seen.slot != *slot {
                    continue;
                }
                if let Err(e) = self
                    .map
                    .stage(*chunk as u64, Authority::Local { slot: *slot })
                {
                    error!("Recording chunk {chunk} as local failed: {e}");
                    answer = false;
                }
            }
            if let Err(e) = self.map.commit() {
                error!("Committing the map for a flush failed: {e}");
                answer = false;
            }
        }

        if answer {
            for (chunk, slot) in &flush.chunks {
                let seen = self.state.get(*chunk);
                if seen.state == ChunkState::Resident && seen.slot == *slot {
                    self.dirty.remove(chunk);
                }
            }
        }
        for reply in flush.replies {
            reply.answer(answer);
        }
    }

    /// Stop, having written down where everything is. A crash is allowed to
    /// lose writes the guest never flushed; an orderly shutdown is not, and
    /// this is the difference between the two.
    pub fn finish(&mut self) {
        let deadline = std::time::Instant::now() + FINISH_TIMEOUT;
        while (!self.fills.is_empty() || !self.evicts.is_empty())
            && std::time::Instant::now() < deadline
        {
            self.update();
        }

        let inbox = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        self.handle(SpillRequest::Flush {
            reply: FlushReply::new(inbox.clone(), 0),
        });
        while std::time::Instant::now() < deadline {
            self.update();
            match inbox.lock().expect("flush inbox").first() {
                Some((_, true)) => return,
                Some((_, false)) => {
                    error!("The last flush before shutting down failed");
                    return;
                }
                None => {}
            }
        }
        error!("Gave up waiting for the last flush before shutting down");
    }

    #[cfg(test)]
    pub fn map(&self) -> &Map<Box<dyn MapStorage>> {
        &self.map
    }

    #[cfg(test)]
    pub fn free_slots(&self) -> usize {
        self.slots.free_count()
    }

    /// Lose everything in the store, as an operator with a delete key might.
    #[cfg(test)]
    pub fn forget_objects(&mut self) {
        self.store = Box::new(crate::archive::MemStore::new());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::archive::MemStore;
    use crate::block_device::bdev_spill::map::fake::FakeStorage;
    use crate::block_device::bdev_spill::map::{format::Binding, sectors_needed};
    use crate::block_device::bdev_test::TestBlockDevice;
    use crate::block_device::BlockDevice;
    use std::sync::{Arc, Mutex};

    const CHUNK_SECTORS: u64 = 4;
    const SLOTS: u32 = 2;
    const CHUNKS: u64 = 8;
    const JOURNAL_BLOCKS: u64 = 8;
    const PREFIX: &str = "spill/dev";

    fn geometry() -> Geometry {
        Geometry {
            chunk_sectors: CHUNK_SECTORS,
            device_sectors: CHUNKS * CHUNK_SECTORS,
            slot_count: SLOTS,
        }
    }

    fn binding() -> Binding {
        Binding {
            device_uuid: [8u8; 16],
            chunk_size: (CHUNK_SECTORS * SECTOR_SIZE as u64) as u32,
            logical_sector_count: CHUNKS * CHUNK_SECTORS,
            slot_count: SLOTS,
            store_digest: [1u8; 32],
        }
    }

    struct Harness {
        task: SpillTask,
        state: SharedState,
        base: Box<TestBlockDevice>,
        objects: std::rc::Rc<std::cell::RefCell<std::collections::HashMap<String, Vec<u8>>>>,
    }

    fn harness() -> Harness {
        let map = Map::create(
            Box::new(FakeStorage::new(sectors_needed(CHUNKS, JOURNAL_BLOCKS)))
                as Box<dyn MapStorage>,
            binding(),
            CHUNKS,
            JOURNAL_BLOCKS,
        )
        .expect("map");
        harness_with_map(map)
    }

    fn harness_with_map(map: Map<Box<dyn MapStorage>>) -> Harness {
        let state = SharedState::new(CHUNKS as usize);
        let base = Box::new(TestBlockDevice::new(
            SLOTS as u64 * CHUNK_SECTORS * SECTOR_SIZE as u64,
        ));
        let store = Box::new(MemStore::new());
        let objects = store.objects.clone();
        let task = SpillTask::new(
            state.clone(),
            map,
            store,
            base.create_channel().expect("channel"),
            geometry(),
            PREFIX.to_string(),
            42,
            4,
        )
        .expect("task");
        Harness {
            task,
            state,
            base,
            objects,
        }
    }

    fn drive(task: &mut SpillTask) {
        for _ in 0..100 {
            task.update();
            if !task.busy() {
                return;
            }
        }
        panic!("the task never settled");
    }

    fn chunk_bytes() -> usize {
        geometry().chunk_bytes()
    }

    #[test]
    fn a_chunk_nothing_wrote_is_brought_in_as_zeroes() {
        let mut h = harness();
        h.task.handle(SpillRequest::Fetch { chunk: 3 });
        drive(&mut h.task);

        let seen = h.state.get(3);
        assert_eq!(seen.state, ChunkState::Resident);
        let mem = h.base.mem.read().unwrap();
        let at = seen.slot as usize * chunk_bytes();
        assert!(mem[at..at + chunk_bytes()].iter().all(|b| *b == 0));
    }

    #[test]
    fn a_written_chunk_is_uploaded_to_free_its_slot_and_recorded() {
        let mut h = harness();
        h.task.handle(SpillRequest::Fetch { chunk: 0 });
        drive(&mut h.task);

        // The channel writes into the slot and says so.
        let slot = h.state.get(0).slot;
        h.base.write(
            slot as usize * chunk_bytes(),
            &vec![0xAB; chunk_bytes()],
            chunk_bytes(),
        );
        h.state.try_lease(0).expect("lease");
        h.state.release(0, true);
        h.task.handle(SpillRequest::Wrote { chunk: 0 });

        // Two more chunks need slots, so chunk 0 has to go.
        for chunk in [1, 2] {
            h.task.handle(SpillRequest::Fetch { chunk });
            drive(&mut h.task);
        }

        assert_eq!(h.state.get(0).state, ChunkState::Idle);
        match h.task.map().authority(0) {
            Authority::Remote {
                open, generation, ..
            } => {
                assert_eq!(open, 42);
                assert_eq!(generation, 1);
            }
            other => panic!("chunk 0 was not recorded as uploaded: {other:?}"),
        }
        let objects = h.objects.borrow();
        let name = format!("{PREFIX}/chunk-{:012}/42.1", 0);
        assert_eq!(objects.get(&name).map(|o| o.len()), Some(chunk_bytes()));
        assert!(objects[&name].iter().all(|b| *b == 0xAB));
    }

    #[test]
    fn a_chunk_that_was_never_written_is_dropped_rather_than_uploaded() {
        let mut h = harness();
        for chunk in [0, 1] {
            h.task.handle(SpillRequest::Fetch { chunk });
            drive(&mut h.task);
        }

        h.task.handle(SpillRequest::Fetch { chunk: 2 });
        drive(&mut h.task);

        assert!(h.objects.borrow().is_empty(), "a clean chunk was uploaded");
        assert_eq!(h.state.get(2).state, ChunkState::Resident);
    }

    #[test]
    fn an_uploaded_chunk_comes_back_when_it_is_asked_for() {
        let mut h = harness();
        h.task.handle(SpillRequest::Fetch { chunk: 0 });
        drive(&mut h.task);
        let slot = h.state.get(0).slot;
        h.base.write(
            slot as usize * chunk_bytes(),
            &vec![0xCD; chunk_bytes()],
            chunk_bytes(),
        );
        h.state.try_lease(0).expect("lease");
        h.state.release(0, true);
        h.task.handle(SpillRequest::Wrote { chunk: 0 });
        for chunk in [1, 2] {
            h.task.handle(SpillRequest::Fetch { chunk });
            drive(&mut h.task);
        }
        assert_eq!(h.state.get(0).state, ChunkState::Idle);

        h.task.handle(SpillRequest::Fetch { chunk: 0 });
        drive(&mut h.task);

        let seen = h.state.get(0);
        assert_eq!(seen.state, ChunkState::Resident);
        let mem = h.base.mem.read().unwrap();
        let at = seen.slot as usize * chunk_bytes();
        assert!(
            mem[at..at + chunk_bytes()].iter().all(|b| *b == 0xCD),
            "the slot does not hold what was uploaded"
        );
    }

    #[test]
    fn an_object_that_is_not_what_the_map_describes_is_refused() {
        let mut h = harness();
        h.task.handle(SpillRequest::Fetch { chunk: 0 });
        drive(&mut h.task);
        let slot = h.state.get(0).slot;
        h.base.write(
            slot as usize * chunk_bytes(),
            &vec![0xCD; chunk_bytes()],
            chunk_bytes(),
        );
        h.state.try_lease(0).expect("lease");
        h.state.release(0, true);
        h.task.handle(SpillRequest::Wrote { chunk: 0 });
        for chunk in [1, 2] {
            h.task.handle(SpillRequest::Fetch { chunk });
            drive(&mut h.task);
        }

        // Something else answers for that object.
        let name = format!("{PREFIX}/chunk-{:012}/42.1", 0);
        h.objects
            .borrow_mut()
            .insert(name, vec![0xFF; chunk_bytes()]);

        h.task.handle(SpillRequest::Fetch { chunk: 0 });
        drive(&mut h.task);

        assert_eq!(
            h.state.get(0).state,
            ChunkState::Idle,
            "a chunk was installed from an object that does not match its digest"
        );
    }

    #[test]
    fn a_flush_records_where_the_written_chunks_are() {
        let mut h = harness();
        h.task.handle(SpillRequest::Fetch { chunk: 0 });
        drive(&mut h.task);
        h.state.try_lease(0).expect("lease");
        h.state.release(0, true);
        h.task.handle(SpillRequest::Wrote { chunk: 0 });

        let inbox = Arc::new(Mutex::new(Vec::new()));
        h.task.handle(SpillRequest::Flush {
            reply: FlushReply::new(inbox.clone(), 7),
        });
        drive(&mut h.task);

        assert_eq!(*inbox.lock().unwrap(), vec![(7, true)]);
        let slot = h.state.get(0).slot;
        assert_eq!(h.task.map().authority(0), Authority::Local { slot });
    }

    /// A flush covers what had completed when it was admitted. A write that
    /// lands afterwards must not be published as local before its bytes are.
    #[test]
    fn a_flush_does_not_publish_a_write_that_arrived_after_it() {
        let mut h = harness();
        for chunk in [0, 1] {
            h.task.handle(SpillRequest::Fetch { chunk });
            drive(&mut h.task);
        }
        h.state.try_lease(0).expect("lease");
        h.state.release(0, true);
        h.task.handle(SpillRequest::Wrote { chunk: 0 });

        let inbox = Arc::new(Mutex::new(Vec::new()));
        h.task.handle(SpillRequest::Flush {
            reply: FlushReply::new(inbox.clone(), 1),
        });
        h.task.update(); // the base flush is on its way

        h.state.try_lease(1).expect("lease");
        h.state.release(1, true);
        h.task.handle(SpillRequest::Wrote { chunk: 1 });
        drive(&mut h.task);

        assert_eq!(*inbox.lock().unwrap(), vec![(1, true)]);
        assert!(matches!(h.task.map().authority(0), Authority::Local { .. }));
        assert_eq!(
            h.task.map().authority(1),
            Authority::Zero,
            "a write that arrived after the flush was admitted was published by it"
        );
    }

    /// A chunk that leaves its slot while a flush is in flight is not
    /// published by that flush: whatever moved it made it recoverable its own
    /// way, and the slot it is in now may hold bytes the flush did not cover.
    #[test]
    fn a_flush_does_not_publish_a_chunk_that_moved_under_it() {
        for refetched in [false, true] {
            let mut h = harness();
            h.task.handle(SpillRequest::Fetch { chunk: 0 });
            drive(&mut h.task);
            h.state.try_lease(0).expect("lease");
            h.state.release(0, true);
            h.task.handle(SpillRequest::Wrote { chunk: 0 });

            let inbox = Arc::new(Mutex::new(Vec::new()));
            h.task.handle(SpillRequest::Flush {
                reply: FlushReply::new(inbox.clone(), 1),
            });
            h.task.update(); // the base flush is on its way

            // The evictor takes it, and it may come back somewhere else.
            let slot = h.state.get(0).slot;
            h.state.begin_evict(0).expect("evict");
            h.state.finish_evict(0).expect("finish");
            if refetched {
                let elsewhere = (slot + 1) % SLOTS;
                assert!(h.state.begin_fill(0, elsewhere));
                assert!(h.state.finish_fill(0, false));
            }

            drive(&mut h.task);

            assert_eq!(*inbox.lock().unwrap(), vec![(1, true)]);
            assert_eq!(
                h.task.map().authority(0),
                Authority::Zero,
                "the flush published a chunk that had moved (refetched: {refetched})"
            );
        }
    }

    /// What the map says on reopening is what the task starts from: chunks in
    /// slots are resident, and their slots are not handed out again.
    #[test]
    fn a_task_starts_from_what_the_map_knows() {
        let mut h = harness();
        h.task.handle(SpillRequest::Fetch { chunk: 5 });
        drive(&mut h.task);
        h.state.try_lease(5).expect("lease");
        h.state.release(5, true);
        h.task.handle(SpillRequest::Wrote { chunk: 5 });
        let inbox = Arc::new(Mutex::new(Vec::new()));
        h.task.handle(SpillRequest::Flush {
            reply: FlushReply::new(inbox, 1),
        });
        drive(&mut h.task);
        let slot = h.state.get(5).slot;

        // Everything the map committed was flushed, so reading it back sector
        // by sector is the image a restart would find.
        let image = {
            let storage = h.task.map().storage();
            let mut image = vec![0u8; storage.sector_count() as usize * SECTOR_SIZE];
            for sector in 0..storage.sector_count() {
                let at = sector as usize * SECTOR_SIZE;
                storage
                    .read_at(sector, &mut image[at..at + SECTOR_SIZE])
                    .expect("read the map back");
            }
            image
        };
        let reopened = Map::open(
            Box::new(FakeStorage::from_image(image)) as Box<dyn MapStorage>,
            binding(),
        )
        .expect("reopen");
        let fresh = harness_with_map(reopened);

        assert_eq!(fresh.state.get(5).state, ChunkState::Resident);
        assert_eq!(fresh.state.get(5).slot, slot);
        assert_eq!(fresh.task.free_slots(), SLOTS as usize - 1);
    }
}
