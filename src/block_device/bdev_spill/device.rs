//! The device the layer above sees, and the channel that serves it.
//!
//! A request is split into chunk-sized pieces, and each piece leases its chunk
//! before it may touch the slot. A piece that cannot lease asks the task for
//! the transition it needs and is tried again on the next poll, so a request
//! whose footprint is larger than the whole cache still makes progress.

use std::collections::{HashMap, VecDeque};
use std::sync::mpsc::Sender;
use std::sync::{Arc, Mutex};

use log::error;

use crate::backends::SECTOR_SIZE;
use crate::block_device::{BgWorkerRequest, BlockDevice, IoChannel, SharedBuffer};
use crate::utils::aligned_buffer_pool::AlignedBufferPool;
use crate::Result;

use super::state::{ChunkState, SharedState};
use super::task::{FlushReply, Geometry, SpillRequest};

/// How many chunk-sized scratch buffers a channel keeps for the pieces of
/// requests that span more than one chunk.
const SCRATCH_BUFFERS: usize = 4;

pub struct SpillBlockDevice {
    base: Box<dyn BlockDevice>,
    state: SharedState,
    geometry: Geometry,
    requests: Sender<BgWorkerRequest>,
}

impl SpillBlockDevice {
    pub fn new(
        base: Box<dyn BlockDevice>,
        state: SharedState,
        geometry: Geometry,
        requests: Sender<BgWorkerRequest>,
    ) -> Result<Box<Self>> {
        let slots_needed = geometry.slot_count as u64 * geometry.chunk_sectors;
        if base.sector_count() < slots_needed {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: format!(
                    "the disk holds {} sectors, too few for {} slots of {} sectors",
                    base.sector_count(),
                    geometry.slot_count,
                    geometry.chunk_sectors
                ),
            }));
        }
        Ok(Box::new(SpillBlockDevice {
            base,
            state,
            geometry,
            requests,
        }))
    }
}

impl BlockDevice for SpillBlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>> {
        Ok(Box::new(SpillIoChannel {
            base: self.base.create_channel()?,
            state: self.state.clone(),
            geometry: self.geometry,
            requests: self.requests.clone(),
            queue: VecDeque::new(),
            live: HashMap::new(),
            base_ops: HashMap::new(),
            finished: Vec::new(),
            inbox: Arc::new(Mutex::new(Vec::new())),
            scratch: AlignedBufferPool::new(
                crate::utils::aligned_buffer::BUFFER_ALIGNMENT,
                SCRATCH_BUFFERS,
                self.geometry.chunk_bytes(),
            ),
            next_base_id: 0,
            asked: HashMap::new(),
        }))
    }

    fn sector_count(&self) -> u64 {
        self.geometry.device_sectors
    }

    fn clone(&self) -> Box<dyn BlockDevice> {
        Box::new(SpillBlockDevice {
            base: self.base.clone(),
            state: self.state.clone(),
            geometry: self.geometry,
            requests: self.requests.clone(),
        })
    }
}

/// The questions a channel asks about a chunk, kept apart so that asking one
/// does not count as having asked another.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Ask {
    Bring,
    Wrote,
    Repair,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Read,
    Write,
    Flush,
}

struct Request {
    kind: Kind,
    buf: Option<SharedBuffer>,
    /// Where the whole request started, so a piece knows its place in the
    /// caller's buffer.
    first_sector: u64,
    sector: u64,
    remaining: u32,
    single_piece: bool,
    in_flight: bool,
    ok: bool,
}

struct BaseOp {
    request: usize,
    chunk: usize,
    scratch: Option<SharedBuffer>,
    buf_sector: u64,
    sectors: u32,
    kind: Kind,
}

pub struct SpillIoChannel {
    base: Box<dyn IoChannel>,
    state: SharedState,
    geometry: Geometry,
    requests: Sender<BgWorkerRequest>,
    queue: VecDeque<usize>,
    live: HashMap<usize, Request>,
    base_ops: HashMap<usize, BaseOp>,
    finished: Vec<(usize, bool)>,
    inbox: Arc<Mutex<Vec<(usize, bool)>>>,
    scratch: AlignedBufferPool,
    next_base_id: usize,
    /// What this channel has asked about, and how many chunks had finished
    /// moving when it asked. Without this a waiting request asks again on
    /// every poll, which is thousands of messages saying the same thing; with
    /// only the chunk, a request whose chunk arrived and left again would wait
    /// for ever, and one kind of question would silence another.
    asked: HashMap<(usize, Ask), u64>,
}

impl SpillIoChannel {
    fn add(&mut self, kind: Kind, sector: u64, sectors: u32, buf: Option<SharedBuffer>, id: usize) {
        // Before anything indexes a chunk with it.
        let end = sector.checked_add(u64::from(sectors));
        if kind != Kind::Flush && end.is_none_or(|end| end > self.geometry.device_sectors) {
            error!("Spill request {id} asks for sectors {sector}..+{sectors}, past the end");
            self.finished.push((id, false));
            return;
        }

        let single_piece = kind != Kind::Flush && {
            let chunk_sectors = self.geometry.chunk_sectors;
            let within = sector % chunk_sectors;
            within + sectors as u64 <= chunk_sectors
        };
        self.live.insert(
            id,
            Request {
                kind,
                buf,
                first_sector: sector,
                sector,
                remaining: sectors,
                single_piece,
                in_flight: false,
                ok: true,
            },
        );
        self.queue.push_back(id);
    }

    fn ask(&self, request: SpillRequest) -> bool {
        let message = match request {
            SpillRequest::Fetch { chunk } => BgWorkerRequest::SpillFetch { chunk },
            SpillRequest::MakeRoom => BgWorkerRequest::SpillMakeRoom,
            SpillRequest::Flush { reply } => BgWorkerRequest::SpillFlush { reply },
            SpillRequest::Wrote { chunk } => BgWorkerRequest::SpillWrote { chunk },
            SpillRequest::Poison { chunk } => BgWorkerRequest::SpillPoison { chunk },
            SpillRequest::Repair { chunk } => BgWorkerRequest::SpillRepair { chunk },
        };
        if let Err(e) = self.requests.send(message) {
            error!("The spill task is not listening: {e}");
            return false;
        }
        true
    }

    /// Complete a request, once. A flush that was failed by a submit error is
    /// still owed a reply by the task, and answering that reply as well would
    /// complete the same descriptor twice.
    /// Ask something about a chunk, unless this channel asked the same thing
    /// and nothing has moved since.
    fn ask_once(&mut self, chunk: usize, what: Ask, request: SpillRequest) -> bool {
        let moved = self.state.transitions();
        if self.asked.insert((chunk, what), moved) == Some(moved) {
            return true;
        }
        self.ask(request)
    }

    fn finish(&mut self, id: usize, ok: bool) {
        if self.live.remove(&id).is_some() {
            self.finished.push((id, ok));
        }
    }

    /// Work through the queue, starting whatever can start. A request that
    /// cannot lease its next chunk stays where it is and asks for what it
    /// needs, so the queue keeps its order.
    fn advance(&mut self) {
        if self.queue.is_empty() {
            return;
        }
        let ids: Vec<usize> = self.queue.iter().copied().collect();
        for id in ids {
            while let Some(request) = self.live.get(&id) {
                if request.in_flight {
                    break;
                }
                if !request.ok {
                    let ok = false;
                    self.queue.retain(|queued| *queued != id);
                    self.finish(id, ok);
                    break;
                }
                if request.kind == Kind::Flush {
                    break;
                }
                if request.remaining == 0 {
                    self.queue.retain(|queued| *queued != id);
                    self.finish(id, true);
                    break;
                }
                if !self.start_piece(id) {
                    break;
                }
            }
        }

        if let Err(e) = self.base.submit() {
            // The pieces that were just added may or may not run: a failed
            // submit says nothing about what the kernel already took. They
            // keep their leases, so the slots they hold are never handed to
            // another chunk while something might still be writing into them.
            // A leaked slot costs capacity; a reused one costs the data.
            error!("Failed to submit spill I/O: {e}");
            for id in self.queue.iter() {
                if let Some(request) = self.live.get_mut(id) {
                    request.ok = false;
                }
            }
        }
    }

    /// Try to make progress on one piece. Returns whether the caller should
    /// look at this request again straight away.
    fn start_piece(&mut self, id: usize) -> bool {
        let (kind, sector, remaining, first_sector, single_piece) = {
            let request = &self.live[&id];
            (
                request.kind,
                request.sector,
                request.remaining,
                request.first_sector,
                request.single_piece,
            )
        };

        let chunk_sectors = self.geometry.chunk_sectors;
        let chunk = (sector / chunk_sectors) as usize;
        let within = sector % chunk_sectors;
        let sectors = (chunk_sectors - within).min(remaining as u64) as u32;

        // Nothing has ever been written here: a read is zeroes, and needs no
        // slot, no fetch and no lease.
        if kind == Kind::Read && self.state.is_empty(chunk) {
            if let Some(buf) = self.live[&id].buf.clone() {
                let at = (sector - first_sector) as usize * SECTOR_SIZE;
                buf.borrow_mut().as_mut_slice()[at..at + sectors as usize * SECTOR_SIZE].fill(0);
            }
            let request = self.live.get_mut(&id).expect("live");
            request.sector += sectors as u64;
            request.remaining -= sectors;
            return true;
        }

        let Some(slot) = self.state.try_lease(chunk) else {
            let seen = self.state.get(chunk);
            if seen.state == ChunkState::Poisoned {
                // A write that covers every sector the guest can address in
                // this chunk makes what was uncertain about it irrelevant.
                let live = self.geometry.live_sectors(chunk);
                if kind == Kind::Write && within == 0 && u64::from(sectors) == live {
                    self.ask_once(chunk, Ask::Repair, SpillRequest::Repair { chunk });
                    return false;
                }
                self.live.get_mut(&id).expect("live").ok = false;
                return true;
            }
            // Nothing is coming for a chunk whose last fetch failed.
            if seen.fetch_failed {
                let request = self.live.get_mut(&id).expect("live");
                request.ok = false;
                return true;
            }
            if !self.ask_once(chunk, Ask::Bring, SpillRequest::Fetch { chunk })
                || !self.ask(SpillRequest::MakeRoom)
            {
                self.live.get_mut(&id).expect("live").ok = false;
                return true;
            }
            return false;
        };

        let at = self.geometry.slot_sector(slot) + within;
        let buf_sector = sector - first_sector;
        let guest = self.live[&id].buf.clone();

        let (buffer, scratch) = if single_piece {
            (guest.expect("a read or write has a buffer"), None)
        } else {
            let Some(scratch) = self.scratch.get_buffer() else {
                self.state.release(chunk, false);
                return false;
            };
            if kind == Kind::Write {
                let guest = guest.expect("a write has a buffer");
                let from = buf_sector as usize * SECTOR_SIZE;
                let len = sectors as usize * SECTOR_SIZE;
                scratch.borrow_mut().as_mut_slice()[..len]
                    .copy_from_slice(&guest.borrow().as_slice()[from..from + len]);
            }
            (scratch.clone(), Some(scratch))
        };

        let base_id = self.next_base_id;
        self.next_base_id += 1;
        self.base_ops.insert(
            base_id,
            BaseOp {
                request: id,
                chunk,
                scratch,
                buf_sector,
                sectors,
                kind,
            },
        );
        match kind {
            Kind::Read => self.base.add_read(at, sectors, buffer, base_id),
            Kind::Write => self.base.add_write(at, sectors, buffer, base_id),
            Kind::Flush => unreachable!("a flush has no pieces"),
        }
        self.live.get_mut(&id).expect("live").in_flight = true;
        false
    }

    fn base_completed(&mut self, base_id: usize, ok: bool) {
        let Some(op) = self.base_ops.remove(&base_id) else {
            error!("Spill channel saw a completion for {base_id}, which it never sent");
            return;
        };

        if ok && op.kind == Kind::Read {
            if let (Some(scratch), Some(guest)) = (
                op.scratch.as_ref(),
                self.live.get(&op.request).and_then(|r| r.buf.clone()),
            ) {
                let at = op.buf_sector as usize * SECTOR_SIZE;
                let len = op.sectors as usize * SECTOR_SIZE;
                guest.borrow_mut().as_mut_slice()[at..at + len]
                    .copy_from_slice(&scratch.borrow().as_slice()[..len]);
            }
        }
        if let Some(scratch) = op.scratch {
            self.scratch.return_buffer(&scratch);
        }

        self.state.release(op.chunk, ok && op.kind == Kind::Write);
        if op.kind == Kind::Write {
            if ok {
                // Once per chunk, not once per write: what the task does with
                // this is record where the chunk is, and it is in the same
                // slot until something moves it - which is what resets this.
                self.ask_once(
                    op.chunk,
                    Ask::Wrote,
                    SpillRequest::Wrote { chunk: op.chunk },
                );
            } else {
                // The slot's contents are now uncertain: nothing may read it,
                // and nothing may upload it as though it were the chunk.
                self.state.poison(op.chunk);
                self.ask(SpillRequest::Poison { chunk: op.chunk });
            }
        }

        if let Some(request) = self.live.get_mut(&op.request) {
            request.in_flight = false;
            if ok {
                request.sector += op.sectors as u64;
                request.remaining -= op.sectors;
            } else {
                request.ok = false;
            }
        }
    }

    fn take_flush_replies(&mut self) {
        let replies = std::mem::take(&mut *self.inbox.lock().expect("flush inbox"));
        for (id, ok) in replies {
            self.queue.retain(|queued| *queued != id);
            self.finish(id, ok);
        }
    }
}

impl IoChannel for SpillIoChannel {
    fn add_read(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        self.add(Kind::Read, sector_offset, sector_count, Some(buf), id);
    }

    fn add_write(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        self.add(Kind::Write, sector_offset, sector_count, Some(buf), id);
    }

    fn add_flush(&mut self, id: usize) {
        self.add(Kind::Flush, 0, 0, None, id);
        // Nothing else will ever answer it, so a flush the task cannot be told
        // about fails now rather than waiting for a reply that is not coming.
        if !self.ask(SpillRequest::Flush {
            reply: FlushReply::new(self.inbox.clone(), id),
        }) {
            self.queue.retain(|queued| *queued != id);
            self.finish(id, false);
        }
    }

    fn submit(&mut self) -> Result<()> {
        self.advance();
        Ok(())
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        let completions = self.base.poll();
        for (base_id, ok) in completions {
            self.base_completed(base_id, ok);
        }
        self.take_flush_replies();
        self.advance();
        std::mem::take(&mut self.finished)
    }

    fn busy(&self) -> bool {
        !self.live.is_empty() || !self.finished.is_empty() || self.base.busy()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::archive::MemStore;
    use crate::block_device::bdev_spill::map::fake::FakeStorage;
    use crate::block_device::bdev_spill::map::format::Binding;
    use crate::block_device::bdev_spill::map::storage::MapStorage;
    use crate::block_device::bdev_spill::map::{sectors_needed, Map};
    use crate::block_device::bdev_spill::task::SpillTask;
    use crate::block_device::bdev_test::TestBlockDevice;
    use crate::block_device::shared_buffer;
    use std::sync::mpsc::{channel, Receiver};

    const CHUNK_SECTORS: u64 = 4;
    const SLOTS: u32 = 2;
    const CHUNKS: u64 = 8;
    const JOURNAL_BLOCKS: u64 = 8;

    fn geometry() -> Geometry {
        Geometry {
            chunk_sectors: CHUNK_SECTORS,
            device_sectors: CHUNKS * CHUNK_SECTORS,
            slot_count: SLOTS,
        }
    }

    fn binding() -> Binding {
        Binding {
            device_uuid: [2u8; 16],
            chunk_size: (CHUNK_SECTORS * SECTOR_SIZE as u64) as u32,
            logical_sector_count: CHUNKS * CHUNK_SECTORS,
            slot_count: SLOTS,
            store_digest: [3u8; 32],
        }
    }

    struct Stack {
        channel: Box<dyn IoChannel>,
        device: Box<dyn BlockDevice>,
        state: SharedState,
        task: SpillTask,
        inbox: Receiver<BgWorkerRequest>,
        base: Box<TestBlockDevice>,
        next_id: usize,
        messages: usize,
    }

    fn stack() -> Stack {
        let map = Map::create(
            Box::new(FakeStorage::new(sectors_needed(CHUNKS, JOURNAL_BLOCKS)))
                as Box<dyn MapStorage>,
            binding(),
            CHUNKS,
            JOURNAL_BLOCKS,
        )
        .expect("map");
        let state = SharedState::new(CHUNKS as usize);
        let base = Box::new(TestBlockDevice::new(
            SLOTS as u64 * CHUNK_SECTORS * SECTOR_SIZE as u64,
        ));
        let (sender, inbox) = channel();
        let task = SpillTask::new(
            state.clone(),
            map,
            Box::new(MemStore::new()),
            base.create_channel().expect("channel"),
            geometry(),
            "spill/dev".to_string(),
            7,
            4,
        )
        .expect("task");
        let device =
            SpillBlockDevice::new(base.clone(), state.clone(), geometry(), sender).expect("device");
        Stack {
            channel: device.create_channel().expect("channel"),
            device,
            state,
            task,
            inbox,
            base,
            next_id: 0,
            messages: 0,
        }
    }

    impl Stack {
        fn state_of(&self, chunk: usize) -> ChunkState {
            self.state.get(chunk).state
        }

        fn id(&mut self) -> usize {
            self.next_id += 1;
            self.next_id
        }

        /// Drive both sides until the channel has nothing left, as a frontend
        /// and the worker thread would between them.
        fn run(&mut self) -> Vec<(usize, bool)> {
            self.run_with(&mut [])
        }

        /// The same, with other channels of the same device in play.
        fn run_with(&mut self, others: &mut [Box<dyn IoChannel>]) -> Vec<(usize, bool)> {
            let mut done = Vec::new();
            self.channel.submit().expect("submit");
            for other in others.iter_mut() {
                other.submit().expect("submit");
            }
            for _ in 0..2000 {
                while let Ok(request) = self.inbox.try_recv() {
                    self.messages += 1;
                    match request {
                        BgWorkerRequest::SpillFetch { chunk } => {
                            self.task.handle(SpillRequest::Fetch { chunk })
                        }
                        BgWorkerRequest::SpillMakeRoom => self.task.handle(SpillRequest::MakeRoom),
                        BgWorkerRequest::SpillFlush { reply } => {
                            self.task.handle(SpillRequest::Flush { reply })
                        }
                        BgWorkerRequest::SpillWrote { chunk } => {
                            self.task.handle(SpillRequest::Wrote { chunk })
                        }
                        BgWorkerRequest::SpillPoison { chunk } => {
                            self.task.handle(SpillRequest::Poison { chunk })
                        }
                        BgWorkerRequest::SpillRepair { chunk } => {
                            self.task.handle(SpillRequest::Repair { chunk })
                        }
                        _ => {}
                    }
                }
                self.task.update();
                done.extend(self.channel.poll());
                for other in others.iter_mut() {
                    done.extend(other.poll());
                }
                if !self.channel.busy() && !others.iter().any(|other| other.busy()) {
                    return done;
                }
            }
            panic!("the stack never settled");
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
            buf.borrow_mut().as_mut_slice().fill(0x5A);
            let id = self.id();
            self.channel.add_read(sector, sectors, buf.clone(), id);
            if self.run() == vec![(id, true)] {
                let read = buf.borrow().as_slice().to_vec();
                Some(read)
            } else {
                None
            }
        }

        fn flush(&mut self) -> bool {
            let id = self.id();
            self.channel.add_flush(id);
            self.run() == vec![(id, true)]
        }
    }

    #[test]
    fn a_device_nothing_wrote_reads_as_zeroes_without_taking_a_slot() {
        let mut stack = stack();

        let read = stack.read(0, CHUNK_SECTORS as u32 * 3).expect("read");

        assert!(read.iter().all(|b| *b == 0));
        assert_eq!(stack.task.free_slots(), SLOTS as usize, "a slot was taken");
    }

    #[test]
    fn what_was_written_reads_back() {
        let mut stack = stack();
        assert!(stack.write(1, 2, 0xA1));

        let read = stack.read(0, 4).expect("read");

        assert!(read[..SECTOR_SIZE].iter().all(|b| *b == 0));
        assert!(read[SECTOR_SIZE..3 * SECTOR_SIZE]
            .iter()
            .all(|b| *b == 0xA1));
        assert!(read[3 * SECTOR_SIZE..].iter().all(|b| *b == 0));
    }

    #[test]
    fn a_request_that_crosses_chunks_is_written_and_read_in_pieces() {
        let mut stack = stack();
        let sectors = CHUNK_SECTORS as u32 * 2;

        assert!(stack.write(CHUNK_SECTORS - 1, sectors, 0xB2));
        let read = stack.read(CHUNK_SECTORS - 1, sectors).expect("read");

        assert!(
            read.iter().all(|b| *b == 0xB2),
            "the pieces did not line up"
        );
    }

    /// The cache is two slots and this request touches four chunks. Leasing
    /// all of them at once could never succeed, so the pieces have to be able
    /// to go one at a time.
    #[test]
    fn a_request_larger_than_the_whole_cache_still_finishes() {
        let mut stack = stack();
        let sectors = CHUNK_SECTORS as u32 * 4;

        assert!(stack.write(0, sectors, 0xC3), "the write never completed");
        let read = stack.read(0, sectors).expect("read");

        assert!(read.iter().all(|b| *b == 0xC3));
    }

    #[test]
    fn a_chunk_that_was_pushed_out_comes_back_with_its_contents() {
        let mut stack = stack();
        assert!(stack.write(0, 2, 0xD4));

        // Two more chunks, so the first has to give up its slot.
        assert!(stack.write(CHUNK_SECTORS, 1, 0xE5));
        assert!(stack.write(CHUNK_SECTORS * 2, 1, 0xF6));

        let read = stack.read(0, 2).expect("read");

        assert!(
            read.iter().all(|b| *b == 0xD4),
            "what came back is not what was written before the chunk was evicted"
        );
    }

    /// Two channels wanting the same chunk at the same time. One fetch brings
    /// it in and both get the data; neither installs a second copy.
    #[test]
    fn two_channels_missing_the_same_chunk_both_get_it() {
        let mut stack = stack();
        assert!(stack.write(0, 1, 0x77));
        // Push it out to the store.
        assert!(stack.write(CHUNK_SECTORS, 1, 0x01));
        assert!(stack.write(CHUNK_SECTORS * 2, 1, 0x02));

        let mut second = stack.device.create_channel().expect("a second channel");
        let first_buf = shared_buffer(SECTOR_SIZE);
        let second_buf = shared_buffer(SECTOR_SIZE);
        let (a, b) = (stack.id(), stack.id());
        stack.channel.add_read(0, 1, first_buf.clone(), a);
        second.add_read(0, 1, second_buf.clone(), b);

        let mut done = stack.run_with(std::slice::from_mut(&mut second));
        done.sort();

        assert_eq!(done, vec![(a, true), (b, true)]);
        assert!(first_buf.borrow().as_slice().iter().all(|x| *x == 0x77));
        assert!(second_buf.borrow().as_slice().iter().all(|x| *x == 0x77));
    }

    /// Two channels writing different parts of one chunk. Both land: neither
    /// reads the slot, changes its copy and writes the whole thing back.
    #[test]
    fn two_channels_writing_one_chunk_do_not_lose_each_other() {
        let mut stack = stack();
        assert!(stack.write(0, 1, 0x10));

        let mut second = stack.device.create_channel().expect("a second channel");
        let first_buf = shared_buffer(SECTOR_SIZE);
        first_buf.borrow_mut().as_mut_slice().fill(0xAA);
        let second_buf = shared_buffer(SECTOR_SIZE);
        second_buf.borrow_mut().as_mut_slice().fill(0xBB);
        let (a, b) = (stack.id(), stack.id());
        stack.channel.add_write(1, 1, first_buf, a);
        second.add_write(2, 1, second_buf, b);

        let mut done = stack.run_with(std::slice::from_mut(&mut second));
        done.sort();
        assert_eq!(done, vec![(a, true), (b, true)]);

        let read = stack.read(0, 3).expect("read");
        assert!(read[..SECTOR_SIZE].iter().all(|x| *x == 0x10));
        assert!(read[SECTOR_SIZE..2 * SECTOR_SIZE]
            .iter()
            .all(|x| *x == 0xAA));
        assert!(read[2 * SECTOR_SIZE..].iter().all(|x| *x == 0xBB));
    }

    /// Writing the same chunk over and over tells the task once, not once per
    /// write: what it does with that is record where the chunk is, and it does
    /// not move in between.
    #[test]
    fn a_run_of_writes_to_one_chunk_is_one_message() {
        let mut stack = stack();
        assert!(stack.write(0, 1, 0x01));

        let before = stack.messages;
        for byte in 2..12u8 {
            assert!(stack.write(0, 1, byte));
        }

        let sent = stack.messages - before;
        assert!(
            sent <= 2,
            "ten writes to one chunk sent {sent} messages to the task"
        );
    }

    #[test]
    fn a_flush_is_answered() {
        let mut stack = stack();
        assert!(stack.write(0, 1, 0x11));

        assert!(stack.flush());
    }

    /// A write that fails leaves a slot nobody can trust, so reads of that
    /// chunk fail rather than handing back whatever is in it.
    #[test]
    fn a_chunk_whose_write_failed_is_not_served() {
        let mut stack = stack();
        assert!(stack.write(0, 1, 0x22));

        stack
            .base
            .fail_next
            .store(true, std::sync::atomic::Ordering::SeqCst);
        assert!(
            !stack.write(0, 1, 0x33),
            "a failed write was reported as done"
        );

        assert_eq!(stack.read(0, 1), None, "a poisoned chunk was read");
        assert_eq!(
            stack.task.map().authority(0),
            crate::block_device::bdev_spill::map::format::Authority::Unreadable
        );
    }

    /// A chunk that cannot be brought in fails the request waiting for it,
    /// rather than leaving it to wait for an attempt nobody is going to make
    /// again.
    /// A chunk that arrives and is taken away again before the request
    /// waiting for it gets a turn. The request has to ask a second time, or it
    /// waits for a fetch nobody is going to make.
    #[test]
    fn a_request_asks_again_when_its_chunk_comes_and_goes() {
        let mut stack = stack();
        assert!(stack.write(0, 1, 0x44));
        assert!(stack.write(CHUNK_SECTORS, 1, 0x55));
        assert!(stack.write(CHUNK_SECTORS * 2, 1, 0x66));

        // Chunk 0 is in the store now. Ask for it, let the task bring it in,
        // then take it away again before the channel can lease it.
        let buf = shared_buffer(SECTOR_SIZE);
        let id = stack.id();
        stack.channel.add_read(0, 1, buf.clone(), id);
        stack.channel.submit().expect("submit");
        for _ in 0..200 {
            while let Ok(request) = stack.inbox.try_recv() {
                match request {
                    BgWorkerRequest::SpillFetch { chunk } => {
                        stack.task.handle(SpillRequest::Fetch { chunk })
                    }
                    BgWorkerRequest::SpillMakeRoom => stack.task.handle(SpillRequest::MakeRoom),
                    _ => {}
                }
            }
            stack.task.update();
            if stack.state_of(0) == ChunkState::Resident {
                break;
            }
        }
        assert_eq!(stack.state_of(0), ChunkState::Resident, "never came in");
        let (slot, _) = stack.state.begin_evict(0).expect("take it away again");
        stack.state.finish_evict(0).expect("and free the slot");
        stack.task.release_slot(slot);

        assert_eq!(stack.run(), vec![(id, true)], "the request was stranded");
        assert!(buf.borrow().as_slice().iter().all(|b| *b == 0x44));
    }

    #[test]
    fn a_read_whose_chunk_cannot_be_fetched_fails() {
        let mut stack = stack();
        assert!(stack.write(0, 1, 0x99));
        // Push it to the store, then take the object away.
        assert!(stack.write(CHUNK_SECTORS, 1, 0x01));
        assert!(stack.write(CHUNK_SECTORS * 2, 1, 0x02));
        stack.task.forget_objects();

        assert_eq!(stack.read(0, 1), None, "a chunk with no object was served");

        // Other chunks are unaffected.
        assert!(stack.read(CHUNK_SECTORS, 1).is_some());
    }

    /// A chunk taken out of service by a failed write comes back when the
    /// guest overwrites all of it - and not before. The map goes on saying it
    /// is unreadable until that overwrite has been flushed, so a crash in
    /// between leaves reads failing rather than serving zeroes.
    #[test]
    fn a_chunk_is_repaired_by_overwriting_the_whole_of_it() {
        let mut stack = stack();
        assert!(stack.write(0, 1, 0x22));
        stack
            .base
            .fail_next
            .store(true, std::sync::atomic::Ordering::SeqCst);
        assert!(!stack.write(0, 1, 0x33));
        assert_eq!(stack.read(0, 1), None, "a poisoned chunk was read");

        // Part of it is not enough.
        assert!(!stack.write(0, 1, 0x44), "a partial write repaired a chunk");
        assert_eq!(
            stack.task.map().authority(0),
            crate::block_device::bdev_spill::map::format::Authority::Unreadable
        );

        // All of it is.
        assert!(
            stack.write(0, CHUNK_SECTORS as u32, 0x55),
            "a whole-chunk write did not repair it"
        );
        let read = stack.read(0, CHUNK_SECTORS as u32).expect("read");
        assert!(read.iter().all(|b| *b == 0x55));

        assert!(stack.flush());
        assert!(
            matches!(
                stack.task.map().authority(0),
                crate::block_device::bdev_spill::map::format::Authority::Local { .. }
            ),
            "the repair was not recorded"
        );
    }

    #[test]
    fn reads_and_writes_past_the_end_of_the_device_are_refused() {
        let mut stack = stack();
        let end = CHUNKS * CHUNK_SECTORS;

        for (sector, sectors) in [(end, 1), (end - 1, 2), (u64::MAX, 1)] {
            let id = stack.id();
            let buf = shared_buffer(sectors as usize * SECTOR_SIZE);
            stack.channel.add_read(sector, sectors, buf, id);
            assert_eq!(stack.run(), vec![(id, false)], "read {sector}..+{sectors}");

            let id = stack.id();
            let buf = shared_buffer(sectors as usize * SECTOR_SIZE);
            stack.channel.add_write(sector, sectors, buf, id);
            assert_eq!(stack.run(), vec![(id, false)], "write {sector}..+{sectors}");
        }
    }

    #[test]
    fn a_request_for_nothing_is_answered_rather_than_queued() {
        let mut stack = stack();
        let id = stack.id();
        let buf = shared_buffer(SECTOR_SIZE);
        stack.channel.add_read(0, 0, buf, id);

        assert_eq!(stack.run(), vec![(id, true)]);
    }
}
