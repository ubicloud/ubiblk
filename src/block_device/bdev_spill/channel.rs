use std::collections::{HashMap, VecDeque};
use std::sync::Arc;

use log::error;

use crate::{
    archive::ArchiveStore,
    backends::SECTOR_SIZE,
    block_device::{shared_buffer, IoChannel, SharedBuffer},
    Result,
};

use super::map::Victim;
use super::shared::Shared;

/// One chunk's worth of a request. A request spanning chunks is split, because
/// its chunks are in unrelated slots below.
struct Piece {
    chunk_id: usize,
    sector: u64,
    sectors: u32,
    buf_offset: usize,
}

struct Pending {
    id: usize,
    write: bool,
    buf: SharedBuffer,
    pieces: Vec<Piece>,
    next: usize,
    slot: Option<usize>,
}

/// Making a chunk resident: the object arrives, then the whole chunk is written
/// into its slot, and only then can the request that wanted it go ahead.
enum Resolve {
    Fetching {
        chunk_id: usize,
        name: String,
    },
    /// Waiting on the device below; which op it is, is in the `BaseOp`.
    Base,
    Uploading {
        chunk_id: usize,
        slot: usize,
        name: String,
    },
}

enum BaseOp {
    Piece { id: usize, bounced: bool },
    Install { chunk_id: usize, slot: usize },
    Drain { chunk_id: usize, slot: usize },
}

pub(super) struct SpillIoChannel {
    base: Box<dyn IoChannel>,
    shared: Arc<Shared>,
    store: Box<dyn ArchiveStore + Send>,
    queued: VecDeque<Pending>,
    finished: Vec<(usize, bool)>,
    base_ops: HashMap<usize, BaseOp>,
    next_base_id: usize,
    resolve: Option<Resolve>,
    /// For a request split across chunks, and for installing a fetched chunk.
    bounce: SharedBuffer,
}

impl SpillIoChannel {
    pub fn new(
        base: Box<dyn IoChannel>,
        shared: Arc<Shared>,
        store: Box<dyn ArchiveStore + Send>,
    ) -> Self {
        let bounce = shared_buffer(shared.chunk_len());
        Self {
            base,
            shared,
            store,
            queued: VecDeque::new(),
            finished: Vec::new(),
            base_ops: HashMap::new(),
            next_base_id: 0,
            resolve: None,
            bounce,
        }
    }

    fn base_id(&mut self, op: BaseOp) -> usize {
        let id = self.next_base_id;
        self.next_base_id = self.next_base_id.wrapping_add(1);
        self.base_ops.insert(id, op);
        id
    }

    fn split(&self, sector_offset: u64, sector_count: u32) -> Vec<Piece> {
        let mut pieces = Vec::new();
        let mut sector = sector_offset;
        let end = sector_offset + sector_count as u64;
        while sector < end {
            let chunk_id = (sector / self.shared.chunk_sectors) as usize;
            let chunk_end = (chunk_id as u64 + 1) * self.shared.chunk_sectors;
            let sectors = std::cmp::min(end, chunk_end) - sector;
            pieces.push(Piece {
                chunk_id,
                sector,
                sectors: sectors as u32,
                buf_offset: (sector - sector_offset) as usize * SECTOR_SIZE,
            });
            sector += sectors;
        }
        pieces
    }

    fn start(&mut self, request: Pending) {
        self.queued.push_back(request);
        if self.queued.len() == 1 {
            self.advance();
        }
    }

    /// Work on the front request's current piece, as far as it can go without
    /// waiting for the device below or the store.
    fn advance(&mut self) {
        loop {
            let Some(request) = self.queued.front() else {
                return;
            };
            if request.slot.is_some() || self.resolve.is_some() {
                return;
            }
            let piece = &request.pieces[request.next];
            let (chunk_id, write, whole_chunk) = (
                piece.chunk_id,
                request.write,
                piece.sectors as u64 == self.shared.chunk_sectors,
            );

            let mut map = self.shared.map.lock().unwrap();
            if let Some(slot) = map.slot_of(chunk_id) {
                map.pin(slot);
                drop(map);
                self.submit_piece(slot);
                return;
            }

            if !write && map.never_written(chunk_id) {
                // Nothing has ever put anything here.
                let (offset, len) = {
                    let piece = &self.queued.front().expect("front exists").pieces[request.next];
                    (piece.buf_offset, piece.sectors as usize * SECTOR_SIZE)
                };
                drop(map);
                let request = self.queued.front().expect("front exists");
                request.buf.borrow_mut().as_mut_slice()[offset..offset + len].fill(0);
                self.finish_piece(true);
                continue;
            }

            if map.free_slots() == 0 {
                drop(map);
                if self.start_reclaim() {
                    continue;
                }
                return;
            }

            // A whole-chunk write needs nothing of what was there; anything
            // else has to see it first.
            if write && whole_chunk {
                let slot = map.install(chunk_id, true).expect("a slot was free");
                map.pin(slot);
                drop(map);
                self.submit_piece(slot);
                return;
            }

            if map.in_store(chunk_id) {
                drop(map);
                let name = self.shared.object_name(chunk_id);
                self.store.start_get_object(&name);
                self.resolve = Some(Resolve::Fetching { chunk_id, name });
            } else {
                // Never written, but this is a partial write: the rest of the
                // chunk has to exist as zeroes before the write lands on it.
                let slot = map.install(chunk_id, true).expect("a slot was free");
                drop(map);
                self.bounce.borrow_mut().as_mut_slice().fill(0);
                self.install_chunk(chunk_id, slot);
            }
            return;
        }
    }

    fn submit_piece(&mut self, slot: usize) {
        let request = self.queued.front_mut().expect("front exists");
        request.slot = Some(slot);
        let piece = &request.pieces[request.next];
        let bounced = request.pieces.len() > 1;
        let sectors = piece.sectors;
        let sector = self.shared.mapped_sector(piece.sector, slot);
        let (write, offset) = (request.write, piece.buf_offset);
        let len = sectors as usize * SECTOR_SIZE;

        let buf = if bounced {
            if write {
                let src = request.buf.borrow();
                self.bounce.borrow_mut().as_mut_slice()[..len]
                    .copy_from_slice(&src.as_slice()[offset..offset + len]);
            }
            self.bounce.clone()
        } else {
            request.buf.clone()
        };

        let id = request.id;
        let base_id = self.base_id(BaseOp::Piece { id, bounced });
        if write {
            self.shared.map.lock().unwrap().mark_dirty(slot);
            self.base.add_write(sector, sectors, buf, base_id);
        } else {
            self.base.add_read(sector, sectors, buf, base_id);
        }
    }

    /// Free a slot. Returns true if one came free without any I/O; otherwise a
    /// resolve is under way, or there was nothing to take.
    fn start_reclaim(&mut self) -> bool {
        let victim = self.shared.map.lock().unwrap().claim_victim();
        match victim {
            Some(Victim::Clean { slot, chunk_id }) => {
                self.shared
                    .map
                    .lock()
                    .unwrap()
                    .release(slot, chunk_id, true);
                true
            }
            Some(Victim::Dirty { slot, chunk_id }) => {
                let base_id = self.base_id(BaseOp::Drain { chunk_id, slot });
                self.base.add_read(
                    self.shared.slot_sector(slot),
                    self.shared.chunk_sectors as u32,
                    self.bounce.clone(),
                    base_id,
                );
                self.resolve = Some(Resolve::Base);
                false
            }
            None => false,
        }
    }

    fn drive_upload(&mut self) {
        let Some(Resolve::Uploading {
            chunk_id,
            slot,
            name,
        }) = &self.resolve
        else {
            return;
        };
        let (chunk_id, slot, name) = (*chunk_id, *slot, name.clone());
        for (object, result) in self.store.poll_puts() {
            if object != name {
                continue;
            }
            self.resolve = None;
            let mut map = self.shared.map.lock().unwrap();
            match result {
                Ok(()) => map.release(slot, chunk_id, true),
                Err(e) => {
                    error!("Failed to spill chunk {chunk_id}: {e}");
                    map.restore(slot, chunk_id);
                }
            }
            return;
        }
    }

    /// Write a whole chunk from the bounce buffer into its slot.
    fn install_chunk(&mut self, chunk_id: usize, slot: usize) {
        let base_id = self.base_id(BaseOp::Install { chunk_id, slot });
        self.base.add_write(
            self.shared.slot_sector(slot),
            self.shared.chunk_sectors as u32,
            self.bounce.clone(),
            base_id,
        );
        self.resolve = Some(Resolve::Base);
    }

    fn finish_piece(&mut self, ok: bool) {
        let request = self.queued.front_mut().expect("front exists");
        if let Some(slot) = request.slot.take() {
            self.shared.map.lock().unwrap().unpin(slot);
        }
        request.next += 1;
        if !ok || request.next == request.pieces.len() {
            let request = self.queued.pop_front().expect("front exists");
            self.finished.push((request.id, ok));
        }
    }

    fn drive_fetch(&mut self) {
        let Some(Resolve::Fetching { chunk_id, name }) = &self.resolve else {
            return;
        };
        let (chunk_id, name) = (*chunk_id, name.clone());
        for (object, result) in self.store.poll_gets() {
            if object != name {
                continue;
            }
            match result {
                Ok(data) if data.len() == self.shared.chunk_len() => {
                    self.bounce.borrow_mut().as_mut_slice()[..data.len()].copy_from_slice(&data);
                    let slot = self.shared.map.lock().unwrap().install(chunk_id, false);
                    match slot {
                        Some(slot) => self.install_chunk(chunk_id, slot),
                        None => self.resolve = None,
                    }
                }
                Ok(data) => {
                    error!(
                        "Chunk {chunk_id} came back as {} bytes, expected {}",
                        data.len(),
                        self.shared.chunk_len()
                    );
                    self.resolve = None;
                    self.finish_piece(false);
                }
                Err(e) => {
                    error!("Failed to fetch chunk {chunk_id}: {e}");
                    self.resolve = None;
                    self.finish_piece(false);
                }
            }
            return;
        }
    }
}

impl IoChannel for SpillIoChannel {
    fn add_read(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        let pieces = self.split(sector_offset, sector_count);
        self.start(Pending {
            id,
            write: false,
            buf,
            pieces,
            next: 0,
            slot: None,
        });
    }

    fn add_write(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        let pieces = self.split(sector_offset, sector_count);
        self.start(Pending {
            id,
            write: true,
            buf,
            pieces,
            next: 0,
            slot: None,
        });
    }

    fn add_flush(&mut self, id: usize) {
        let base_id = self.base_id(BaseOp::Piece { id, bounced: false });
        self.base.add_flush(base_id);
    }

    fn submit(&mut self) -> Result<()> {
        self.base.submit()
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        self.drive_fetch();
        self.drive_upload();

        for (base_id, ok) in self.base.poll() {
            match self.base_ops.remove(&base_id) {
                Some(BaseOp::Piece { id, bounced }) => {
                    if self
                        .queued
                        .front()
                        .is_some_and(|request| request.id == id && !request.write)
                        && bounced
                        && ok
                    {
                        let request = self.queued.front().expect("front exists");
                        let piece = &request.pieces[request.next];
                        let (offset, len) =
                            (piece.buf_offset, piece.sectors as usize * SECTOR_SIZE);
                        let src = self.bounce.borrow();
                        request.buf.borrow_mut().as_mut_slice()[offset..offset + len]
                            .copy_from_slice(&src.as_slice()[..len]);
                    }
                    if self.queued.front().is_some_and(|r| r.id == id) {
                        self.finish_piece(ok);
                    } else {
                        // A flush, which does not belong to a queued request.
                        self.finished.push((id, ok));
                    }
                }
                Some(BaseOp::Drain { chunk_id, slot }) => {
                    if ok {
                        let data =
                            self.bounce.borrow().as_slice()[..self.shared.chunk_len()].to_vec();
                        let name = self.shared.object_name(chunk_id);
                        self.store.start_put_object(&name, data);
                        self.resolve = Some(Resolve::Uploading {
                            chunk_id,
                            slot,
                            name,
                        });
                    } else {
                        error!("Failed to read slot {slot} to spill chunk {chunk_id}");
                        self.resolve = None;
                        self.shared.map.lock().unwrap().restore(slot, chunk_id);
                    }
                }
                Some(BaseOp::Install { chunk_id, slot }) => {
                    self.resolve = None;
                    if ok {
                        self.shared.map.lock().unwrap().touch(slot);
                    } else {
                        error!("Failed to install chunk {chunk_id} in slot {slot}");
                        let mut map = self.shared.map.lock().unwrap();
                        map.release(slot, chunk_id, false);
                        drop(map);
                        self.finish_piece(false);
                    }
                }
                None => error!("The device below completed {base_id}, which is not ours"),
            }
        }

        self.advance();
        let _ = self.base.submit();
        std::mem::take(&mut self.finished)
    }

    fn busy(&self) -> bool {
        !self.finished.is_empty()
            || !self.queued.is_empty()
            || self.resolve.is_some()
            || self.base.busy()
    }
}
