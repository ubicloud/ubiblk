//! What is happening to each chunk right now.
//!
//! One `AtomicU64` per chunk holds everything a channel needs on its I/O path:
//! the chunk's state, whether its copy differs from the authority the map
//! names, how many requests are holding it, and which slot it is in. Taking a
//! lease is one compare-and-swap, and so is giving one back while saying the
//! chunk was modified - those have to be the same step, or an evictor that
//! sees the last lease go can drop a slot whose contents nobody has recorded.
//!
//! Everything else - the free list, the waiters, the replacement clock - is the
//! worker's, and is not here.

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

pub const MAX_LEASES: u32 = (1 << 11) - 1;
pub const MAX_SLOTS: u32 = (1 << 24) - 1;

const STATE_BITS: u64 = 0xF;
const MODIFIED_BIT: u64 = 1 << 4;
const LEASE_SHIFT: u32 = 5;
const LEASE_MASK: u64 = 0x7FF << LEASE_SHIFT;
const SLOT_SHIFT: u32 = 16;
const SLOT_MASK: u64 = 0xFF_FFFF << SLOT_SHIFT;
/// Set once a chunk has content anywhere. A read of a chunk without it is
/// served as zeroes and needs no slot; the bit is cleared before anything can
/// write to the chunk, so an acknowledged write can never be read as nothing.
const HAS_CONTENT_BIT: u64 = 1 << 40;
/// Set when the last attempt to bring a chunk in failed. A request waiting for
/// that chunk fails rather than waiting for an attempt nobody is going to make
/// again; the next one to ask for it clears the bit and tries afresh.
const FETCH_FAILED_BIT: u64 = 1 << 41;

/// The states a chunk moves through. Only `Resident` can be leased, so a chunk
/// in the middle of anything is untouchable rather than merely undocumented.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChunkState {
    /// No slot: served from the store, or from zeroes, or not at all.
    Idle = 0,
    /// A slot is being filled for it.
    Filling = 1,
    /// In its slot, and readable.
    Resident = 2,
    /// Being moved out of its slot.
    Evicting = 3,
    /// A failed write left the contents uncertain.
    Poisoned = 4,
}

impl ChunkState {
    fn from_bits(bits: u64) -> ChunkState {
        match bits {
            0 => ChunkState::Idle,
            1 => ChunkState::Filling,
            2 => ChunkState::Resident,
            3 => ChunkState::Evicting,
            _ => ChunkState::Poisoned,
        }
    }
}

/// A chunk's word, unpacked.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Chunk {
    pub state: ChunkState,
    pub modified: bool,
    pub has_content: bool,
    pub fetch_failed: bool,
    pub leases: u32,
    pub slot: u32,
}

impl Chunk {
    fn decode(word: u64) -> Chunk {
        Chunk {
            state: ChunkState::from_bits(word & STATE_BITS),
            modified: word & MODIFIED_BIT != 0,
            has_content: word & HAS_CONTENT_BIT != 0,
            fetch_failed: word & FETCH_FAILED_BIT != 0,
            leases: ((word & LEASE_MASK) >> LEASE_SHIFT) as u32,
            slot: ((word & SLOT_MASK) >> SLOT_SHIFT) as u32,
        }
    }

    fn encode(&self) -> u64 {
        (self.state as u64)
            | if self.modified { MODIFIED_BIT } else { 0 }
            | if self.has_content { HAS_CONTENT_BIT } else { 0 }
            | if self.fetch_failed {
                FETCH_FAILED_BIT
            } else {
                0
            }
            | ((self.leases as u64) << LEASE_SHIFT)
            | ((self.slot as u64) << SLOT_SHIFT)
    }
}

#[derive(Clone)]
pub struct SharedState {
    chunks: Arc<Vec<AtomicU64>>,
    /// Bumped whenever a chunk finishes moving. A channel waiting for one can
    /// tell "nothing has happened since I asked" from "something did, and what
    /// I asked for may need asking again".
    transitions: Arc<AtomicU64>,
}

impl SharedState {
    pub fn new(chunk_count: usize) -> Self {
        SharedState {
            chunks: Arc::new((0..chunk_count).map(|_| AtomicU64::new(0)).collect()),
            transitions: Arc::new(AtomicU64::new(0)),
        }
    }

    pub fn chunk_count(&self) -> usize {
        self.chunks.len()
    }

    /// How many chunks have finished moving, ever.
    pub fn transitions(&self) -> u64 {
        self.transitions.load(Ordering::Acquire)
    }

    fn moved(&self) {
        self.transitions.fetch_add(1, Ordering::AcqRel);
    }

    pub fn get(&self, chunk: usize) -> Chunk {
        Chunk::decode(self.chunks[chunk].load(Ordering::Acquire))
    }

    fn update<T>(
        &self,
        chunk: usize,
        mut change: impl FnMut(Chunk) -> Option<(Chunk, T)>,
    ) -> Option<T> {
        let word = &self.chunks[chunk];
        let mut current = word.load(Ordering::Acquire);
        loop {
            let (next, out) = change(Chunk::decode(current))?;
            match word.compare_exchange_weak(
                current,
                next.encode(),
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => return Some(out),
                Err(seen) => current = seen,
            }
        }
    }

    /// Hold a resident chunk in its slot. Nothing else may move it until every
    /// lease is given back.
    pub fn try_lease(&self, chunk: usize) -> Option<u32> {
        self.update(chunk, |mut c| {
            if c.state != ChunkState::Resident || c.leases >= MAX_LEASES {
                return None;
            }
            c.leases += 1;
            Some((c, c.slot))
        })
    }

    /// Give a lease back, saying in the same step whether this request left the
    /// slot different from what the map names.
    pub fn release(&self, chunk: usize, modified: bool) {
        self.update(chunk, |mut c| {
            debug_assert!(c.leases > 0, "released a lease that was not held");
            c.leases = c.leases.saturating_sub(1);
            c.modified |= modified;
            Some((c, ()))
        });
    }

    pub fn begin_fill(&self, chunk: usize, slot: u32) -> bool {
        assert!(slot <= MAX_SLOTS);
        self.update(chunk, |mut c| {
            if c.state != ChunkState::Idle {
                return None;
            }
            c.state = ChunkState::Filling;
            c.slot = slot;
            c.modified = false;
            c.fetch_failed = false;
            // Before anything can be written into the slot, so a read that saw
            // no content did so before this chunk had any.
            c.has_content = true;
            Some((c, ()))
        })
        .is_some()
    }

    /// Nothing could bring this chunk in. Whoever is waiting for it should
    /// stop rather than wait for an attempt that is not coming.
    pub fn mark_fetch_failed(&self, chunk: usize) {
        self.update(chunk, |mut c| {
            c.fetch_failed = true;
            Some((c, ()))
        });
        self.moved();
    }

    /// Say a chunk has content, as the map does for one it already knows about.
    pub fn mark_content(&self, chunk: usize) {
        self.update(chunk, |mut c| {
            c.has_content = true;
            Some((c, ()))
        });
    }

    /// Whether a read has to go and get anything at all.
    pub fn is_empty(&self, chunk: usize) -> bool {
        let seen = self.get(chunk);
        !seen.has_content && seen.state == ChunkState::Idle
    }

    /// The slot holds the chunk now. `modified` says the contents differ from
    /// what the map names, which is true of a chunk written into a fresh slot.
    pub fn finish_fill(&self, chunk: usize, modified: bool) -> bool {
        self.update(chunk, |mut c| {
            if c.state != ChunkState::Filling {
                return None;
            }
            c.state = ChunkState::Resident;
            c.modified = modified;
            Some((c, ()))
        })
        .inspect(|()| self.moved())
        .is_some()
    }

    /// The fill failed: the chunk goes back to having no slot.
    pub fn abandon_fill(&self, chunk: usize) -> Option<u32> {
        self.update(chunk, |mut c| {
            if c.state != ChunkState::Filling {
                return None;
            }
            let slot = c.slot;
            c.state = ChunkState::Idle;
            c.slot = 0;
            Some((c, slot))
        })
        .inspect(|_| self.moved())
    }

    /// Take a chunk out of service so its slot can be reused. This is the CAS
    /// that has to exclude new leases in the same step as it checks there are
    /// none.
    pub fn begin_evict(&self, chunk: usize) -> Option<(u32, bool)> {
        self.update(chunk, |mut c| {
            if c.state != ChunkState::Resident || c.leases != 0 {
                return None;
            }
            c.state = ChunkState::Evicting;
            Some((c, (c.slot, c.modified)))
        })
    }

    /// The eviction is done and the slot is free.
    pub fn finish_evict(&self, chunk: usize) -> Option<u32> {
        self.update(chunk, |mut c| {
            if c.state != ChunkState::Evicting {
                return None;
            }
            let slot = c.slot;
            c.state = ChunkState::Idle;
            c.slot = 0;
            c.modified = false;
            Some((c, slot))
        })
        .inspect(|_| self.moved())
    }

    /// The eviction failed; the chunk keeps its slot and whatever it held.
    pub fn keep(&self, chunk: usize) -> bool {
        self.update(chunk, |mut c| {
            if c.state != ChunkState::Evicting {
                return None;
            }
            c.state = ChunkState::Resident;
            Some((c, ()))
        })
        .inspect(|()| self.moved())
        .is_some()
    }

    /// A failed write: nothing may read this chunk, and nothing may upload it.
    pub fn poison(&self, chunk: usize) {
        self.update(chunk, |mut c| {
            c.state = ChunkState::Poisoned;
            c.modified = false;
            Some((c, ()))
        });
        self.moved();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::AtomicUsize;
    use std::thread;

    fn resident(state: &SharedState, chunk: usize, slot: u32) {
        assert!(state.begin_fill(chunk, slot));
        assert!(state.finish_fill(chunk, false));
    }

    #[test]
    fn a_word_holds_everything_a_channel_needs() {
        let chunk = Chunk {
            state: ChunkState::Evicting,
            modified: true,
            has_content: true,
            fetch_failed: true,
            leases: MAX_LEASES,
            slot: MAX_SLOTS,
        };
        assert_eq!(Chunk::decode(chunk.encode()), chunk);
    }

    /// A chunk nothing has ever written is read as zeroes without a slot; one
    /// that is being filled is not, however briefly.
    #[test]
    fn an_empty_chunk_stops_being_empty_before_anything_can_write_to_it() {
        let state = SharedState::new(2);
        assert!(state.is_empty(0));

        assert!(state.begin_fill(0, 1));
        assert!(
            !state.is_empty(0),
            "a chunk being filled still read as empty"
        );

        assert!(state.finish_fill(0, true));
        assert!(!state.is_empty(0));
    }

    #[test]
    fn a_fill_clears_the_mark_a_failed_one_left() {
        let state = SharedState::new(2);
        state.mark_fetch_failed(0);
        assert!(state.get(0).fetch_failed);

        assert!(state.begin_fill(0, 1));

        assert!(
            !state.get(0).fetch_failed,
            "a fresh attempt kept the old mark"
        );
    }

    #[test]
    fn a_chunk_the_map_knows_about_is_not_empty() {
        let state = SharedState::new(2);
        state.mark_content(1);
        assert!(!state.is_empty(1));
        assert!(state.is_empty(0));
    }

    #[test]
    fn only_a_resident_chunk_can_be_leased() {
        let state = SharedState::new(4);
        assert_eq!(state.try_lease(0), None);

        assert!(state.begin_fill(0, 7));
        assert_eq!(state.try_lease(0), None, "a chunk being filled was leased");

        assert!(state.finish_fill(0, false));
        assert_eq!(state.try_lease(0), Some(7));
    }

    #[test]
    fn a_leased_chunk_cannot_be_evicted() {
        let state = SharedState::new(4);
        resident(&state, 0, 3);
        state.try_lease(0).expect("lease");

        assert_eq!(state.begin_evict(0), None);

        state.release(0, false);
        assert_eq!(state.begin_evict(0), Some((3, false)));
    }

    #[test]
    fn releasing_says_the_chunk_changed_in_the_same_step() {
        let state = SharedState::new(4);
        resident(&state, 0, 3);
        state.try_lease(0).expect("lease");

        state.release(0, true);

        assert_eq!(state.begin_evict(0), Some((3, true)));
    }

    #[test]
    fn an_evicting_chunk_is_not_leasable_and_can_be_kept() {
        let state = SharedState::new(4);
        resident(&state, 0, 3);
        state.begin_evict(0).expect("evict");

        assert_eq!(state.try_lease(0), None);
        assert!(state.keep(0));
        assert_eq!(state.try_lease(0), Some(3));
    }

    #[test]
    fn a_finished_eviction_gives_the_slot_back() {
        let state = SharedState::new(4);
        resident(&state, 0, 3);
        state.begin_evict(0).expect("evict");

        assert_eq!(state.finish_evict(0), Some(3));
        assert_eq!(state.get(0).state, ChunkState::Idle);
        assert_eq!(state.try_lease(0), None);
    }

    #[test]
    fn a_failed_fill_gives_the_slot_back() {
        let state = SharedState::new(4);
        assert!(state.begin_fill(0, 5));

        assert_eq!(state.abandon_fill(0), Some(5));
        assert_eq!(state.get(0).state, ChunkState::Idle);
    }

    #[test]
    fn a_poisoned_chunk_is_refused_to_everyone() {
        let state = SharedState::new(4);
        resident(&state, 0, 3);
        state.poison(0);

        assert_eq!(state.try_lease(0), None);
        assert_eq!(state.begin_evict(0), None);
        assert!(!state.finish_fill(0, false));
    }

    #[test]
    fn a_chunk_can_be_leased_many_times_at_once() {
        let state = SharedState::new(4);
        resident(&state, 0, 1);
        for _ in 0..8 {
            assert_eq!(state.try_lease(0), Some(1));
        }
        assert_eq!(state.get(0).leases, 8);
        assert_eq!(state.begin_evict(0), None);
    }

    #[test]
    fn leases_stop_rather_than_wrap() {
        let state = SharedState::new(2);
        resident(&state, 0, 1);
        for _ in 0..MAX_LEASES {
            assert!(state.try_lease(0).is_some());
        }
        assert_eq!(state.try_lease(0), None, "the lease count wrapped");
        assert_eq!(state.get(0).leases, MAX_LEASES);
    }

    /// The race the design exists for: readers and writers coming and going
    /// while an evictor tries to take the slot. Either it gets a chunk with no
    /// leases, or it does not get it at all, and a chunk that was written must
    /// never be evicted as unmodified.
    #[test]
    fn an_evictor_never_takes_a_chunk_from_under_a_request() {
        let state = SharedState::new(1);
        resident(&state, 0, 1);
        let evicted_dirty = Arc::new(AtomicUsize::new(0));
        let evicted_clean = Arc::new(AtomicUsize::new(0));

        let mut threads = Vec::new();
        for writer in 0..4 {
            let state = state.clone();
            threads.push(thread::spawn(move || {
                for _ in 0..2000 {
                    if state.try_lease(0).is_some() {
                        let seen = state.get(0);
                        assert_eq!(seen.state, ChunkState::Resident);
                        assert!(seen.leases > 0);
                        state.release(0, writer % 2 == 0);
                    }
                }
            }));
        }

        let dirty = evicted_dirty.clone();
        let clean = evicted_clean.clone();
        let evictor = state.clone();
        threads.push(thread::spawn(move || {
            for _ in 0..2000 {
                if let Some((slot, modified)) = evictor.begin_evict(0) {
                    assert_eq!(slot, 1);
                    assert_eq!(evictor.get(0).leases, 0, "evicted a leased chunk");
                    if modified {
                        dirty.fetch_add(1, Ordering::Relaxed);
                    } else {
                        clean.fetch_add(1, Ordering::Relaxed);
                    }
                    // Put it back, as a failed upload would.
                    assert!(evictor.keep(0));
                }
            }
        }));

        for thread in threads {
            thread.join().unwrap();
        }
        assert!(
            evicted_dirty.load(Ordering::Relaxed) + evicted_clean.load(Ordering::Relaxed) > 0,
            "the evictor never got the chunk, so this proved nothing"
        );
    }

    /// Two workers racing to fill the same chunk: one wins, and the loser is
    /// told so rather than installing a second slot for it.
    #[test]
    fn only_one_fill_can_win() {
        let state = SharedState::new(1);
        let winners = Arc::new(AtomicUsize::new(0));

        let threads: Vec<_> = (0..4)
            .map(|slot| {
                let state = state.clone();
                let winners = winners.clone();
                thread::spawn(move || {
                    if state.begin_fill(0, slot) {
                        winners.fetch_add(1, Ordering::Relaxed);
                    }
                })
            })
            .collect();
        for thread in threads {
            thread.join().unwrap();
        }

        assert_eq!(winners.load(Ordering::Relaxed), 1);
    }
}
