use std::collections::{HashMap, HashSet};

/// Which slot of the cache below holds which chunk of the device above, plus
/// what the evictor needs to choose a slot to take back.
///
/// **In memory only.** Nothing here survives a restart, and neither does the
/// device's content: see the note on [`super::device::SpillBlockDevice`].
pub(super) struct AddressMap {
    slot_of: HashMap<usize, usize>,
    /// What each slot holds, for going the other way when a slot is taken back.
    chunk_in: Vec<Option<usize>>,
    free: Vec<usize>,
    /// The slot's content differs from what the store holds, so taking it back
    /// costs an upload.
    dirty: Vec<bool>,
    /// Requests in flight against the slot. Never taken back while non-zero.
    pins: Vec<u32>,
    /// Touched since the hand last passed: the whole replacement policy.
    referenced: Vec<bool>,
    hand: usize,
    /// Chunks the store has a copy of, current or not: `dirty` says which. A
    /// chunk in neither this nor the map has never been written and reads as
    /// zeroes.
    in_store: HashSet<usize>,
}

/// What a slot has to be given up for.
pub(super) enum Victim {
    /// Take the slot; the store already holds this chunk.
    Clean { slot: usize, chunk_id: usize },
    /// Upload this chunk before the slot can be reused.
    Dirty { slot: usize, chunk_id: usize },
}

impl AddressMap {
    pub fn new(slots: usize) -> Self {
        Self {
            slot_of: HashMap::new(),
            chunk_in: vec![None; slots],
            free: (0..slots).rev().collect(),
            dirty: vec![false; slots],
            pins: vec![0; slots],
            referenced: vec![false; slots],
            hand: 0,
            in_store: HashSet::new(),
        }
    }

    pub fn slots(&self) -> usize {
        self.chunk_in.len()
    }

    pub fn resident(&self) -> usize {
        self.slot_of.len()
    }

    pub fn free_slots(&self) -> usize {
        self.free.len()
    }

    pub fn slot_of(&self, chunk_id: usize) -> Option<usize> {
        self.slot_of.get(&chunk_id).copied()
    }

    pub fn in_store(&self, chunk_id: usize) -> bool {
        self.in_store.contains(&chunk_id)
    }

    /// A chunk nothing has ever written: reads as zeroes rather than as
    /// whatever a slot happens to hold.
    pub fn never_written(&self, chunk_id: usize) -> bool {
        !self.slot_of.contains_key(&chunk_id) && !self.in_store.contains(&chunk_id)
    }

    pub fn touch(&mut self, slot: usize) {
        self.referenced[slot] = true;
    }

    pub fn pin(&mut self, slot: usize) {
        self.pins[slot] += 1;
        self.referenced[slot] = true;
    }

    pub fn unpin(&mut self, slot: usize) {
        self.pins[slot] -= 1;
    }

    /// Give a chunk a slot, or nothing if the cache is full.
    pub fn install(&mut self, chunk_id: usize, dirty: bool) -> Option<usize> {
        let slot = self.free.pop()?;
        self.slot_of.insert(chunk_id, slot);
        self.chunk_in[slot] = Some(chunk_id);
        self.dirty[slot] = dirty;
        self.referenced[slot] = true;
        Some(slot)
    }

    /// The slot no longer matches what the store holds, so freeing it costs an
    /// upload.
    pub fn mark_dirty(&mut self, slot: usize) {
        self.dirty[slot] = true;
    }

    /// The hand sweeps, clearing reference bits, and takes the first slot
    /// untouched since it last passed.
    pub fn claim_victim(&mut self) -> Option<Victim> {
        let slots = self.chunk_in.len();
        for _ in 0..2 * slots {
            let slot = self.hand;
            self.hand = (self.hand + 1) % slots;

            let Some(chunk_id) = self.chunk_in[slot] else {
                continue;
            };
            if self.pins[slot] > 0 {
                continue;
            }
            if self.referenced[slot] {
                self.referenced[slot] = false;
                continue;
            }
            // Claimed by removing it: a request that wants this chunk now finds
            // it absent and waits for a slot, rather than reading one that is
            // being emptied.
            self.slot_of.remove(&chunk_id);
            self.chunk_in[slot] = None;
            return Some(if self.dirty[slot] {
                Victim::Dirty { slot, chunk_id }
            } else {
                Victim::Clean { slot, chunk_id }
            });
        }
        None
    }

    /// The slot is empty and can be handed out again.
    pub fn release(&mut self, slot: usize, chunk_id: usize, uploaded: bool) {
        if uploaded {
            self.in_store.insert(chunk_id);
        }
        self.dirty[slot] = false;
        self.referenced[slot] = false;
        self.free.push(slot);
    }

    /// Put a claimed slot back where it was, for an eviction that failed.
    pub fn restore(&mut self, slot: usize, chunk_id: usize) {
        self.slot_of.insert(chunk_id, slot);
        self.chunk_in[slot] = Some(chunk_id);
    }
}

#[cfg(test)]
impl AddressMap {
    /// Claim a named chunk's slot, bypassing the policy. Returns whether it has
    /// to be uploaded before the slot can be reused.
    pub fn take(&mut self, chunk_id: usize, slot: usize) -> bool {
        self.slot_of.remove(&chunk_id);
        self.chunk_in[slot] = None;
        self.dirty[slot]
    }
}
