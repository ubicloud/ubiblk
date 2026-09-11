//! The pool of chunk-sized places on the local disk.
//!
//! A slot belongs to at most one chunk, and the hand that looks for a victim
//! walks the slots rather than the address space, so finding room costs the
//! number of slots and not the size of the device.

use std::collections::VecDeque;

use crate::Result;

pub struct SlotPool {
    owner: Vec<Option<usize>>,
    free: VecDeque<u32>,
    hand: u32,
}

impl SlotPool {
    pub fn new(slot_count: u32) -> Self {
        SlotPool {
            owner: vec![None; slot_count as usize],
            free: (0..slot_count).collect(),
            hand: 0,
        }
    }

    pub fn slot_count(&self) -> u32 {
        self.owner.len() as u32
    }

    pub fn free_count(&self) -> usize {
        self.free.len()
    }

    /// Say that a slot already belongs to a chunk, as the map says after a
    /// restart. Two chunks claiming one slot is a corrupt map, not a race.
    pub fn claim(&mut self, slot: u32, chunk: usize) -> Result<()> {
        let Some(owner) = self.owner.get_mut(slot as usize) else {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: format!("the map gives chunk {chunk} slot {slot}, which is not there"),
            }));
        };
        if let Some(other) = *owner {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: format!("the map gives slot {slot} to both chunk {other} and {chunk}"),
            }));
        }
        *owner = Some(chunk);
        self.free.retain(|free| *free != slot);
        Ok(())
    }

    pub fn allocate(&mut self, chunk: usize) -> Option<u32> {
        let slot = self.free.pop_front()?;
        self.owner[slot as usize] = Some(chunk);
        Some(slot)
    }

    pub fn release(&mut self, slot: u32) {
        self.owner[slot as usize] = None;
        self.free.push_back(slot);
    }

    /// The next slot that belongs to someone, starting where the last search
    /// left off. Whether its chunk can actually be taken is for the caller to
    /// decide, since only the chunk's own word can say so.
    pub fn next_occupied(&mut self) -> Option<(u32, usize)> {
        let slots = self.slot_count();
        if slots == 0 {
            return None;
        }
        for _ in 0..slots {
            let slot = self.hand;
            self.hand = (self.hand + 1) % slots;
            if let Some(chunk) = self.owner[slot as usize] {
                return Some((slot, chunk));
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn slots_are_handed_out_and_given_back() {
        let mut pool = SlotPool::new(2);
        let first = pool.allocate(10).expect("a free slot");
        let second = pool.allocate(11).expect("a free slot");

        assert_ne!(first, second);
        assert_eq!(pool.allocate(12), None);
        assert_eq!(pool.free_count(), 0);

        pool.release(first);
        assert_eq!(pool.allocate(13), Some(first));
    }

    #[test]
    fn the_hand_visits_every_occupied_slot() {
        let mut pool = SlotPool::new(4);
        pool.allocate(100);
        pool.allocate(101);

        let mut seen = vec![pool.next_occupied(), pool.next_occupied()];
        seen.sort();
        assert_eq!(seen, vec![Some((0, 100)), Some((1, 101))]);
        assert_eq!(
            pool.next_occupied(),
            Some((0, 100)),
            "the hand did not wrap"
        );
    }

    #[test]
    fn a_pool_with_nothing_in_it_has_no_victim() {
        let mut pool = SlotPool::new(4);
        assert_eq!(pool.next_occupied(), None);
    }

    #[test]
    fn a_map_that_gives_one_slot_to_two_chunks_is_refused() {
        let mut pool = SlotPool::new(2);
        pool.claim(1, 5).expect("first claim");

        assert!(pool.claim(1, 6).is_err());
        assert!(pool.claim(2, 7).is_err(), "a slot past the end was claimed");
    }

    #[test]
    fn a_claimed_slot_is_not_handed_out_again() {
        let mut pool = SlotPool::new(2);
        pool.claim(0, 5).expect("claim");

        assert_eq!(pool.allocate(6), Some(1));
        assert_eq!(pool.allocate(7), None);
        assert_eq!(pool.next_occupied(), Some((0, 5)));
    }
}
