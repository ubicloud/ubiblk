//! The map's journal: authority changes, appended a sector at a time.
//!
//! A commit is a block written and flushed. Blocks carry consecutive sequence
//! numbers, so replay stops at the first one that does not decode or does not
//! continue the run — a torn tail, or a block left over from before the last
//! checkpoint. Nothing already acknowledged is ever rewritten: an append goes
//! to the next block, never back into one that holds a committed record.

use crate::backends::SECTOR_SIZE;
use crate::Result;

use super::format::{JournalBlock, JournalEntry, JOURNAL_ENTRIES_PER_BLOCK};
use super::storage::MapStorage;

pub struct Journal {
    first_sector: u64,
    capacity: u64,
    next_block: u64,
    next_sequence: u64,
}

impl Journal {
    /// An empty journal that will write its first block with `sequence`.
    pub fn empty(first_sector: u64, capacity: u64, sequence: u64) -> Self {
        Journal {
            first_sector,
            capacity,
            next_block: 0,
            next_sequence: sequence,
        }
    }

    /// Read back everything committed since the checkpoint that expects
    /// `sequence` next, and leave the journal ready to append after it.
    pub fn replay(
        storage: &dyn MapStorage,
        first_sector: u64,
        capacity: u64,
        sequence: u64,
    ) -> Result<(Journal, Vec<JournalEntry>)> {
        let mut journal = Journal::empty(first_sector, capacity, sequence);
        let mut entries = Vec::new();
        let mut sector = [0u8; SECTOR_SIZE];

        while journal.next_block < capacity {
            storage.read_at(first_sector + journal.next_block, &mut sector)?;
            let Ok(block) = JournalBlock::decode(&sector) else {
                break;
            };
            if block.sequence != journal.next_sequence {
                break;
            }
            entries.extend(block.entries);
            journal.next_block += 1;
            journal.next_sequence += 1;
        }

        Ok((journal, entries))
    }

    pub fn has_room(&self) -> bool {
        self.next_block < self.capacity
    }

    pub fn next_sequence(&self) -> u64 {
        self.next_sequence
    }

    pub fn blocks_used(&self) -> u64 {
        self.next_block
    }

    /// Append one block and make it durable. Returning `Ok` is what makes the
    /// entries committed; on any error nothing is advanced, so the same block
    /// index and sequence are used again rather than leaving a gap.
    pub fn append(
        &mut self,
        storage: &mut dyn MapStorage,
        entries: Vec<JournalEntry>,
    ) -> Result<()> {
        assert!(entries.len() <= JOURNAL_ENTRIES_PER_BLOCK);
        if !self.has_room() {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: "the map's journal is full".to_string(),
            }));
        }

        let block = JournalBlock {
            sequence: self.next_sequence,
            entries,
        };
        let mut sector = [0u8; SECTOR_SIZE];
        block.encode(&mut sector);

        storage.write_at(self.first_sector + self.next_block, &sector)?;
        storage.flush()?;

        self.next_block += 1;
        self.next_sequence += 1;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::super::fake::FakeStorage;
    use super::super::format::Authority;
    use super::*;

    const FIRST: u64 = 2;
    const CAPACITY: u64 = 4;

    fn entry(chunk: u64, slot: u32) -> JournalEntry {
        JournalEntry {
            chunk,
            authority: Authority::Local { slot },
        }
    }

    fn storage() -> FakeStorage {
        FakeStorage::new(FIRST + CAPACITY)
    }

    #[test]
    fn what_was_committed_comes_back_in_order() -> Result<()> {
        let mut storage = storage();
        let mut journal = Journal::empty(FIRST, CAPACITY, 1);
        journal.append(&mut storage, vec![entry(0, 10), entry(1, 11)])?;
        journal.append(&mut storage, vec![entry(2, 12)])?;

        let (journal, entries) = Journal::replay(&storage, FIRST, CAPACITY, 1)?;

        assert_eq!(entries, vec![entry(0, 10), entry(1, 11), entry(2, 12)]);
        assert_eq!(journal.next_sequence(), 3);
        assert_eq!(journal.blocks_used(), 2);
        Ok(())
    }

    #[test]
    fn a_torn_block_ends_the_replay_without_taking_what_came_before() -> Result<()> {
        let mut storage = storage();
        let mut journal = Journal::empty(FIRST, CAPACITY, 1);
        journal.append(&mut storage, vec![entry(0, 10)])?;

        // The next block reaches the disk as the first 96 bytes of itself,
        // losing five of its six entries. A tear that loses only the zeroes a
        // sparse block is padded with leaves exactly the block that was being
        // written, which is why this one is full.
        let mut sector = [0u8; SECTOR_SIZE];
        JournalBlock {
            sequence: 2,
            entries: (1..=JOURNAL_ENTRIES_PER_BLOCK as u64)
                .map(|chunk| entry(chunk, chunk as u32 + 10))
                .collect(),
        }
        .encode(&mut sector);
        storage.write_at(FIRST + 1, &sector)?;
        let crashed = FakeStorage::from_image(storage.image_after_crash(&[0], Some(96)));

        let (journal, entries) = Journal::replay(&crashed, FIRST, CAPACITY, 1)?;

        assert_eq!(entries, vec![entry(0, 10)]);
        assert_eq!(journal.next_sequence(), 2);
        Ok(())
    }

    #[test]
    fn a_block_that_was_never_flushed_is_not_committed() -> Result<()> {
        let mut storage = storage();
        let mut journal = Journal::empty(FIRST, CAPACITY, 1);
        journal.append(&mut storage, vec![entry(0, 10)])?;

        let mut sector = [0u8; SECTOR_SIZE];
        JournalBlock {
            sequence: 2,
            entries: vec![entry(1, 11)],
        }
        .encode(&mut sector);
        storage.write_at(FIRST + 1, &sector)?;

        let crashed = FakeStorage::from_image(storage.image_without_pending());
        let (_, entries) = Journal::replay(&crashed, FIRST, CAPACITY, 1)?;

        assert_eq!(entries, vec![entry(0, 10)]);
        Ok(())
    }

    /// After a checkpoint the journal starts again at block zero with a higher
    /// sequence. What is left of the previous round must not be read as
    /// following it.
    #[test]
    fn blocks_left_from_before_a_checkpoint_are_not_replayed() -> Result<()> {
        let mut storage = storage();
        let mut old = Journal::empty(FIRST, CAPACITY, 1);
        old.append(&mut storage, vec![entry(0, 10)])?;
        old.append(&mut storage, vec![entry(1, 11)])?;
        old.append(&mut storage, vec![entry(2, 12)])?;

        let mut fresh = Journal::empty(FIRST, CAPACITY, 4);
        fresh.append(&mut storage, vec![entry(3, 13)])?;

        let (journal, entries) = Journal::replay(&storage, FIRST, CAPACITY, 4)?;

        assert_eq!(entries, vec![entry(3, 13)]);
        assert_eq!(journal.blocks_used(), 1);
        Ok(())
    }

    #[test]
    fn a_full_journal_refuses_to_append() -> Result<()> {
        let mut storage = storage();
        let mut journal = Journal::empty(FIRST, CAPACITY, 1);
        for chunk in 0..CAPACITY {
            journal.append(&mut storage, vec![entry(chunk, 0)])?;
        }

        assert!(!journal.has_room());
        assert!(journal.append(&mut storage, vec![entry(99, 0)]).is_err());
        Ok(())
    }

    #[test]
    fn a_failed_flush_leaves_the_block_to_be_written_again() -> Result<()> {
        let mut storage = storage();
        let mut journal = Journal::empty(FIRST, CAPACITY, 1);
        journal.append(&mut storage, vec![entry(0, 10)])?;

        storage.fail_flushes_from(2);
        assert!(journal.append(&mut storage, vec![entry(1, 11)]).is_err());
        assert_eq!(journal.next_sequence(), 2);
        assert_eq!(journal.blocks_used(), 1);
        Ok(())
    }
}
