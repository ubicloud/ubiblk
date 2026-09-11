//! The pair of sectors that says which checkpoint is live.
//!
//! Two copies, written alternately, the higher sequence that still verifies
//! winning. A crash during an update therefore costs the newer copy and leaves
//! the older one, which still describes a map that was true.

use crate::backends::SECTOR_SIZE;
use crate::Result;

use super::format::Superblock;
use super::storage::MapStorage;

pub const SECTORS: u64 = 2;

pub fn write(storage: &mut dyn MapStorage, superblock: &Superblock) -> Result<()> {
    let mut sector = [0u8; SECTOR_SIZE];
    superblock.encode(&mut sector);
    storage.write_at(superblock.sequence % SECTORS, &sector)?;
    storage.flush()
}

/// The newest superblock that verifies, or nothing if neither does.
pub fn read(storage: &dyn MapStorage) -> Result<Option<Superblock>> {
    let mut newest: Option<Superblock> = None;
    for at in 0..SECTORS {
        let mut sector = [0u8; SECTOR_SIZE];
        storage.read_at(at, &mut sector)?;
        if let Ok(candidate) = Superblock::decode(&sector) {
            if newest.is_none_or(|best| candidate.sequence > best.sequence) {
                newest = Some(candidate);
            }
        }
    }
    Ok(newest)
}

#[cfg(test)]
mod tests {
    use super::super::fake::FakeStorage;
    use super::super::format::Binding;
    use super::*;

    fn superblock(sequence: u64, checkpoint_slot: u8) -> Superblock {
        Superblock {
            sequence,
            binding: Binding {
                device_uuid: [1u8; 16],
                chunk_size: 128 * 1024,
                logical_sector_count: 2048,
                slot_count: 8,
                store_digest: [2u8; 32],
            },
            chunk_count: 16,
            checkpoint_slot,
            journal_blocks: 32,
            journal_next_sequence: sequence * 10,
        }
    }

    #[test]
    fn the_newer_superblock_wins() -> Result<()> {
        let mut storage = FakeStorage::new(4);
        write(&mut storage, &superblock(4, 0))?;
        write(&mut storage, &superblock(5, 1))?;

        assert_eq!(read(&storage)?, Some(superblock(5, 1)));
        Ok(())
    }

    /// Updates alternate, so the copy a crash did not reach still describes the
    /// checkpoint that was live before it.
    #[test]
    fn a_torn_update_leaves_the_previous_superblock() -> Result<()> {
        let mut storage = FakeStorage::new(4);
        write(&mut storage, &superblock(4, 0))?;

        let mut sector = [0u8; SECTOR_SIZE];
        superblock(5, 1).encode(&mut sector);
        storage.write_at(5 % SECTORS, &sector)?;
        let crashed = FakeStorage::from_image(storage.image_after_crash(&[0], Some(40)));

        assert_eq!(read(&crashed)?, Some(superblock(4, 0)));
        Ok(())
    }

    #[test]
    fn a_map_with_no_superblock_at_all_says_so() -> Result<()> {
        let storage = FakeStorage::new(4);
        assert_eq!(read(&storage)?, None);
        Ok(())
    }

    #[test]
    fn updates_alternate_rather_than_overwriting_the_live_copy() -> Result<()> {
        let mut storage = FakeStorage::new(4);
        for sequence in 1..=4 {
            write(&mut storage, &superblock(sequence, 0))?;
        }

        let mut first = [0u8; SECTOR_SIZE];
        let mut second = [0u8; SECTOR_SIZE];
        storage.read_at(0, &mut first)?;
        storage.read_at(1, &mut second)?;

        assert_eq!(Superblock::decode(&first).unwrap().sequence, 4);
        assert_eq!(Superblock::decode(&second).unwrap().sequence, 3);
        Ok(())
    }
}
