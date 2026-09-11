//! The durable map: where the authoritative copy of each chunk is.
//!
//! A checkpoint plus the journal blocks that follow it is the whole story. A
//! commit appends to the journal; when the journal fills, a checkpoint is
//! written into the slot that is not in use and a superblock update makes it
//! live, which is the only moment the old journal stops mattering.
//!
//! Layout, in sectors:
//!
//! ```text
//!   0, 1        superblocks, written alternately
//!   2 ..        checkpoint slot 0
//!   ...         checkpoint slot 1
//!   ...         journal blocks
//! ```

pub mod checkpoint;
pub mod format;
pub mod journal;
pub mod storage;
pub mod superblock;

#[cfg(test)]
pub mod crash;
#[cfg(test)]
pub mod fake;

use crate::Result;

use format::{Authority, Binding, JournalEntry, Superblock, JOURNAL_ENTRIES_PER_BLOCK};
use journal::Journal;
use storage::MapStorage;

/// How much room a map needs, so a caller can size its file.
pub fn sectors_needed(chunk_count: u64, journal_blocks: u64) -> u64 {
    superblock::SECTORS + 2 * checkpoint::sectors_for(chunk_count) + journal_blocks
}

pub struct Map<S: MapStorage> {
    storage: S,
    binding: Binding,
    authorities: Vec<Authority>,
    staged: Vec<JournalEntry>,
    journal: Journal,
    journal_blocks: u64,
    checkpoint_slot: u8,
    superblock_sequence: u64,
    failed: bool,
}

impl<S: MapStorage> Map<S> {
    fn checkpoint_sector(&self, slot: u8) -> u64 {
        superblock::SECTORS + u64::from(slot) * checkpoint::sectors_for(self.chunk_count())
    }

    fn journal_first_sector(&self) -> u64 {
        superblock::SECTORS + 2 * checkpoint::sectors_for(self.chunk_count())
    }

    pub fn chunk_count(&self) -> u64 {
        self.authorities.len() as u64
    }

    /// Lay out a fresh map: every chunk `Zero`, an empty journal, and a
    /// superblock naming the checkpoint that says so.
    pub fn create(
        mut storage: S,
        binding: Binding,
        chunk_count: u64,
        journal_blocks: u64,
    ) -> Result<Self> {
        if storage.sector_count() < sectors_needed(chunk_count, journal_blocks) {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: format!(
                    "a map for {chunk_count} chunks needs {} sectors, not {}",
                    sectors_needed(chunk_count, journal_blocks),
                    storage.sector_count()
                ),
            }));
        }

        if superblock::read(&storage)?.is_some() {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: "a map is already here: open it rather than starting again"
                    .to_string(),
            }));
        }

        let authorities = vec![Authority::Zero; chunk_count as usize];
        let first_checkpoint = superblock::SECTORS;
        checkpoint::write(&mut storage, first_checkpoint, 1, 1, &authorities)?;
        let head = Superblock {
            sequence: 1,
            binding,
            chunk_count,
            checkpoint_slot: 0,
            journal_blocks,
            journal_next_sequence: 1,
        };
        superblock::write(&mut storage, &head)?;

        let journal_first = superblock::SECTORS + 2 * checkpoint::sectors_for(chunk_count);
        Ok(Map {
            storage,
            binding,
            authorities,
            staged: Vec::new(),
            journal: Journal::empty(journal_first, journal_blocks, 1),
            journal_blocks,
            checkpoint_slot: 0,
            superblock_sequence: 1,
            failed: false,
        })
    }

    /// Recover: the live checkpoint, then every journal block that follows it.
    pub fn open(storage: S, expected: Binding) -> Result<Self> {
        let Some(head) = superblock::read(&storage)? else {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: "no readable superblock: this is not a map".to_string(),
            }));
        };
        if head.binding != expected {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: format!(
                    "this map is for another device: {:?} on disk, {:?} configured",
                    head.binding, expected
                ),
            }));
        }

        let checkpoint_sectors = checkpoint::sectors_for(head.chunk_count);
        let first_checkpoint =
            superblock::SECTORS + u64::from(head.checkpoint_slot) * checkpoint_sectors;
        let (_, mut authorities) = checkpoint::read(&storage, first_checkpoint)?;
        if authorities.len() as u64 != head.chunk_count {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: format!(
                    "checkpoint holds {} chunks, superblock says {}",
                    authorities.len(),
                    head.chunk_count
                ),
            }));
        }

        let journal_first = superblock::SECTORS + 2 * checkpoint_sectors;
        let (journal, entries) = Journal::replay(
            &storage,
            journal_first,
            head.journal_blocks,
            head.journal_next_sequence,
        )?;
        for entry in entries {
            let Some(slot) = authorities.get_mut(entry.chunk as usize) else {
                return Err(crate::ubiblk_error!(InvalidParameter {
                    description: format!("journal names chunk {}, past the end", entry.chunk),
                }));
            };
            *slot = entry.authority;
        }

        Ok(Map {
            storage,
            binding: head.binding,
            authorities,
            staged: Vec::new(),
            journal,
            journal_blocks: head.journal_blocks,
            checkpoint_slot: head.checkpoint_slot,
            superblock_sequence: head.sequence,
            failed: false,
        })
    }

    pub fn authority(&self, chunk: u64) -> Authority {
        self.authorities[chunk as usize]
    }

    pub fn binding(&self) -> &Binding {
        &self.binding
    }

    /// Once a map has failed a write it stops committing: the caller cannot
    /// reuse a slot or discharge a durability promise on a map that may not
    /// describe the disk any more.
    pub fn failed(&self) -> bool {
        self.failed
    }

    /// Stage a change. Nothing is durable, and nothing is visible to
    /// `authority`, until `commit` returns.
    pub fn stage(&mut self, chunk: u64, authority: Authority) -> Result<()> {
        if chunk >= self.chunk_count() {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: format!("chunk {chunk} is past the end of the map"),
            }));
        }
        self.staged.push(JournalEntry { chunk, authority });
        Ok(())
    }

    /// Make everything staged durable. Returning `Ok` is the acknowledgement
    /// that authorises reusing a released slot.
    pub fn commit(&mut self) -> Result<()> {
        if self.failed {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: "the map has failed a write and cannot commit".to_string(),
            }));
        }
        if self.staged.is_empty() {
            return Ok(());
        }

        let staged = std::mem::take(&mut self.staged);
        for batch in staged.chunks(JOURNAL_ENTRIES_PER_BLOCK) {
            // Checked for each block rather than for the batch: a commit can
            // be larger than the whole journal, and a checkpoint in the middle
            // of one carries what has been applied so far.
            if !self.journal.has_room() {
                self.checkpoint()?;
            }
            if let Err(e) = self.journal.append(&mut self.storage, batch.to_vec()) {
                self.failed = true;
                return Err(e);
            }
            for entry in batch {
                self.authorities[entry.chunk as usize] = entry.authority;
            }
        }
        Ok(())
    }

    /// Write the whole map into the slot that is not in use, then name it.
    /// Until the superblock is durable the old checkpoint and its journal are
    /// still what recovery reads, so this cannot lose a committed change.
    pub fn checkpoint(&mut self) -> Result<()> {
        if self.failed {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: "the map has failed a write and cannot checkpoint".to_string(),
            }));
        }

        let next_slot = 1 - self.checkpoint_slot;
        let restart_sequence = self.journal.next_sequence();
        let at = self.checkpoint_sector(next_slot);
        let head = Superblock {
            sequence: self.superblock_sequence + 1,
            binding: self.binding,
            chunk_count: self.chunk_count(),
            checkpoint_slot: next_slot,
            journal_blocks: self.journal_blocks,
            journal_next_sequence: restart_sequence,
        };

        let result = checkpoint::write(
            &mut self.storage,
            at,
            head.sequence,
            restart_sequence,
            &self.authorities,
        )
        .and_then(|()| superblock::write(&mut self.storage, &head));

        if let Err(e) = result {
            self.failed = true;
            return Err(e);
        }

        self.checkpoint_slot = next_slot;
        self.superblock_sequence += 1;
        self.journal = Journal::empty(
            self.journal_first_sector(),
            self.journal_blocks,
            restart_sequence,
        );
        Ok(())
    }

    pub fn storage(&self) -> &S {
        &self.storage
    }
}

#[cfg(test)]
mod tests {
    use super::fake::FakeStorage;
    use super::storage::FileStorage;
    use super::*;

    const CHUNKS: u64 = 40;
    const JOURNAL_BLOCKS: u64 = 4;
    use super::format::JOURNAL_ENTRIES_PER_BLOCK;

    fn binding() -> Binding {
        Binding {
            device_uuid: [3u8; 16],
            chunk_size: 128 * 1024,
            logical_sector_count: 10_000,
            slot_count: 16,
            store_digest: [4u8; 32],
        }
    }

    fn fresh() -> Map<FakeStorage> {
        let storage = FakeStorage::new(sectors_needed(CHUNKS, JOURNAL_BLOCKS));
        Map::create(storage, binding(), CHUNKS, JOURNAL_BLOCKS).unwrap()
    }

    fn reopen(map: &Map<FakeStorage>) -> Result<Map<FakeStorage>> {
        Map::open(
            FakeStorage::from_image(map.storage().image_without_pending()),
            binding(),
        )
    }

    fn local(slot: u32) -> Authority {
        Authority::Local { slot }
    }

    fn remote(generation: u64) -> Authority {
        Authority::Remote {
            open: 77,
            generation,
            digest: generation * 3,
        }
    }

    #[test]
    fn a_fresh_map_says_nothing_was_ever_written() -> Result<()> {
        let map = fresh();
        for chunk in 0..CHUNKS {
            assert_eq!(map.authority(chunk), Authority::Zero);
        }
        let reopened = reopen(&map)?;
        assert_eq!(reopened.authority(CHUNKS - 1), Authority::Zero);
        Ok(())
    }

    #[test]
    fn a_committed_change_is_there_after_a_crash() -> Result<()> {
        let mut map = fresh();
        map.stage(1, local(5))?;
        map.stage(2, remote(9))?;
        map.commit()?;

        let reopened = reopen(&map)?;

        assert_eq!(reopened.authority(1), local(5));
        assert_eq!(reopened.authority(2), remote(9));
        Ok(())
    }

    #[test]
    fn a_change_that_was_only_staged_is_not_there_and_is_not_claimed() -> Result<()> {
        let mut map = fresh();
        map.stage(1, local(5))?;

        assert_eq!(map.authority(1), Authority::Zero);
        assert_eq!(reopen(&map)?.authority(1), Authority::Zero);
        Ok(())
    }

    /// Creating is for a map that is not there. Doing it over one that is
    /// would throw away everything it knows, and the caller that asked has
    /// mistaken a reopen for a first run.
    #[test]
    fn creating_a_map_where_one_already_exists_is_refused() -> Result<()> {
        let mut map = fresh();
        map.stage(0, local(1))?;
        map.commit()?;

        let storage = FakeStorage::from_image(map.storage().image_without_pending());
        assert!(Map::create(storage.clone(), binding(), CHUNKS, JOURNAL_BLOCKS).is_err());

        assert_eq!(Map::open(storage, binding())?.authority(0), local(1));
        Ok(())
    }

    #[test]
    fn a_chunk_past_the_end_is_refused() {
        let mut map = fresh();
        assert!(map.stage(CHUNKS, local(0)).is_err());
    }

    #[test]
    fn a_map_belonging_to_another_device_is_refused() -> Result<()> {
        let map = fresh();
        let mut other = binding();
        other.device_uuid = [9u8; 16];

        let opened = Map::open(
            FakeStorage::from_image(map.storage().image_without_pending()),
            other,
        );

        assert!(opened.is_err());
        Ok(())
    }

    /// The same files with a different logical size have the same chunk count
    /// and pass every other check, so capacity is part of what is compared.
    #[test]
    fn a_map_for_the_same_chunks_but_a_different_size_is_refused() -> Result<()> {
        let map = fresh();
        let mut resized = binding();
        resized.logical_sector_count += 8;

        assert!(Map::open(
            FakeStorage::from_image(map.storage().image_without_pending()),
            resized
        )
        .is_err());
        Ok(())
    }

    #[test]
    fn the_journal_is_compacted_before_it_overflows() -> Result<()> {
        let mut map = fresh();
        for round in 0..(JOURNAL_BLOCKS * 3) {
            map.stage(round % CHUNKS, local(round as u32))?;
            map.commit()?;
        }

        let reopened = reopen(&map)?;

        for round in 0..(JOURNAL_BLOCKS * 3) {
            assert_eq!(reopened.authority(round % CHUNKS), local(round as u32));
        }
        assert!(
            map.superblock_sequence > 1,
            "no checkpoint was ever written"
        );
        Ok(())
    }

    /// A commit can be larger than the whole journal: a flush covering every
    /// slot of a big cache is one entry per chunk.
    #[test]
    fn a_commit_larger_than_the_journal_still_commits() -> Result<()> {
        let mut map = fresh();
        let entries = (JOURNAL_ENTRIES_PER_BLOCK as u64 * JOURNAL_BLOCKS * 2).min(CHUNKS);
        assert!(entries > JOURNAL_ENTRIES_PER_BLOCK as u64 * JOURNAL_BLOCKS);

        for chunk in 0..entries {
            map.stage(chunk, local(chunk as u32))?;
        }
        map.commit()?;

        let reopened = reopen(&map)?;
        for chunk in 0..entries {
            assert_eq!(reopened.authority(chunk), local(chunk as u32));
        }
        assert!(!map.failed());
        Ok(())
    }

    /// The case the design exists for: once a release is acknowledged and its
    /// slot handed to another chunk, no recovery may go back to a map that
    /// still names the released slot - not through a checkpoint, and not
    /// through a journal block left over from before one.
    #[test]
    fn recovery_never_goes_back_across_an_acknowledged_release() -> Result<()> {
        let mut map = fresh();
        for (chunk, slot) in [(5, 5), (6, 6)] {
            map.stage(chunk, local(slot))?;
            map.commit()?;
        }
        // The last block before the checkpoint is the one that gives chunk 0
        // slot 7, so it stays on disk after the journal restarts.
        map.stage(0, local(7))?;
        map.commit()?;
        map.checkpoint()?;

        // Chunk 0 is uploaded and gives up slot 7; chunk 1 takes it.
        map.stage(0, remote(1))?;
        map.commit()?;
        map.stage(1, local(7))?;
        map.commit()?;

        let clean = map.storage().image_without_pending();
        let mut images = vec![clean.clone()];
        // And the same again for an append that was torn on its way out.
        for torn in [0, 96, 300] {
            let mut storage = FakeStorage::from_image(clean.clone());
            let mut sector = [0u8; crate::backends::SECTOR_SIZE];
            sector.fill(0xA5);
            storage.write_at(map.journal_first_sector() + 2, &sector)?;
            images.push(storage.image_after_crash(&[0], Some(torn)));
        }

        for (i, image) in images.into_iter().enumerate() {
            let recovered = Map::open(FakeStorage::from_image(image), binding())?;
            assert_eq!(recovered.authority(0), remote(1), "image {i}");
            assert_eq!(recovered.authority(1), local(7), "image {i}");
        }
        Ok(())
    }

    /// A checkpoint is only live once the superblock says so. Interrupted
    /// before that, the map is exactly what it was: the old checkpoint and the
    /// journal that follows it are both still there.
    #[test]
    fn a_checkpoint_interrupted_partway_leaves_the_map_as_it_was() -> Result<()> {
        let mut map = fresh();
        map.stage(0, local(1))?;
        map.commit()?;

        let fail_at = map.storage().writes + 3;
        map.storage.fail_writes_from(fail_at);
        assert!(map.checkpoint().is_err());

        let recovered = reopen(&map)?;

        assert_eq!(recovered.authority(0), local(1));
        Ok(())
    }

    #[test]
    fn a_map_on_a_file_reopens_with_what_it_committed() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("map");
        let sectors = sectors_needed(CHUNKS, JOURNAL_BLOCKS);

        {
            let mut map = Map::create(
                FileStorage::create(&path, sectors)?,
                binding(),
                CHUNKS,
                JOURNAL_BLOCKS,
            )?;
            for round in 0..(JOURNAL_BLOCKS * 3) {
                map.stage(round % CHUNKS, local(round as u32))?;
                map.commit()?;
            }
        }

        let reopened = Map::open(FileStorage::open(&path)?, binding())?;
        for round in 0..(JOURNAL_BLOCKS * 3) {
            assert_eq!(reopened.authority(round % CHUNKS), local(round as u32));
        }
        Ok(())
    }

    /// The map holds nothing in user space that a graceful exit would flush, so
    /// a process that dies outright still leaves a map with its commits in it.
    /// The child below aborts the moment its commit returns.
    #[test]
    fn a_committed_map_survives_the_process_dying() -> Result<()> {
        const CHILD: &str = "UBIBLK_MAP_ABORT_CHILD";
        const NAME: &str =
            "block_device::bdev_spill::map::tests::a_committed_map_survives_the_process_dying";

        if let Ok(path) = std::env::var(CHILD) {
            let path = std::path::PathBuf::from(path);
            let storage = FileStorage::create(&path, sectors_needed(CHUNKS, JOURNAL_BLOCKS))?;
            let mut map = Map::create(storage, binding(), CHUNKS, JOURNAL_BLOCKS)?;
            map.stage(2, local(9))?;
            map.commit()?;
            std::process::abort();
        }

        let dir = tempfile::tempdir()?;
        let path = dir.path().join("map");
        let status = std::process::Command::new(std::env::current_exe()?)
            .args([NAME, "--exact", "--nocapture"])
            .env(CHILD, &path)
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status()?;

        assert!(!status.success(), "the child was meant to abort");
        let map = Map::open(FileStorage::open(&path)?, binding())?;
        assert_eq!(map.authority(2), local(9));
        Ok(())
    }

    #[test]
    fn a_map_that_cannot_write_stops_committing() -> Result<()> {
        let mut map = fresh();
        map.storage.fail_writes_from(1);
        map.stage(0, local(1))?;

        assert!(map.commit().is_err());
        assert!(map.failed());

        map.stage(0, local(2))?;
        assert!(map.commit().is_err(), "a failed map committed anyway");
        assert!(map.checkpoint().is_err());
        Ok(())
    }

    #[test]
    fn a_commit_whose_flush_failed_is_not_reported_as_durable() -> Result<()> {
        let mut map = fresh();
        map.stage(0, local(1))?;
        map.commit()?;

        map.storage.fail_flushes_from(2);
        map.stage(0, local(2))?;
        assert!(map.commit().is_err());

        let recovered = reopen(&map)?;
        assert_eq!(recovered.authority(0), local(1));
        Ok(())
    }
}
