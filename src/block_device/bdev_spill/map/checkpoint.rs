//! A checkpoint: every chunk's authority in one place, so the journal does not
//! have to reach back to the beginning of time.
//!
//! A checkpoint is written and flushed, but it is not in use until a
//! superblock names it. That is what makes replacing one atomic: a half
//! written checkpoint sits in the slot nobody is pointed at.

use crate::backends::SECTOR_SIZE;
use crate::Result;

use super::format::{Authority, CheckpointHeader, AUTHORITY_SIZE};
use super::storage::MapStorage;

const AUTHORITIES_PER_SECTOR: usize = SECTOR_SIZE / AUTHORITY_SIZE;

/// Header sector plus however many the authorities take.
pub fn sectors_for(chunk_count: u64) -> u64 {
    1 + chunk_count.div_ceil(AUTHORITIES_PER_SECTOR as u64)
}

fn encode_body(authorities: &[Authority]) -> Vec<u8> {
    let sectors = authorities.len().div_ceil(AUTHORITIES_PER_SECTOR);
    let mut body = vec![0u8; sectors * SECTOR_SIZE];
    for (i, authority) in authorities.iter().enumerate() {
        let at = i * AUTHORITY_SIZE;
        authority.encode(&mut body[at..at + AUTHORITY_SIZE]);
    }
    body
}

pub fn write(
    storage: &mut dyn MapStorage,
    first_sector: u64,
    sequence: u64,
    journal_next_sequence: u64,
    authorities: &[Authority],
) -> Result<()> {
    let body = encode_body(authorities);
    let header = CheckpointHeader {
        sequence,
        chunk_count: authorities.len() as u64,
        journal_next_sequence,
        body_crc: crc32fast::hash(&body),
    };

    if !body.is_empty() {
        storage.write_at(first_sector + 1, &body)?;
    }
    let mut sector = [0u8; SECTOR_SIZE];
    header.encode(&mut sector);
    storage.write_at(first_sector, &sector)?;
    storage.flush()
}

pub fn read(
    storage: &dyn MapStorage,
    first_sector: u64,
) -> Result<(CheckpointHeader, Vec<Authority>)> {
    let mut sector = [0u8; SECTOR_SIZE];
    storage.read_at(first_sector, &mut sector)?;
    let header = CheckpointHeader::decode(&sector).map_err(|e| {
        crate::ubiblk_error!(InvalidParameter {
            description: format!("unreadable checkpoint header: {e:?}"),
        })
    })?;

    let sectors = header
        .chunk_count
        .div_ceil(AUTHORITIES_PER_SECTOR as u64)
        .max(1) as usize;
    let mut body = vec![0u8; sectors * SECTOR_SIZE];
    storage.read_at(first_sector + 1, &mut body)?;

    let covered = header.chunk_count as usize * AUTHORITY_SIZE;
    let covered = covered.div_ceil(SECTOR_SIZE) * SECTOR_SIZE;
    if crc32fast::hash(&body[..covered]) != header.body_crc {
        return Err(crate::ubiblk_error!(InvalidParameter {
            description: "checkpoint body does not match its header".to_string(),
        }));
    }

    let mut authorities = Vec::with_capacity(header.chunk_count as usize);
    for i in 0..header.chunk_count as usize {
        let at = i * AUTHORITY_SIZE;
        authorities.push(
            Authority::decode(&body[at..at + AUTHORITY_SIZE]).map_err(|e| {
                crate::ubiblk_error!(InvalidParameter {
                    description: format!("unreadable authority for chunk {i}: {e:?}"),
                })
            })?,
        );
    }

    Ok((header, authorities))
}

#[cfg(test)]
mod tests {
    use super::super::fake::FakeStorage;
    use super::*;

    const FIRST: u64 = 2;

    fn authorities() -> Vec<Authority> {
        (0..40)
            .map(|i| match i % 4 {
                0 => Authority::Zero,
                1 => Authority::Local { slot: i },
                2 => Authority::Remote {
                    open: 1,
                    generation: i as u64,
                    digest: i as u64 * 7,
                },
                _ => Authority::Unreadable,
            })
            .collect()
    }

    fn storage() -> FakeStorage {
        FakeStorage::new(FIRST + sectors_for(40) + 1)
    }

    #[test]
    fn a_checkpoint_comes_back_as_it_went_in() -> Result<()> {
        let mut storage = storage();
        write(&mut storage, FIRST, 5, 9, &authorities())?;

        let (header, read_back) = read(&storage, FIRST)?;

        assert_eq!(header.sequence, 5);
        assert_eq!(header.journal_next_sequence, 9);
        assert_eq!(read_back, authorities());
        Ok(())
    }

    #[test]
    fn a_checkpoint_whose_body_was_not_written_is_refused() -> Result<()> {
        let mut storage = storage();
        write(&mut storage, FIRST, 5, 9, &authorities())?;

        // The body sector reached the disk as half of itself.
        let mut half = vec![0u8; SECTOR_SIZE];
        storage.read_at(FIRST + 1, &mut half)?;
        half[64..].fill(0);
        storage.write_at(FIRST + 1, &half)?;
        storage.flush()?;

        assert!(read(&storage, FIRST).is_err());
        Ok(())
    }

    #[test]
    fn a_checkpoint_whose_header_was_not_written_is_refused() -> Result<()> {
        let mut storage = storage();
        write(&mut storage, FIRST, 5, 9, &authorities())?;
        storage.write_at(FIRST, &[0u8; SECTOR_SIZE])?;
        storage.flush()?;

        assert!(read(&storage, FIRST).is_err());
        Ok(())
    }

    #[test]
    fn an_empty_map_still_checkpoints() -> Result<()> {
        let mut storage = storage();
        write(&mut storage, FIRST, 1, 1, &[])?;

        let (header, read_back) = read(&storage, FIRST)?;

        assert_eq!(header.chunk_count, 0);
        assert!(read_back.is_empty());
        Ok(())
    }

    #[test]
    fn the_space_a_checkpoint_needs_counts_its_header() {
        assert_eq!(sectors_for(0), 1);
        assert_eq!(sectors_for(1), 2);
        assert_eq!(sectors_for(AUTHORITIES_PER_SECTOR as u64), 2);
        assert_eq!(sectors_for(AUTHORITIES_PER_SECTOR as u64 + 1), 3);
    }
}
