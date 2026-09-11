//! On-disk shapes for the authority map.
//!
//! Every structure is written and read as whole sectors, so a torn write costs
//! the sector it was in and nothing else. Each sector carries a CRC over the
//! rest of itself, which is how recovery tells a torn write from a short one.

use crate::backends::SECTOR_SIZE;

pub const FORMAT_VERSION: u32 = 1;
pub const SUPERBLOCK_MAGIC: u64 = 0x5542_494d_4150_3031; // "UBIMAP01"
pub const CHECKPOINT_MAGIC: u32 = 0x554d_4350; // "UMCP"
pub const JOURNAL_MAGIC: u32 = 0x554d_4a4c; // "UMJL"

pub const AUTHORITY_SIZE: usize = 32;
pub const JOURNAL_ENTRY_SIZE: usize = 64;
pub const JOURNAL_HEADER_SIZE: usize = 64;
pub const JOURNAL_ENTRIES_PER_BLOCK: usize =
    (SECTOR_SIZE - JOURNAL_HEADER_SIZE) / JOURNAL_ENTRY_SIZE;

/// Where the authoritative copy of a chunk is.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum Authority {
    /// Nothing was ever written.
    #[default]
    Zero,
    /// The slot on the local disk holds it.
    Local { slot: u32 },
    /// The object named by this open and generation holds it.
    Remote {
        open: u64,
        generation: u64,
        digest: u64,
    },
    /// A failed write left the contents uncertain.
    Unreadable,
}

const TAG_ZERO: u8 = 0;
const TAG_LOCAL: u8 = 1;
const TAG_REMOTE: u8 = 2;
const TAG_UNREADABLE: u8 = 3;

#[derive(Debug, PartialEq, Eq)]
pub enum DecodeError {
    Magic,
    Version(u32),
    Crc,
    Tag(u8),
    Truncated,
}

impl Authority {
    pub fn encode(&self, out: &mut [u8]) {
        out[..AUTHORITY_SIZE].fill(0);
        match *self {
            Authority::Zero => out[0] = TAG_ZERO,
            Authority::Local { slot } => {
                out[0] = TAG_LOCAL;
                out[4..8].copy_from_slice(&slot.to_le_bytes());
            }
            Authority::Remote {
                open,
                generation,
                digest,
            } => {
                out[0] = TAG_REMOTE;
                out[8..16].copy_from_slice(&open.to_le_bytes());
                out[16..24].copy_from_slice(&generation.to_le_bytes());
                out[24..32].copy_from_slice(&digest.to_le_bytes());
            }
            Authority::Unreadable => out[0] = TAG_UNREADABLE,
        }
    }

    pub fn decode(raw: &[u8]) -> Result<Authority, DecodeError> {
        if raw.len() < AUTHORITY_SIZE {
            return Err(DecodeError::Truncated);
        }
        match raw[0] {
            TAG_ZERO => Ok(Authority::Zero),
            TAG_LOCAL => Ok(Authority::Local {
                slot: u32::from_le_bytes(raw[4..8].try_into().unwrap()),
            }),
            TAG_REMOTE => Ok(Authority::Remote {
                open: u64::from_le_bytes(raw[8..16].try_into().unwrap()),
                generation: u64::from_le_bytes(raw[16..24].try_into().unwrap()),
                digest: u64::from_le_bytes(raw[24..32].try_into().unwrap()),
            }),
            TAG_UNREADABLE => Ok(Authority::Unreadable),
            tag => Err(DecodeError::Tag(tag)),
        }
    }
}

/// What a device is, checked against the files it is opened with.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Binding {
    pub device_uuid: [u8; 16],
    pub chunk_size: u32,
    pub logical_sector_count: u64,
    pub slot_count: u32,
    pub store_digest: [u8; 32],
}

/// Sector 0 and 1: the same shape, written alternately, the higher sequence
/// that still verifies winning. Naming the checkpoint here is what makes
/// replacing one an atomic choice rather than a hope.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Superblock {
    pub sequence: u64,
    pub binding: Binding,
    pub chunk_count: u64,
    pub checkpoint_slot: u8,
    pub journal_blocks: u64,
    pub journal_next_sequence: u64,
}

fn crc_of(sector: &[u8], skip: std::ops::Range<usize>) -> u32 {
    let mut hasher = crc32fast::Hasher::new();
    hasher.update(&sector[..skip.start]);
    hasher.update(&sector[skip.end..]);
    hasher.finalize()
}

impl Superblock {
    const CRC: std::ops::Range<usize> = 12..16;

    pub fn encode(&self, sector: &mut [u8]) {
        sector[..SECTOR_SIZE].fill(0);
        sector[0..8].copy_from_slice(&SUPERBLOCK_MAGIC.to_le_bytes());
        sector[8..12].copy_from_slice(&FORMAT_VERSION.to_le_bytes());
        sector[16..24].copy_from_slice(&self.sequence.to_le_bytes());
        sector[24..40].copy_from_slice(&self.binding.device_uuid);
        sector[40..44].copy_from_slice(&self.binding.chunk_size.to_le_bytes());
        sector[44..52].copy_from_slice(&self.binding.logical_sector_count.to_le_bytes());
        sector[52..56].copy_from_slice(&self.binding.slot_count.to_le_bytes());
        sector[56..64].copy_from_slice(&self.chunk_count.to_le_bytes());
        sector[64] = self.checkpoint_slot;
        sector[72..80].copy_from_slice(&self.journal_blocks.to_le_bytes());
        sector[80..88].copy_from_slice(&self.journal_next_sequence.to_le_bytes());
        sector[88..120].copy_from_slice(&self.binding.store_digest);
        let crc = crc_of(&sector[..SECTOR_SIZE], Self::CRC);
        sector[Self::CRC].copy_from_slice(&crc.to_le_bytes());
    }

    pub fn decode(sector: &[u8]) -> Result<Superblock, DecodeError> {
        if sector.len() < SECTOR_SIZE {
            return Err(DecodeError::Truncated);
        }
        if u64::from_le_bytes(sector[0..8].try_into().unwrap()) != SUPERBLOCK_MAGIC {
            return Err(DecodeError::Magic);
        }
        let version = u32::from_le_bytes(sector[8..12].try_into().unwrap());
        if version != FORMAT_VERSION {
            return Err(DecodeError::Version(version));
        }
        let stored = u32::from_le_bytes(sector[Self::CRC].try_into().unwrap());
        if stored != crc_of(&sector[..SECTOR_SIZE], Self::CRC) {
            return Err(DecodeError::Crc);
        }
        Ok(Superblock {
            sequence: u64::from_le_bytes(sector[16..24].try_into().unwrap()),
            binding: Binding {
                device_uuid: sector[24..40].try_into().unwrap(),
                chunk_size: u32::from_le_bytes(sector[40..44].try_into().unwrap()),
                logical_sector_count: u64::from_le_bytes(sector[44..52].try_into().unwrap()),
                slot_count: u32::from_le_bytes(sector[52..56].try_into().unwrap()),
                store_digest: sector[88..120].try_into().unwrap(),
            },
            chunk_count: u64::from_le_bytes(sector[56..64].try_into().unwrap()),
            checkpoint_slot: sector[64],
            journal_blocks: u64::from_le_bytes(sector[72..80].try_into().unwrap()),
            journal_next_sequence: u64::from_le_bytes(sector[80..88].try_into().unwrap()),
        })
    }
}

/// The first sector of a checkpoint: what the body is and whether it arrived.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckpointHeader {
    pub sequence: u64,
    pub chunk_count: u64,
    pub journal_next_sequence: u64,
    pub body_crc: u32,
}

impl CheckpointHeader {
    const CRC: std::ops::Range<usize> = 8..12;

    pub fn encode(&self, sector: &mut [u8]) {
        sector[..SECTOR_SIZE].fill(0);
        sector[0..4].copy_from_slice(&CHECKPOINT_MAGIC.to_le_bytes());
        sector[4..8].copy_from_slice(&FORMAT_VERSION.to_le_bytes());
        sector[16..24].copy_from_slice(&self.sequence.to_le_bytes());
        sector[24..32].copy_from_slice(&self.chunk_count.to_le_bytes());
        sector[32..40].copy_from_slice(&self.journal_next_sequence.to_le_bytes());
        sector[40..44].copy_from_slice(&self.body_crc.to_le_bytes());
        let crc = crc_of(&sector[..SECTOR_SIZE], Self::CRC);
        sector[Self::CRC].copy_from_slice(&crc.to_le_bytes());
    }

    pub fn decode(sector: &[u8]) -> Result<CheckpointHeader, DecodeError> {
        if sector.len() < SECTOR_SIZE {
            return Err(DecodeError::Truncated);
        }
        if u32::from_le_bytes(sector[0..4].try_into().unwrap()) != CHECKPOINT_MAGIC {
            return Err(DecodeError::Magic);
        }
        let version = u32::from_le_bytes(sector[4..8].try_into().unwrap());
        if version != FORMAT_VERSION {
            return Err(DecodeError::Version(version));
        }
        let stored = u32::from_le_bytes(sector[Self::CRC].try_into().unwrap());
        if stored != crc_of(&sector[..SECTOR_SIZE], Self::CRC) {
            return Err(DecodeError::Crc);
        }
        Ok(CheckpointHeader {
            sequence: u64::from_le_bytes(sector[16..24].try_into().unwrap()),
            chunk_count: u64::from_le_bytes(sector[24..32].try_into().unwrap()),
            journal_next_sequence: u64::from_le_bytes(sector[32..40].try_into().unwrap()),
            body_crc: u32::from_le_bytes(sector[40..44].try_into().unwrap()),
        })
    }
}

/// One authority change, as it appears in a journal block.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct JournalEntry {
    pub chunk: u64,
    pub authority: Authority,
}

/// A journal block is the unit of commit: a whole sector, written once and
/// never rewritten, so an append cannot tear a record that is already
/// acknowledged.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JournalBlock {
    pub sequence: u64,
    pub entries: Vec<JournalEntry>,
}

impl JournalBlock {
    const CRC: std::ops::Range<usize> = 4..8;

    pub fn encode(&self, sector: &mut [u8]) {
        assert!(self.entries.len() <= JOURNAL_ENTRIES_PER_BLOCK);
        sector[..SECTOR_SIZE].fill(0);
        sector[0..4].copy_from_slice(&JOURNAL_MAGIC.to_le_bytes());
        sector[8..16].copy_from_slice(&self.sequence.to_le_bytes());
        sector[16..20].copy_from_slice(&(self.entries.len() as u32).to_le_bytes());
        sector[20..24].copy_from_slice(&FORMAT_VERSION.to_le_bytes());
        for (i, entry) in self.entries.iter().enumerate() {
            let at = JOURNAL_HEADER_SIZE + i * JOURNAL_ENTRY_SIZE;
            sector[at..at + 8].copy_from_slice(&entry.chunk.to_le_bytes());
            entry
                .authority
                .encode(&mut sector[at + 8..at + 8 + AUTHORITY_SIZE]);
        }
        let crc = crc_of(&sector[..SECTOR_SIZE], Self::CRC);
        sector[Self::CRC].copy_from_slice(&crc.to_le_bytes());
    }

    pub fn decode(sector: &[u8]) -> Result<JournalBlock, DecodeError> {
        if sector.len() < SECTOR_SIZE {
            return Err(DecodeError::Truncated);
        }
        if u32::from_le_bytes(sector[0..4].try_into().unwrap()) != JOURNAL_MAGIC {
            return Err(DecodeError::Magic);
        }
        let version = u32::from_le_bytes(sector[20..24].try_into().unwrap());
        if version != FORMAT_VERSION {
            return Err(DecodeError::Version(version));
        }
        let stored = u32::from_le_bytes(sector[Self::CRC].try_into().unwrap());
        if stored != crc_of(&sector[..SECTOR_SIZE], Self::CRC) {
            return Err(DecodeError::Crc);
        }
        let count = u32::from_le_bytes(sector[16..20].try_into().unwrap()) as usize;
        if count > JOURNAL_ENTRIES_PER_BLOCK {
            return Err(DecodeError::Truncated);
        }
        let mut entries = Vec::with_capacity(count);
        for i in 0..count {
            let at = JOURNAL_HEADER_SIZE + i * JOURNAL_ENTRY_SIZE;
            entries.push(JournalEntry {
                chunk: u64::from_le_bytes(sector[at..at + 8].try_into().unwrap()),
                authority: Authority::decode(&sector[at + 8..at + 8 + AUTHORITY_SIZE])?,
            });
        }
        Ok(JournalBlock {
            sequence: u64::from_le_bytes(sector[8..16].try_into().unwrap()),
            entries,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn binding() -> Binding {
        Binding {
            device_uuid: [7u8; 16],
            chunk_size: 128 * 1024,
            logical_sector_count: 12345,
            slot_count: 64,
            store_digest: [9u8; 32],
        }
    }

    fn superblock() -> Superblock {
        Superblock {
            sequence: 42,
            binding: binding(),
            chunk_count: 97,
            checkpoint_slot: 1,
            journal_blocks: 256,
            journal_next_sequence: 4096,
        }
    }

    #[test]
    fn an_authority_survives_a_round_trip() {
        let cases = [
            Authority::Zero,
            Authority::Local { slot: 4_000_000 },
            Authority::Remote {
                open: u64::MAX,
                generation: 7,
                digest: 0xdead_beef_dead_beef,
            },
            Authority::Unreadable,
        ];
        for authority in cases {
            let mut raw = [0xFFu8; AUTHORITY_SIZE];
            authority.encode(&mut raw);
            assert_eq!(Authority::decode(&raw), Ok(authority));
        }
    }

    #[test]
    fn an_authority_this_version_does_not_know_is_not_guessed_at() {
        let mut raw = [0u8; AUTHORITY_SIZE];
        raw[0] = 9;
        assert_eq!(Authority::decode(&raw), Err(DecodeError::Tag(9)));
    }

    #[test]
    fn a_superblock_survives_a_round_trip() {
        let mut sector = [0xFFu8; SECTOR_SIZE];
        superblock().encode(&mut sector);
        assert_eq!(Superblock::decode(&sector), Ok(superblock()));
    }

    #[test]
    fn every_byte_of_a_superblock_is_covered_by_its_crc() {
        let mut sector = [0u8; SECTOR_SIZE];
        superblock().encode(&mut sector);
        for byte in 0..SECTOR_SIZE {
            if Superblock::CRC.contains(&byte) {
                continue;
            }
            let mut torn = sector;
            torn[byte] ^= 0xFF;
            let decoded = Superblock::decode(&torn);
            assert!(
                decoded.is_err(),
                "flipping byte {byte} left a superblock that still verifies"
            );
        }
    }

    #[test]
    fn a_checkpoint_header_survives_a_round_trip() {
        let header = CheckpointHeader {
            sequence: 11,
            chunk_count: 500,
            journal_next_sequence: 12,
            body_crc: 0x1234_5678,
        };
        let mut sector = [0xFFu8; SECTOR_SIZE];
        header.encode(&mut sector);
        assert_eq!(CheckpointHeader::decode(&sector), Ok(header));
    }

    #[test]
    fn a_journal_block_survives_a_round_trip() {
        let block = JournalBlock {
            sequence: 3,
            entries: vec![
                JournalEntry {
                    chunk: 0,
                    authority: Authority::Local { slot: 1 },
                },
                JournalEntry {
                    chunk: 999,
                    authority: Authority::Remote {
                        open: 5,
                        generation: 6,
                        digest: 7,
                    },
                },
            ],
        };
        let mut sector = [0xFFu8; SECTOR_SIZE];
        block.encode(&mut sector);
        assert_eq!(JournalBlock::decode(&sector), Ok(block));
    }

    #[test]
    fn a_full_journal_block_survives_a_round_trip() {
        let block = JournalBlock {
            sequence: 1,
            entries: (0..JOURNAL_ENTRIES_PER_BLOCK)
                .map(|i| JournalEntry {
                    chunk: i as u64,
                    authority: Authority::Local { slot: i as u32 },
                })
                .collect(),
        };
        let mut sector = [0u8; SECTOR_SIZE];
        block.encode(&mut sector);
        assert_eq!(JournalBlock::decode(&sector), Ok(block));
    }

    /// A block torn anywhere must read as damaged rather than as fewer, or
    /// different, entries than were committed.
    #[test]
    fn every_byte_of_a_journal_block_is_covered_by_its_crc() {
        let block = JournalBlock {
            sequence: 8,
            entries: vec![JournalEntry {
                chunk: 3,
                authority: Authority::Local { slot: 2 },
            }],
        };
        let mut sector = [0u8; SECTOR_SIZE];
        block.encode(&mut sector);
        for byte in 0..SECTOR_SIZE {
            if JournalBlock::CRC.contains(&byte) {
                continue;
            }
            let mut torn = sector;
            torn[byte] ^= 0xFF;
            assert!(
                JournalBlock::decode(&torn).is_err(),
                "flipping byte {byte} left a journal block that still verifies"
            );
        }
    }

    #[test]
    fn a_sector_of_zeroes_is_not_a_record() {
        let empty = [0u8; SECTOR_SIZE];
        assert_eq!(Superblock::decode(&empty), Err(DecodeError::Magic));
        assert_eq!(CheckpointHeader::decode(&empty), Err(DecodeError::Magic));
        assert_eq!(JournalBlock::decode(&empty), Err(DecodeError::Magic));
    }
}
