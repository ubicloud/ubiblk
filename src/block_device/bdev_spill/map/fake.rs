//! Storage that can be crashed on purpose.
//!
//! A real disk will not tell us which of our writes reached it, so the tests
//! use one that does: writes sit in a pending list until a flush moves them to
//! the durable image, and a crash can keep any prefix of them, in any order,
//! with one of them torn. Recovery is then asked to make sense of the image
//! that survived.

use std::collections::HashMap;

use crate::backends::SECTOR_SIZE;
use crate::Result;

use super::storage::MapStorage;

#[derive(Clone)]
struct PendingWrite {
    sector: u64,
    data: Vec<u8>,
}

#[derive(Clone, Default)]
pub struct FakeStorage {
    durable: Vec<u8>,
    pending: Vec<PendingWrite>,
    pub writes: usize,
    pub flushes: usize,
    fail_writes_from: Option<usize>,
    fail_flushes_from: Option<usize>,
}

impl FakeStorage {
    pub fn new(sector_count: u64) -> Self {
        FakeStorage {
            durable: vec![0u8; sector_count as usize * SECTOR_SIZE],
            ..Default::default()
        }
    }

    pub fn from_image(durable: Vec<u8>) -> Self {
        FakeStorage {
            durable,
            ..Default::default()
        }
    }

    /// The bytes a crash right now would leave behind, keeping the pending
    /// writes named by `applied`, in the order given, and tearing the last of
    /// them after `torn_bytes`.
    pub fn image_after_crash(&self, applied: &[usize], torn_bytes: Option<usize>) -> Vec<u8> {
        let mut image = self.durable.clone();
        for (position, index) in applied.iter().enumerate() {
            let write = &self.pending[*index];
            let at = write.sector as usize * SECTOR_SIZE;
            let last = position + 1 == applied.len();
            let len = match torn_bytes {
                Some(bytes) if last => bytes.min(write.data.len()),
                _ => write.data.len(),
            };
            image[at..at + len].copy_from_slice(&write.data[..len]);
        }
        image
    }

    /// The bytes a crash right now would leave behind if nothing pending made
    /// it, which is the outcome a flush is there to rule out.
    pub fn image_without_pending(&self) -> Vec<u8> {
        self.durable.clone()
    }

    pub fn pending_count(&self) -> usize {
        self.pending.len()
    }

    pub fn fail_writes_from(&mut self, write: usize) {
        self.fail_writes_from = Some(write);
    }

    pub fn fail_flushes_from(&mut self, flush: usize) {
        self.fail_flushes_from = Some(flush);
    }

    fn overlay(&self) -> HashMap<u64, &[u8]> {
        let mut overlay = HashMap::new();
        for write in &self.pending {
            for (i, sector) in write.data.chunks(SECTOR_SIZE).enumerate() {
                overlay.insert(write.sector + i as u64, sector);
            }
        }
        overlay
    }
}

impl MapStorage for FakeStorage {
    fn read_at(&self, sector: u64, buf: &mut [u8]) -> Result<()> {
        let overlay = self.overlay();
        for (i, out) in buf.chunks_mut(SECTOR_SIZE).enumerate() {
            let at = sector + i as u64;
            match overlay.get(&at) {
                Some(pending) => out.copy_from_slice(pending),
                None => {
                    let from = at as usize * SECTOR_SIZE;
                    out.copy_from_slice(&self.durable[from..from + SECTOR_SIZE]);
                }
            }
        }
        Ok(())
    }

    fn write_at(&mut self, sector: u64, buf: &[u8]) -> Result<()> {
        self.writes += 1;
        if self.fail_writes_from.is_some_and(|at| self.writes >= at) {
            return Err(crate::ubiblk_error!(IoError {
                source: std::io::Error::other("injected map write failure"),
            }));
        }
        self.pending.push(PendingWrite {
            sector,
            data: buf.to_vec(),
        });
        Ok(())
    }

    fn flush(&mut self) -> Result<()> {
        self.flushes += 1;
        if self.fail_flushes_from.is_some_and(|at| self.flushes >= at) {
            return Err(crate::ubiblk_error!(IoError {
                source: std::io::Error::other("injected map flush failure"),
            }));
        }
        for write in self.pending.drain(..) {
            let at = write.sector as usize * SECTOR_SIZE;
            self.durable[at..at + write.data.len()].copy_from_slice(&write.data);
        }
        Ok(())
    }

    fn sector_count(&self) -> u64 {
        (self.durable.len() / SECTOR_SIZE) as u64
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_write_is_visible_before_it_is_durable() -> Result<()> {
        let mut storage = FakeStorage::new(4);
        storage.write_at(1, &[0xAAu8; SECTOR_SIZE])?;

        let mut read = [0u8; SECTOR_SIZE];
        storage.read_at(1, &mut read)?;
        assert_eq!(read, [0xAAu8; SECTOR_SIZE]);

        let crashed = storage.image_without_pending();
        assert_eq!(&crashed[SECTOR_SIZE..2 * SECTOR_SIZE], &[0u8; SECTOR_SIZE]);
        Ok(())
    }

    #[test]
    fn a_flush_makes_writes_survive_a_crash() -> Result<()> {
        let mut storage = FakeStorage::new(4);
        storage.write_at(1, &[0xAAu8; SECTOR_SIZE])?;
        storage.flush()?;

        let crashed = storage.image_without_pending();
        assert_eq!(
            &crashed[SECTOR_SIZE..2 * SECTOR_SIZE],
            &[0xAAu8; SECTOR_SIZE]
        );
        assert_eq!(storage.pending_count(), 0);
        Ok(())
    }

    #[test]
    fn a_crash_can_keep_some_writes_and_tear_one() -> Result<()> {
        let mut storage = FakeStorage::new(4);
        storage.write_at(0, &[1u8; SECTOR_SIZE])?;
        storage.write_at(1, &[2u8; SECTOR_SIZE])?;
        storage.write_at(2, &[3u8; SECTOR_SIZE])?;

        let image = storage.image_after_crash(&[0, 2], Some(8));

        assert_eq!(&image[..SECTOR_SIZE], &[1u8; SECTOR_SIZE]);
        assert_eq!(&image[SECTOR_SIZE..2 * SECTOR_SIZE], &[0u8; SECTOR_SIZE]);
        assert_eq!(&image[2 * SECTOR_SIZE..2 * SECTOR_SIZE + 8], &[3u8; 8]);
        assert_eq!(
            &image[2 * SECTOR_SIZE + 8..3 * SECTOR_SIZE],
            &[0u8; SECTOR_SIZE - 8]
        );
        Ok(())
    }

    #[test]
    fn an_injected_failure_stops_writing_and_flushing() {
        let mut storage = FakeStorage::new(2);
        storage.fail_writes_from(2);
        assert!(storage.write_at(0, &[0u8; SECTOR_SIZE]).is_ok());
        assert!(storage.write_at(0, &[0u8; SECTOR_SIZE]).is_err());

        let mut storage = FakeStorage::new(2);
        storage.fail_flushes_from(1);
        assert!(storage.flush().is_err());
    }
}
