use std::sync::Mutex;

use crate::backends::SECTOR_SIZE;

use super::map::AddressMap;

pub(super) struct Shared {
    pub map: Mutex<AddressMap>,
    pub chunk_sectors: u64,
    pub prefix: String,
}

impl Shared {
    pub fn chunk_len(&self) -> usize {
        self.chunk_sectors as usize * SECTOR_SIZE
    }

    pub fn object_name(&self, chunk_id: usize) -> String {
        format!("{}/chunk-{chunk_id:012}", self.prefix)
    }

    /// Where a chunk's slot starts on the device below.
    pub fn slot_sector(&self, slot: usize) -> u64 {
        slot as u64 * self.chunk_sectors
    }

    /// The same offset within the chunk, but in the slot holding it.
    pub fn mapped_sector(&self, sector: u64, slot: usize) -> u64 {
        self.slot_sector(slot) + sector % self.chunk_sectors
    }

    pub fn resident_chunks(&self) -> usize {
        self.map.lock().unwrap().resident()
    }
}
