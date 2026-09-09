use std::sync::Arc;
use std::time::Duration;

use log::{debug, warn};

use crate::{
    archive::{ArchiveStore, DEFAULT_ARCHIVE_TIMEOUT},
    block_device::{wait_for_completion, IoChannel, SharedBuffer},
    Result,
};

use super::map::Victim;
use super::shared::Shared;

const IO_TIMEOUT: Duration = Duration::from_secs(30);
const BATCH: usize = 32;
const IDLE: Duration = Duration::from_millis(200);

/// Keeps slots free for the channels to hand out, on its own thread: on the
/// thread that serves reads, every upload stalls a read someone is waiting on.
pub struct Evictor {
    pub(super) shared: Arc<Shared>,
    pub(super) base: Box<dyn IoChannel>,
    pub(super) store: Box<dyn ArchiveStore + Send>,
    pub(super) buf: SharedBuffer,
    pub(super) next_id: usize,
    /// How many slots to keep free, so a miss usually finds one waiting.
    pub(super) headroom: usize,
}

impl Evictor {
    fn read_slot(&mut self, slot: usize) -> Result<()> {
        let id = self.next_id;
        self.next_id = self.next_id.wrapping_add(1);
        self.base.add_read(
            self.shared.slot_sector(slot),
            self.shared.chunk_sectors as u32,
            self.buf.clone(),
            id,
        );
        self.base.submit()?;
        wait_for_completion(self.base.as_mut(), id, IO_TIMEOUT)
    }

    fn upload(&mut self, slot: usize, chunk_id: usize) -> Result<()> {
        self.read_slot(slot)?;
        let data = self.buf.borrow().as_slice()[..self.shared.chunk_len()].to_vec();
        self.store.put_object(
            &self.shared.object_name(chunk_id),
            &data,
            DEFAULT_ARCHIVE_TIMEOUT,
        )
    }

    /// Free slots until there is headroom again. Returns what it moved.
    pub fn run_once(&mut self, budget: usize) -> (usize, usize) {
        let (mut dropped, mut uploaded) = (0, 0);
        for _ in 0..budget {
            {
                let map = self.shared.map.lock().unwrap();
                if map.free_slots() >= self.headroom || map.resident() == 0 {
                    break;
                }
            }
            let victim = self.shared.map.lock().unwrap().claim_victim();
            let Some(victim) = victim else { break };

            match victim {
                Victim::Clean { slot, chunk_id } => {
                    self.shared
                        .map
                        .lock()
                        .unwrap()
                        .release(slot, chunk_id, true);
                    dropped += 1;
                }
                Victim::Dirty { slot, chunk_id } => match self.upload(slot, chunk_id) {
                    Ok(()) => {
                        self.shared
                            .map
                            .lock()
                            .unwrap()
                            .release(slot, chunk_id, true);
                        uploaded += 1;
                    }
                    Err(e) => {
                        warn!("Failed to spill chunk {chunk_id}: {e}");
                        self.shared.map.lock().unwrap().restore(slot, chunk_id);
                        break;
                    }
                },
            }
        }
        if dropped + uploaded > 0 {
            debug!(
                "Spilled {uploaded} chunk(s), dropped {dropped} the store already had; {} slots free",
                self.shared.map.lock().unwrap().free_slots()
            );
        }
        (dropped, uploaded)
    }

    pub fn run(mut self) -> ! {
        loop {
            if self.run_once(BATCH) == (0, 0) {
                std::thread::sleep(IDLE);
            }
        }
    }
}
