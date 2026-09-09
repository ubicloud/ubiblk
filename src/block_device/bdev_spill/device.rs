use std::sync::{Arc, Mutex};

use crate::{
    archive::ArchiveStore,
    block_device::{BlockDevice, IoChannel},
    Result, ResultExt,
};

use super::channel::SpillIoChannel;
use super::map::AddressMap;
use super::shared::Shared;

/// Builds a connection to the object store. Each channel and the evictor get
/// their own: the archive trait's asynchronous and synchronous calls must not
/// be mixed on one, and a shared one would hand a caller another's completions.
pub type StoreFactory = Arc<dyn Fn() -> Result<Box<dyn ArchiveStore + Send>> + Send + Sync>;

/// A device that presents more space than the disk under it holds. The disk is
/// a cache of chunk-sized slots; a chunk that is not in one is in the object
/// store, and is fetched into a slot to be read.
///
/// **The address map is in memory, so a device's content does not survive a
/// restart.** Rebuilding it would mean knowing which chunk is in which slot,
/// which is not written down. Reusing a prefix across restarts would resurrect
/// the previous life's chunks under an empty cache, so don't: a prefix belongs
/// to one lifetime of one device.
pub struct SpillBlockDevice {
    base: Box<dyn BlockDevice>,
    shared: Arc<Shared>,
    store_factory: StoreFactory,
    sector_count: u64,
}

impl SpillBlockDevice {
    pub fn new(
        base: Box<dyn BlockDevice>,
        sector_count: u64,
        chunk_sectors: u64,
        prefix: &str,
        store_factory: StoreFactory,
    ) -> Result<Self> {
        if chunk_sectors == 0 {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: "spill chunk size must not be zero".to_string(),
            }));
        }
        let slots = (base.sector_count() / chunk_sectors) as usize;
        if slots == 0 {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: format!(
                    "the disk below holds {} sectors, not one {chunk_sectors}-sector chunk",
                    base.sector_count()
                ),
            }));
        }

        let shared = Arc::new(Shared {
            map: Mutex::new(AddressMap::new(slots)),
            chunk_sectors,
            prefix: prefix.to_string(),
        });

        Ok(Self {
            base,
            shared,
            store_factory,
            sector_count,
        })
    }

    pub fn slots(&self) -> usize {
        self.shared.map.lock().unwrap().slots()
    }

    pub fn resident_chunks(&self) -> usize {
        self.shared.resident_chunks()
    }

    #[cfg(test)]
    pub(super) fn is_resident(&self, chunk_id: usize) -> bool {
        self.shared.map.lock().unwrap().slot_of(chunk_id).is_some()
    }

    /// Free one named chunk's slot. Which slot goes is the policy's decision,
    /// so a test that wants to say something about one chunk cannot go through
    /// it. Returns whether it had to be uploaded.
    #[cfg(test)]
    pub(super) fn evict_named(&self, chunk_id: usize) -> Result<bool> {
        use crate::block_device::{shared_buffer, wait_for_completion};

        let slot = self
            .shared
            .map
            .lock()
            .unwrap()
            .slot_of(chunk_id)
            .expect("chunk is not resident");
        let dirty = self.shared.map.lock().unwrap().take(chunk_id, slot);
        if dirty {
            let mut base = self.base.create_channel()?;
            let buf = shared_buffer(self.shared.chunk_len());
            base.add_read(
                self.shared.slot_sector(slot),
                self.shared.chunk_sectors as u32,
                buf.clone(),
                0,
            );
            base.submit()?;
            wait_for_completion(base.as_mut(), 0, std::time::Duration::from_secs(30))?;
            let data = buf.borrow().as_slice()[..self.shared.chunk_len()].to_vec();
            (self.store_factory)()?.put_object(
                &self.shared.object_name(chunk_id),
                &data,
                crate::archive::DEFAULT_ARCHIVE_TIMEOUT,
            )?;
        }
        self.shared
            .map
            .lock()
            .unwrap()
            .release(slot, chunk_id, true);
        Ok(dirty)
    }
}

impl BlockDevice for SpillBlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>> {
        Ok(Box::new(SpillIoChannel::new(
            self.base.create_channel()?,
            self.shared.clone(),
            (self.store_factory)().context("Failed to reach the spill store")?,
        )))
    }

    fn sector_count(&self) -> u64 {
        self.sector_count
    }

    fn clone(&self) -> Box<dyn BlockDevice> {
        Box::new(SpillBlockDevice {
            base: self.base.clone(),
            shared: self.shared.clone(),
            store_factory: self.store_factory.clone(),
            sector_count: self.sector_count,
        })
    }
}
