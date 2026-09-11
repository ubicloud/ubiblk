//! Where the map's sectors live.
//!
//! The map needs to say when bytes are durable, not merely written, so its
//! storage is a narrow trait: whole sectors in and out, and a flush that means
//! what it says. The real one is a file; the test one can be crashed.

use std::fs::{File, OpenOptions};
use std::os::unix::fs::FileExt;
use std::path::Path;

use crate::backends::SECTOR_SIZE;
use crate::{Result, ResultExt};

pub trait MapStorage {
    fn read_at(&self, sector: u64, buf: &mut [u8]) -> Result<()>;
    /// Write whole sectors. They are durable only once `flush` returns.
    fn write_at(&mut self, sector: u64, buf: &[u8]) -> Result<()>;
    fn flush(&mut self) -> Result<()>;
    fn sector_count(&self) -> u64;
}

impl MapStorage for Box<dyn MapStorage> {
    fn read_at(&self, sector: u64, buf: &mut [u8]) -> Result<()> {
        (**self).read_at(sector, buf)
    }

    fn write_at(&mut self, sector: u64, buf: &[u8]) -> Result<()> {
        (**self).write_at(sector, buf)
    }

    fn flush(&mut self) -> Result<()> {
        (**self).flush()
    }

    fn sector_count(&self) -> u64 {
        (**self).sector_count()
    }
}

pub struct FileStorage {
    file: File,
    sector_count: u64,
}

impl FileStorage {
    pub fn create(path: &Path, sector_count: u64) -> Result<Self> {
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(path)
            .context(format!("Failed to open map at {}", path.display()))?;
        file.set_len(sector_count * SECTOR_SIZE as u64)
            .context("Failed to size the map")?;
        Ok(FileStorage { file, sector_count })
    }

    pub fn open(path: &Path) -> Result<Self> {
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .open(path)
            .context(format!("Failed to open map at {}", path.display()))?;
        let len = file.metadata().context("Failed to stat the map")?.len();
        Ok(FileStorage {
            file,
            sector_count: len / SECTOR_SIZE as u64,
        })
    }
}

fn check_range(sector: u64, buf: &[u8], sector_count: u64) -> Result<()> {
    if !buf.len().is_multiple_of(SECTOR_SIZE) {
        return Err(crate::ubiblk_error!(InvalidParameter {
            description: format!("{} bytes is not whole sectors", buf.len()),
        }));
    }
    let sectors = (buf.len() / SECTOR_SIZE) as u64;
    if sector
        .checked_add(sectors)
        .is_none_or(|end| end > sector_count)
    {
        return Err(crate::ubiblk_error!(InvalidParameter {
            description: format!("sectors {sector}..+{sectors} are outside the map"),
        }));
    }
    Ok(())
}

impl MapStorage for FileStorage {
    fn read_at(&self, sector: u64, buf: &mut [u8]) -> Result<()> {
        check_range(sector, buf, self.sector_count)?;
        self.file
            .read_exact_at(buf, sector * SECTOR_SIZE as u64)
            .context("Failed to read the map")
    }

    fn write_at(&mut self, sector: u64, buf: &[u8]) -> Result<()> {
        check_range(sector, buf, self.sector_count)?;
        self.file
            .write_all_at(buf, sector * SECTOR_SIZE as u64)
            .context("Failed to write the map")
    }

    fn flush(&mut self) -> Result<()> {
        self.file.sync_data().context("Failed to flush the map")
    }

    fn sector_count(&self) -> u64 {
        self.sector_count
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::NamedTempFile;

    #[test]
    fn a_file_gives_back_what_was_written_to_it() -> Result<()> {
        let tmp = NamedTempFile::new()?;
        let mut storage = FileStorage::create(tmp.path(), 8)?;
        let written = [0xABu8; SECTOR_SIZE];
        storage.write_at(3, &written)?;
        storage.flush()?;

        let reopened = FileStorage::open(tmp.path())?;
        let mut read = [0u8; SECTOR_SIZE];
        reopened.read_at(3, &mut read)?;

        assert_eq!(read, written);
        assert_eq!(reopened.sector_count(), 8);
        Ok(())
    }

    #[test]
    fn a_write_outside_the_map_is_refused() -> Result<()> {
        let tmp = NamedTempFile::new()?;
        let mut storage = FileStorage::create(tmp.path(), 2)?;
        assert!(storage.write_at(2, &[0u8; SECTOR_SIZE]).is_err());
        assert!(storage.write_at(0, &[0u8; SECTOR_SIZE + 1]).is_err());
        assert!(storage.write_at(u64::MAX, &[0u8; SECTOR_SIZE]).is_err());
        Ok(())
    }
}
