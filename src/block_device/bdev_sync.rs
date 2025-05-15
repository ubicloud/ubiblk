use super::{BlockDevice, IoChannel, SharedBuffer};
use crate::vhost_backend::SECTOR_SIZE;
use crate::{Result, VhostUserBlockError};
use log::error;
use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

struct SyncIoChannel {
    file: Arc<Mutex<File>>,
    finished_requests: Vec<(usize, bool)>,
}

impl SyncIoChannel {
    fn new(path: &Path, readonly: bool) -> Result<Self> {
        let file = OpenOptions::new()
            .read(true)
            .write(!readonly)
            .open(path)
            .map_err(|e| {
                error!("Failed to open file {}: {}", path.display(), e);
                VhostUserBlockError::IoError { source: e }
            })?;
        Ok(SyncIoChannel {
            file: Arc::new(Mutex::new(file)),
            finished_requests: Vec::new(),
        })
    }
}

impl IoChannel for SyncIoChannel {
    fn add_read(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        let mut buf = buf.borrow_mut();
        let mut file = self.file.lock().unwrap();
        let len = sector_count as usize * SECTOR_SIZE;
        if let Err(e) = file.seek(SeekFrom::Start(sector_offset * SECTOR_SIZE as u64)) {
            error!("Error seeking to sector {}: {}", sector_offset, e);
            self.finished_requests.push((id, false));
            return;
        }
        if let Err(e) = file.read_exact(&mut buf[..len]) {
            error!("Error reading from sector {}: {}", sector_offset, e);
            self.finished_requests.push((id, false));
            return;
        }

        self.finished_requests.push((id, true));
    }

    fn add_write(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        let buf = buf.borrow();
        let mut file = self.file.lock().unwrap();
        let len = sector_count as usize * SECTOR_SIZE;

        if let Err(e) = file.seek(SeekFrom::Start(sector_offset * SECTOR_SIZE as u64)) {
            error!("Error seeking to sector {}: {}", sector_offset, e);
            self.finished_requests.push((id, false));
            return;
        }
        if let Err(e) = file.write_all(&buf[..len]) {
            error!("Error writing to sector {}: {}", sector_offset, e);
            self.finished_requests.push((id, false));
            return;
        }

        self.finished_requests.push((id, true));
    }

    fn add_flush(&mut self, id: usize) {
        let mut file = self.file.lock().unwrap();
        if let Err(_) = file.flush() {
            self.finished_requests.push((id, false));
            return;
        }
        if let Err(_) = file.sync_all() {
            self.finished_requests.push((id, false));
            return;
        }
        self.finished_requests.push((id, true));
    }

    fn submit(&mut self) -> Result<()> {
        Ok(())
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        let finished_requests = self.finished_requests.clone();
        self.finished_requests.clear();
        finished_requests
    }

    fn busy(&mut self) -> bool {
        false
    }
}

pub struct SyncBlockDevice {
    path: PathBuf,
    sector_count: u64,
    readonly: bool,
}

impl BlockDevice for SyncBlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>> {
        let channel = SyncIoChannel::new(&self.path, self.readonly)?;
        Ok(Box::new(channel))
    }

    fn sector_count(&self) -> u64 {
        self.sector_count
    }
}

impl SyncBlockDevice {
    pub fn new(path: PathBuf, readonly: bool) -> Result<Box<Self>> {
        match std::fs::metadata(&path) {
            Ok(metadata) => {
                let size = metadata.len();
                if size % SECTOR_SIZE as u64 != 0 {
                    error!("File size is not a multiple of sector size");
                    return Err(VhostUserBlockError::InvalidParameter {
                        description: "File size is not a multiple of sector size".to_string(),
                    });
                }
                let sector_count = size / SECTOR_SIZE as u64;
                Ok(Box::new(SyncBlockDevice {
                    path,
                    sector_count,
                    readonly,
                }))
            }
            Err(e) => {
                error!("Failed to get metadata for file {}: {}", path.display(), e);
                Err(VhostUserBlockError::IoError { source: e })
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{cell::RefCell, rc::Rc};

    use tempfile::NamedTempFile;

    use super::*;

    #[test]
    fn create_channel_and_basic_io() -> Result<()> {
        let tmpfile = NamedTempFile::new().map_err(|e| {
            error!("Failed to create temporary file: {}", e);
            VhostUserBlockError::IoError { source: e }
        })?;

        let path = tmpfile.path().to_path_buf();
        let device = SyncBlockDevice::new(path.clone(), false)?;

        let mut chan = device.create_channel()?;

        // Write sector 0
        let pattern = vec![0xABu8; SECTOR_SIZE];
        let write_buf = Rc::new(RefCell::new(pattern.clone()));
        chan.add_write(0, 1, write_buf.clone(), 1);
        chan.submit()?;
        let result = chan.poll();
        assert_eq!(result, vec![(1, true)]);

        // Read it back
        let read_buf = Rc::new(RefCell::new(vec![0u8; SECTOR_SIZE]));
        chan.add_read(0, 1, read_buf.clone(), 2);
        chan.submit()?;
        let result = chan.poll();
        assert_eq!(result, vec![(2, true)]);
        assert_eq!(*read_buf.borrow(), pattern);

        Ok(())
    }

    #[test]
    fn create_channel_and_basic_io_readonly() -> Result<()> {
        let tmpfile = NamedTempFile::new().map_err(|e| {
            error!("Failed to create temporary file: {}", e);
            VhostUserBlockError::IoError { source: e }
        })?;

        let path = tmpfile.path().to_path_buf();
        let device = SyncBlockDevice::new(path.clone(), true)?;

        let mut chan = device.create_channel()?;

        // Write sector 0
        let pattern = vec![0xABu8; SECTOR_SIZE];
        let write_buf = Rc::new(RefCell::new(pattern.clone()));
        chan.add_write(0, 1, write_buf.clone(), 1);
        chan.submit()?;
        let result = chan.poll();
        assert_eq!(result, vec![(1, false)]);

        Ok(())
    }
}
