use super::{BlockDevice, IoChannel, SharedBuffer};
#[cfg(test)]
use crate::utils::aligned_buffer::AlignedBuf;
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
        if let Err(e) = file.read_exact(&mut buf.as_mut_slice()[..len]) {
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
        if let Err(e) = file.write_all(&buf.as_slice()[..len]) {
            error!("Error writing to sector {}: {}", sector_offset, e);
            self.finished_requests.push((id, false));
            return;
        }

        self.finished_requests.push((id, true));
    }

    fn add_flush(&mut self, id: usize) {
        let mut file = self.file.lock().unwrap();
        if file.flush().is_err() {
            self.finished_requests.push((id, false));
            return;
        }
        if file.sync_all().is_err() {
            self.finished_requests.push((id, false));
            return;
        }
        self.finished_requests.push((id, true));
    }

    fn submit(&mut self) -> Result<()> {
        Ok(())
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        std::mem::take(&mut self.finished_requests)
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
                    error!(
                        "File {} size is not a multiple of sector size",
                        path.display()
                    );
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
    use std::os::fd::FromRawFd;
    use std::{cell::RefCell, rc::Rc};

    use tempfile::NamedTempFile;

    use super::*;

    #[test]
    // Verify basic read and write operations succeed on a read/write device.
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
        let write_buf = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        write_buf
            .borrow_mut()
            .as_mut_slice()
            .copy_from_slice(&pattern);
        chan.add_write(0, 1, write_buf.clone(), 1);
        chan.submit()?;
        let result = chan.poll();
        assert_eq!(result, vec![(1, true)]);

        // Read it back
        let read_buf = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        chan.add_read(0, 1, read_buf.clone(), 2);
        chan.submit()?;
        let result = chan.poll();
        assert_eq!(result, vec![(2, true)]);
        assert_eq!(read_buf.borrow().as_slice(), pattern.as_slice());

        Ok(())
    }

    #[test]
    // Ensure writes fail when the device is opened read-only.
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
        let write_buf = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        write_buf
            .borrow_mut()
            .as_mut_slice()
            .copy_from_slice(&pattern);
        chan.add_write(0, 1, write_buf.clone(), 1);
        chan.submit()?;
        let result = chan.poll();
        assert_eq!(result, vec![(1, false)]);

        Ok(())
    }

    #[test]
    // Opening a non-existent file for a channel should fail.
    fn sync_io_channel_new_fail() {
        let path = Path::new("/this/does/not/exist");
        assert!(SyncIoChannel::new(path, false).is_err());
    }

    #[test]
    // Creating a device with a size not aligned to sectors should error.
    fn device_new_invalid_size() {
        let tmpfile = NamedTempFile::new().unwrap();
        tmpfile.as_file().write_all(&[0u8; 1]).unwrap();
        let path = tmpfile.path().to_path_buf();
        assert!(matches!(
            SyncBlockDevice::new(path, false),
            Err(VhostUserBlockError::InvalidParameter { .. })
        ));
    }

    #[test]
    // Trigger error paths for out-of-bounds reads and writes.
    fn read_and_write_error_paths() -> Result<()> {
        let tmpfile = NamedTempFile::new().map_err(|e| {
            error!("Failed to create temporary file: {}", e);
            VhostUserBlockError::IoError { source: e }
        })?;
        tmpfile.as_file().set_len(SECTOR_SIZE as u64).unwrap();

        let path = tmpfile.path();
        let mut chan = SyncIoChannel::new(path, false)?;

        let read_buf = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        chan.add_read(1, 1, read_buf.clone(), 1);
        chan.submit()?;
        assert_eq!(chan.poll(), vec![(1, false)]);

        let mut ro_chan = SyncIoChannel::new(path, true)?;
        let write_buf: SharedBuffer = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        ro_chan.add_write(0, 1, write_buf.clone(), 2);
        ro_chan.submit()?;
        assert_eq!(ro_chan.poll(), vec![(2, false)]);
        Ok(())
    }

    #[test]
    // Use a pipe to provoke seek failures during read/write operations.
    // std::mem::forget prevents the pipe file descriptor from being closed twice.
    fn seek_error_paths() -> Result<()> {
        let mut fds = [0; 2];
        unsafe { libc::pipe(fds.as_mut_ptr()) };
        let file = unsafe { File::from_raw_fd(fds[1]) };
        let _r = unsafe { File::from_raw_fd(fds[0]) };
        let mut chan = SyncIoChannel {
            file: Arc::new(Mutex::new(file)),
            finished_requests: Vec::new(),
        };
        let buf: SharedBuffer = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        chan.add_read(0, 1, buf.clone(), 1);
        chan.submit()?;
        assert_eq!(chan.poll(), vec![(1, false)]);
        chan.add_write(0, 1, buf.clone(), 2);
        chan.submit()?;
        assert_eq!(chan.poll(), vec![(2, false)]);
        std::mem::forget(chan);
        Ok(())
    }

    #[test]
    // Test successful flush operations and that the channel never reports busy.
    fn flush_and_busy() -> Result<()> {
        let tmpfile = NamedTempFile::new().map_err(|e| {
            error!("Failed to create temporary file: {}", e);
            VhostUserBlockError::IoError { source: e }
        })?;
        let path = tmpfile.path();
        let mut chan = SyncIoChannel::new(path, false)?;
        assert!(!chan.busy());
        chan.add_flush(1);
        chan.submit()?;
        assert_eq!(chan.poll(), vec![(1, true)]);

        if let Ok(mut err_chan) = SyncIoChannel::new(Path::new("/dev/full"), false) {
            err_chan.add_flush(2);
            err_chan.submit()?;
            assert_eq!(err_chan.poll(), vec![(2, false)]);
        }
        Ok(())
    }

    #[test]
    // Validate error handling on device creation and sector count reporting.
    fn block_device_error_and_sector_count() {
        let path = PathBuf::from("/no/such/file");
        assert!(matches!(
            SyncBlockDevice::new(path, false),
            Err(VhostUserBlockError::IoError { .. })
        ));

        let tmpfile = NamedTempFile::new().unwrap();
        tmpfile.as_file().set_len((SECTOR_SIZE * 2) as u64).unwrap();
        let device = SyncBlockDevice::new(tmpfile.path().to_path_buf(), false).unwrap();
        assert_eq!(device.sector_count(), 2);
    }
}
