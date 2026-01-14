use super::{BlockDevice, IoChannel, SharedBuffer};
use crate::vhost_backend::SECTOR_SIZE;
use crate::{Result, UbiblkError};
use log::error;
use std::fs::{File, OpenOptions};
use std::io::Write;
use std::os::unix::fs::{FileExt, OpenOptionsExt};
use std::path::{Path, PathBuf};

#[cfg(test)]
use nix::unistd::pipe;

struct SyncIoChannel {
    file: File,
    finished_requests: Vec<(usize, bool)>,
}

impl SyncIoChannel {
    fn new(path: &Path, readonly: bool, direct_io: bool, sync: bool) -> Result<Self> {
        let mut opts = OpenOptions::new();
        opts.read(true).write(!readonly);

        let mut flags = 0;
        if direct_io {
            flags |= libc::O_DIRECT;
        }
        if sync {
            flags |= libc::O_SYNC;
        }
        if flags != 0 {
            opts.custom_flags(flags);
        }

        let file = opts.open(path).map_err(|e| {
            error!("Failed to open file {}: {}", path.display(), e);
            UbiblkError::IoError { source: e }
        })?;
        Ok(SyncIoChannel {
            file,
            finished_requests: Vec::new(),
        })
    }
}

impl IoChannel for SyncIoChannel {
    fn add_read(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        let mut buf = buf.borrow_mut();
        let len = sector_count as usize * SECTOR_SIZE;
        let offset = sector_offset * SECTOR_SIZE as u64;

        if let Err(e) = self
            .file
            .read_exact_at(&mut buf.as_mut_slice()[..len], offset)
        {
            error!("Error reading from sector {sector_offset}: {e}");
            self.finished_requests.push((id, false));
            return;
        }

        self.finished_requests.push((id, true));
    }

    fn add_write(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        let buf = buf.borrow();
        let len = sector_count as usize * SECTOR_SIZE;
        let offset = sector_offset * SECTOR_SIZE as u64;

        if let Err(e) = self.file.write_all_at(&buf.as_slice()[..len], offset) {
            error!("Error writing to sector {sector_offset}: {e}");
            self.finished_requests.push((id, false));
            return;
        }

        self.finished_requests.push((id, true));
    }

    fn add_flush(&mut self, id: usize) {
        if let Err(e) = self.file.flush() {
            error!("Error flushing file: {e}");
            self.finished_requests.push((id, false));
            return;
        }
        if let Err(e) = self.file.sync_all() {
            error!("Error syncing file: {e}");
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

    fn busy(&self) -> bool {
        !self.finished_requests.is_empty()
    }
}

pub struct SyncBlockDevice {
    path: PathBuf,
    sector_count: u64,
    readonly: bool,
    direct_io: bool,
    sync: bool,
}

impl BlockDevice for SyncBlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>> {
        let channel = SyncIoChannel::new(&self.path, self.readonly, self.direct_io, self.sync)?;
        Ok(Box::new(channel))
    }

    fn sector_count(&self) -> u64 {
        self.sector_count
    }

    fn clone(&self) -> Box<dyn BlockDevice> {
        Box::new(SyncBlockDevice {
            path: self.path.clone(),
            sector_count: self.sector_count,
            readonly: self.readonly,
            direct_io: self.direct_io,
            sync: self.sync,
        })
    }
}

impl SyncBlockDevice {
    pub fn new(path: PathBuf, readonly: bool, direct_io: bool, sync: bool) -> Result<Box<Self>> {
        match std::fs::metadata(&path) {
            Ok(metadata) => {
                let size = metadata.len();
                if size % SECTOR_SIZE as u64 != 0 {
                    error!(
                        "File {} size is not a multiple of sector size",
                        path.display()
                    );
                    return Err(UbiblkError::InvalidParameter {
                        description: "File size is not a multiple of sector size".to_string(),
                    });
                }
                let sector_count = size / SECTOR_SIZE as u64;
                Ok(Box::new(SyncBlockDevice {
                    path,
                    sector_count,
                    readonly,
                    direct_io,
                    sync,
                }))
            }
            Err(e) => {
                error!("Failed to get metadata for file {}: {}", path.display(), e);
                Err(UbiblkError::IoError { source: e })
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::io::Write;

    use tempfile::NamedTempFile;

    use crate::block_device::shared_buffer;

    use super::*;

    #[test]
    // Verify basic read and write operations succeed on a read/write device.
    fn create_channel_and_basic_io() -> Result<()> {
        let tmpfile = NamedTempFile::new().map_err(|e| {
            error!("Failed to create temporary file: {e}");
            UbiblkError::IoError { source: e }
        })?;

        let path = tmpfile.path().to_path_buf();
        let device = SyncBlockDevice::new(path.clone(), false, false, false)?;

        let mut chan = device.create_channel()?;

        // Write sector 0
        let pattern = vec![0xABu8; SECTOR_SIZE];
        let write_buf = shared_buffer(SECTOR_SIZE);
        write_buf
            .borrow_mut()
            .as_mut_slice()
            .copy_from_slice(&pattern);
        chan.add_write(0, 1, write_buf.clone(), 1);
        chan.submit()?;
        let result = chan.poll();
        assert_eq!(result, vec![(1, true)]);

        // Read it back
        let read_buf = shared_buffer(SECTOR_SIZE);
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
            error!("Failed to create temporary file: {e}");
            UbiblkError::IoError { source: e }
        })?;

        let path = tmpfile.path().to_path_buf();
        let device = SyncBlockDevice::new(path.clone(), true, false, false)?;

        let mut chan = device.create_channel()?;

        // Write sector 0
        let pattern = vec![0xABu8; SECTOR_SIZE];
        let write_buf = shared_buffer(SECTOR_SIZE);
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
        assert!(SyncIoChannel::new(path, false, false, false).is_err());
    }

    #[test]
    // Creating a device with a size not aligned to sectors should error.
    fn device_new_invalid_size() {
        let tmpfile = NamedTempFile::new().unwrap();
        tmpfile.as_file().write_all(&[0u8; 1]).unwrap();
        let path = tmpfile.path().to_path_buf();
        assert!(matches!(
            SyncBlockDevice::new(path, false, false, false),
            Err(UbiblkError::InvalidParameter { .. })
        ));
    }

    #[test]
    // Trigger error paths for out-of-bounds reads and writes.
    fn read_and_write_error_paths() -> Result<()> {
        let tmpfile = NamedTempFile::new().map_err(|e| {
            error!("Failed to create temporary file: {e}");
            UbiblkError::IoError { source: e }
        })?;
        tmpfile.as_file().set_len(SECTOR_SIZE as u64).unwrap();

        let path = tmpfile.path();
        let mut chan = SyncIoChannel::new(path, false, false, false)?;

        let read_buf = shared_buffer(SECTOR_SIZE);
        chan.add_read(1, 1, read_buf.clone(), 1);
        chan.submit()?;
        assert_eq!(chan.poll(), vec![(1, false)]);

        let mut ro_chan = SyncIoChannel::new(path, true, false, false)?;
        let write_buf: SharedBuffer = shared_buffer(SECTOR_SIZE);
        ro_chan.add_write(0, 1, write_buf.clone(), 2);
        ro_chan.submit()?;
        assert_eq!(ro_chan.poll(), vec![(2, false)]);
        Ok(())
    }

    #[test]
    // Use a pipe to provoke seek failures during read/write operations.
    // std::mem::forget prevents the pipe file descriptor from being closed twice.
    fn seek_error_paths() -> Result<()> {
        let (read_fd, write_fd) = pipe().map_err(|e| {
            error!("Failed to create pipe: {e}");
            UbiblkError::IoError {
                source: std::io::Error::from(e),
            }
        })?;
        let file = File::from(write_fd);
        let _r = File::from(read_fd);
        let mut chan = SyncIoChannel {
            file,
            finished_requests: Vec::new(),
        };
        let buf: SharedBuffer = shared_buffer(SECTOR_SIZE);
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
            error!("Failed to create temporary file: {e}");
            UbiblkError::IoError { source: e }
        })?;
        let path = tmpfile.path();
        let mut chan = SyncIoChannel::new(path, false, false, false)?;
        assert!(!chan.busy());
        chan.add_flush(1);
        chan.submit()?;
        assert_eq!(chan.poll(), vec![(1, true)]);

        if let Ok(mut err_chan) = SyncIoChannel::new(Path::new("/dev/full"), false, false, false) {
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
            SyncBlockDevice::new(path, false, false, false),
            Err(UbiblkError::IoError { .. })
        ));

        let tmpfile = NamedTempFile::new().unwrap();
        tmpfile.as_file().set_len((SECTOR_SIZE * 2) as u64).unwrap();
        let device =
            SyncBlockDevice::new(tmpfile.path().to_path_buf(), false, false, false).unwrap();
        assert_eq!(device.sector_count(), 2);
    }
    #[test]
    // Verify that direct I/O works for basic read and write operations.
    fn direct_io_basic_io() -> Result<()> {
        let tmpfile = NamedTempFile::new().map_err(|e| {
            error!("Failed to create temporary file: {e}");
            UbiblkError::IoError { source: e }
        })?;
        let path = tmpfile.path().to_owned();
        let device = SyncBlockDevice::new(path.clone(), false, true, false)?;
        let mut chan = device.create_channel()?;

        let pattern = vec![0xACu8; SECTOR_SIZE];
        let write_buf = shared_buffer(SECTOR_SIZE);
        write_buf
            .borrow_mut()
            .as_mut_slice()
            .copy_from_slice(&pattern);
        chan.add_write(0, 1, write_buf.clone(), 1);
        chan.submit()?;
        let result = chan.poll();
        assert_eq!(result, vec![(1, true)]);

        let read_buf = shared_buffer(SECTOR_SIZE);
        chan.add_read(0, 1, read_buf.clone(), 2);
        chan.submit()?;
        let result = chan.poll();
        assert_eq!(result, vec![(2, true)]);
        assert_eq!(read_buf.borrow().as_slice(), pattern.as_slice());

        Ok(())
    }

    #[test]
    // When opened with O_SYNC, flush requests should complete without issuing
    // an fsync operation (or rather, the write itself was sync, so flush is fine).
    // For SyncIoChannel, flush calls file.sync_all() anyway, but we want to ensure
    // the flag is accepted and doesn't cause errors.
    fn sync_flush_noop() -> Result<()> {
        let tmpfile = NamedTempFile::new().map_err(|e| {
            error!("Failed to create temporary file: {e}");
            UbiblkError::IoError { source: e }
        })?;
        let path = tmpfile.path().to_owned();
        let device = SyncBlockDevice::new(path.clone(), false, false, true)?;
        let mut chan = device.create_channel()?;

        chan.add_flush(1);
        chan.submit()?;
        let result = chan.poll();
        assert_eq!(result, vec![(1, true)]);
        Ok(())
    }

    #[test]
    fn test_clone() {
        let tmpfile = NamedTempFile::new().unwrap();
        let path = tmpfile.path().to_path_buf();
        let device = SyncBlockDevice::new(path.clone(), false, true, true).unwrap();
        let device_clone = device.clone();
        assert_eq!(device.sector_count(), device_clone.sector_count());

        // Write to the clone & read from the original to verify they access the
        // same file.
        let mut chan_clone = device_clone.create_channel().unwrap();
        let pattern = vec![0xDEu8; SECTOR_SIZE];
        let write_buf = shared_buffer(SECTOR_SIZE);
        write_buf
            .borrow_mut()
            .as_mut_slice()
            .copy_from_slice(&pattern);
        chan_clone.add_write(0, 1, write_buf.clone(), 1);
        chan_clone.submit().unwrap();
        assert_eq!(chan_clone.poll(), vec![(1, true)]);
        chan_clone.add_flush(0);
        chan_clone.submit().unwrap();
        assert_eq!(chan_clone.poll(), vec![(0, true)]);

        let mut chan = device.create_channel().unwrap();
        let read_buf = shared_buffer(SECTOR_SIZE);
        chan.add_read(0, 1, read_buf.clone(), 2);
        chan.submit().unwrap();
        assert_eq!(chan.poll(), vec![(2, true)]);
        assert_eq!(read_buf.borrow().as_slice(), pattern.as_slice());
    }
}
