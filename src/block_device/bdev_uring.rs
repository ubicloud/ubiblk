use super::{BlockDevice, IoChannel, SharedBuffer};
#[cfg(test)]
use crate::utils::aligned_buffer::AlignedBuf;
use crate::{vhost_backend::SECTOR_SIZE, Result, VhostUserBlockError};
use io_uring::IoUring;
use log::error;
use nix::errno::Errno;
use std::{
    fs::{File, OpenOptions},
    os::fd::AsRawFd,
    os::unix::fs::OpenOptionsExt,
    path::PathBuf,
};

struct UringIoChannel {
    file: File,
    ring: IoUring,
    pending: u64,
    submissions: u64,
    completions: u64,
    finished_requests: Vec<(usize, bool)>,
    sync_io: bool,
}

impl UringIoChannel {
    fn new(
        path: &str,
        queue_size: usize,
        readonly: bool,
        direct_io: bool,
        sync_io: bool,
    ) -> Result<Self> {
        let mut opts = OpenOptions::new();
        opts.read(true).write(!readonly);
        let mut flags = 0;
        if direct_io {
            flags |= libc::O_DIRECT;
        }
        if sync_io {
            flags |= libc::O_SYNC;
        }
        if flags != 0 {
            opts.custom_flags(flags);
        }
        let file = opts.open(path).map_err(|e| {
            error!("Failed to open file {path}: {e}");
            VhostUserBlockError::IoError { source: e }
        })?;
        let io_uring_entries: u32 = queue_size.try_into().map_err(|_| {
            error!("Invalid queue size: {queue_size}");
            VhostUserBlockError::InvalidParameter {
                description: "Invalid io_uring queue size".to_string(),
            }
        })?;
        let ring = IoUring::new(io_uring_entries).map_err(|e| {
            error!("Failed to create io_uring: {e}");
            VhostUserBlockError::IoError { source: e }
        })?;
        Ok(UringIoChannel {
            file,
            ring,
            pending: 0,
            submissions: 0,
            completions: 0,
            finished_requests: Vec::new(),
            sync_io,
        })
    }
}

impl IoChannel for UringIoChannel {
    fn add_read(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        let mut buf = buf.borrow_mut();
        let fd = self.file.as_raw_fd();
        let len = sector_count * SECTOR_SIZE as u32;
        let read_e = io_uring::opcode::Read::new(io_uring::types::Fd(fd), buf.as_mut_ptr(), len)
            .offset(sector_offset * SECTOR_SIZE as u64)
            .build()
            .user_data(id as u64);
        let push_result = unsafe { self.ring.submission().push(&read_e) };
        if push_result.is_err() {
            self.finished_requests.push((id, false));
            return;
        }
        self.pending += 1;
    }

    fn add_write(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        let buf = buf.borrow();
        let fd = self.file.as_raw_fd();
        let len = sector_count * SECTOR_SIZE as u32;
        let write_e = io_uring::opcode::Write::new(io_uring::types::Fd(fd), buf.as_ptr(), len)
            .offset(sector_offset * SECTOR_SIZE as u64)
            .build()
            .user_data(id as u64);
        let push_result = unsafe { self.ring.submission().push(&write_e) };
        if push_result.is_err() {
            self.finished_requests.push((id, false));
            return;
        }
        self.pending += 1;
    }

    fn add_flush(&mut self, id: usize) {
        if self.sync_io {
            self.finished_requests.push((id, true));
            return;
        }
        let fd = self.file.as_raw_fd();
        let flush_e = io_uring::opcode::Fsync::new(io_uring::types::Fd(fd))
            .build()
            .user_data(id as u64);
        let push_result = unsafe { self.ring.submission().push(&flush_e) };
        if push_result.is_err() {
            self.finished_requests.push((id, false));
            return;
        }
        self.pending += 1;
    }

    fn submit(&mut self) -> Result<()> {
        if self.pending == 0 {
            return Ok(());
        }
        self.submissions += self.pending;
        self.pending = 0;
        if let Err(e) = self.ring.submit() {
            error!("Failed to submit IO request: {e}");
            return Err(VhostUserBlockError::IoError { source: e });
        }
        Ok(())
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        let mut finished_requests = std::mem::take(&mut self.finished_requests);
        loop {
            let maybe_entry = { self.ring.completion().next() };
            match maybe_entry {
                Some(entry) => {
                    let result = entry.result();
                    let id = entry.user_data();
                    if result < 0 {
                        finished_requests.push((id as usize, false));
                        error!("IO request failed: {}", Errno::from_raw(-result));
                    } else {
                        finished_requests.push((id as usize, true));
                    }
                    self.completions += 1;
                }
                None => break,
            }
        }
        finished_requests
    }

    fn busy(&self) -> bool {
        self.submissions > self.completions
            || !self.finished_requests.is_empty()
            || self.pending > 0
    }
}

pub struct UringBlockDevice {
    path: PathBuf,
    sector_count: u64,
    queue_size: usize,
    readonly: bool,
    direct_io: bool,
    sync: bool,
}

impl BlockDevice for UringBlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>> {
        let channel = UringIoChannel::new(
            self.path.to_string_lossy().as_ref(),
            self.queue_size,
            self.readonly,
            self.direct_io,
            self.sync,
        )?;
        Ok(Box::new(channel))
    }

    fn sector_count(&self) -> u64 {
        self.sector_count
    }
}

impl UringBlockDevice {
    pub fn new(
        path: PathBuf,
        queue_size: usize,
        readonly: bool,
        direct_io: bool,
        sync: bool,
    ) -> Result<Box<Self>> {
        if !queue_size.is_power_of_two() {
            error!("Invalid queue size: {queue_size}");
            return Err(VhostUserBlockError::InvalidParameter {
                description: "queue_size must be a positive power of two".to_string(),
            });
        }
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
                Ok(Box::new(UringBlockDevice {
                    path,
                    sector_count,
                    queue_size,
                    readonly,
                    direct_io,
                    sync,
                }))
            }
            Err(e) => {
                error!("Failed to get metadata for {}: {}", path.display(), e);
                Err(VhostUserBlockError::IoError { source: e })
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use log::error;
    use std::{cell::RefCell, rc::Rc, thread::sleep, time::Duration};
    use tempfile::NamedTempFile;

    fn spin_until_complete(chan: &mut Box<dyn IoChannel>) -> Vec<(usize, bool)> {
        let mut completed = vec![];
        while chan.busy() {
            completed.extend(chan.poll());
            sleep(Duration::from_millis(10));
        }
        completed
    }

    // Verify that a channel created from a writable device can perform a
    // complete write followed by a read of the same sector.
    #[test]
    fn create_channel_and_basic_io() -> Result<()> {
        let tmpfile = NamedTempFile::new().map_err(|e| {
            error!("Failed to create temporary file: {e}");
            VhostUserBlockError::IoError { source: e }
        })?;
        let path = tmpfile.path().to_owned();
        let block_dev = UringBlockDevice::new(path.clone(), 8, false, false, false)?;
        let mut chan = block_dev.create_channel()?;

        // Write sector 0
        let pattern = vec![0xABu8; SECTOR_SIZE];
        let write_buf = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        write_buf
            .borrow_mut()
            .as_mut_slice()
            .copy_from_slice(&pattern);
        chan.add_write(0, 1, write_buf.clone(), 1);
        chan.submit()?;
        let result = spin_until_complete(&mut chan);
        assert_eq!(result, vec![(1, true)]);

        // Read it back
        let read_buf = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        chan.add_read(0, 1, read_buf.clone(), 2);
        chan.submit()?;
        let result = spin_until_complete(&mut chan);
        assert_eq!(result, vec![(2, true)]);
        assert_eq!(read_buf.borrow().as_slice(), pattern.as_slice());

        Ok(())
    }

    // When the block device is opened read only, read requests succeed while
    // writes are rejected.
    #[test]
    fn create_channel_and_basic_io_readonly() -> Result<()> {
        let tmpfile = NamedTempFile::new().map_err(|e| {
            error!("Failed to create temporary file: {e}");
            VhostUserBlockError::IoError { source: e }
        })?;
        let path = tmpfile.path().to_owned();
        let block_dev = UringBlockDevice::new(path.clone(), 8, true, false, false)?;
        let mut chan = block_dev.create_channel()?;

        // Read sector 0
        let read_buf = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        chan.add_read(0, 1, read_buf.clone(), 2);
        chan.submit()?;
        let result = spin_until_complete(&mut chan);
        assert_eq!(result, vec![(2, true)]);

        // Attempt to write should fail
        let write_buf = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        write_buf.borrow_mut().as_mut_slice().fill(0xABu8);
        chan.add_write(0, 1, write_buf.clone(), 1);
        chan.submit()?;
        let result = spin_until_complete(&mut chan);
        assert_eq!(result, vec![(1, false)]);

        Ok(())
    }

    // Creating a device backed by a file whose size is not a multiple of the
    // sector size should fail.
    #[test]
    fn new_with_unaligned_size_fails() -> Result<()> {
        let mut tmpfile = NamedTempFile::new().map_err(|e| {
            error!("Failed to create temporary file: {e}");
            VhostUserBlockError::IoError { source: e }
        })?;
        tmpfile
            .as_file_mut()
            .set_len(SECTOR_SIZE as u64 + 1)
            .map_err(|e| {
                error!("Failed to set temporary file size: {e}");
                VhostUserBlockError::IoError { source: e }
            })?;
        let path = tmpfile.path().to_owned();
        let result = UringBlockDevice::new(path, 8, false, false, false);
        assert!(result.is_err());
        Ok(())
    }

    // Creating a device with a path that does not exist should return an error.
    #[test]
    fn new_invalid_path_fails() -> Result<()> {
        let mut path = std::env::temp_dir();
        path.push("ubiblk_nonexistent_file");
        let result = UringBlockDevice::new(path, 8, false, false, false);
        assert!(result.is_err());
        Ok(())
    }

    // Providing a queue size that is not a positive power of two should fail.
    #[test]
    fn new_invalid_queue_size_fails() -> Result<()> {
        let tmpfile = NamedTempFile::new().map_err(|e| {
            error!("Failed to create temporary file: {e}");
            VhostUserBlockError::IoError { source: e }
        })?;
        let path = tmpfile.path().to_owned();
        let result = UringBlockDevice::new(path, 3, false, false, false);
        assert!(matches!(
            result,
            Err(VhostUserBlockError::InvalidParameter { .. })
        ));
        Ok(())
    }

    // Queue size zero should also be rejected.
    #[test]
    fn new_zero_queue_size_fails() -> Result<()> {
        let tmpfile = NamedTempFile::new().map_err(|e| {
            error!("Failed to create temporary file: {e}");
            VhostUserBlockError::IoError { source: e }
        })?;
        let path = tmpfile.path().to_owned();
        let result = UringBlockDevice::new(path, 0, false, false, false);
        assert!(matches!(
            result,
            Err(VhostUserBlockError::InvalidParameter { .. })
        ));
        Ok(())
    }

    // Verify that `busy` reports queued IO and that a flush request is handled.
    #[test]
    fn busy_and_flush() -> Result<()> {
        let tmpfile = NamedTempFile::new().map_err(|e| {
            error!("Failed to create temporary file: {e}");
            VhostUserBlockError::IoError { source: e }
        })?;
        let path = tmpfile.path().to_owned();
        let block_dev = UringBlockDevice::new(path.clone(), 8, false, false, false)?;
        let mut chan = block_dev.create_channel()?;

        // Queue a write followed by a flush and ensure busy() reflects it.
        let write_buf = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        write_buf.borrow_mut().as_mut_slice().fill(0xCDu8);
        chan.add_write(0, 1, write_buf.clone(), 1);
        chan.add_flush(2);
        assert!(chan.busy());
        chan.submit()?;
        assert!(chan.busy());
        let result = spin_until_complete(&mut chan);
        assert_eq!(result.len(), 2);
        assert!(!chan.busy());
        Ok(())
    }

    // When opened with O_SYNC, flush requests should complete without issuing
    // an fsync operation.
    #[test]
    fn sync_flush_noop() -> Result<()> {
        let tmpfile = NamedTempFile::new().map_err(|e| {
            error!("Failed to create temporary file: {e}");
            VhostUserBlockError::IoError { source: e }
        })?;
        let path = tmpfile.path().to_owned();
        let block_dev = UringBlockDevice::new(path.clone(), 8, false, false, true)?;
        let mut chan = block_dev.create_channel()?;

        chan.add_flush(1);
        assert!(chan.busy());
        chan.submit()?;
        let result = spin_until_complete(&mut chan);
        assert_eq!(result, vec![(1, true)]);
        Ok(())
    }

    // When the submission queue is full, additional requests are rejected and
    // reported as failed.
    #[test]
    fn queue_overflow() -> Result<()> {
        let tmpfile = NamedTempFile::new().map_err(|e| {
            error!("Failed to create temporary file: {e}");
            VhostUserBlockError::IoError { source: e }
        })?;
        let path = tmpfile.path().to_owned();
        // Queue size of one allows only a single in-flight request.
        let block_dev = UringBlockDevice::new(path.clone(), 1, false, false, false)?;
        let mut chan = block_dev.create_channel()?;

        let write_buf1 = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        write_buf1.borrow_mut().as_mut_slice().fill(0xAAu8);
        chan.add_write(0, 1, write_buf1.clone(), 1);
        // Second request should fail to queue.
        let write_buf2 = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        write_buf2.borrow_mut().as_mut_slice().fill(0xBBu8);
        chan.add_write(1, 1, write_buf2.clone(), 2);
        chan.submit()?;
        let result = spin_until_complete(&mut chan);
        assert!(result.contains(&(1, true)));
        assert!(result.contains(&(2, false)));
        Ok(())
    }

    // When there are failed submissions that haven't been reported yet, busy()
    // should still return true so the caller knows to poll for them.
    #[test]
    fn busy_reports_finished_requests() -> Result<()> {
        let tmpfile = NamedTempFile::new().map_err(|e| {
            error!("Failed to create temporary file: {e}");
            VhostUserBlockError::IoError { source: e }
        })?;
        let path = tmpfile.path().to_owned();
        let mut chan = UringIoChannel::new(path.to_str().unwrap(), 8, false, false, false)?;

        assert!(!chan.busy());

        chan.finished_requests.push((1, false));
        assert!(chan.busy());

        let result = chan.poll();
        assert_eq!(result, vec![(1, false)]);
        assert!(!chan.busy());
        Ok(())
    }

    // Verify that direct I/O works for basic read and write operations.
    #[test]
    fn direct_io_basic_io() -> Result<()> {
        let tmpfile = NamedTempFile::new().map_err(|e| {
            error!("Failed to create temporary file: {e}");
            VhostUserBlockError::IoError { source: e }
        })?;
        let path = tmpfile.path().to_owned();
        let block_dev = UringBlockDevice::new(path.clone(), 8, false, true, false)?;
        let mut chan = block_dev.create_channel()?;

        let pattern = vec![0xACu8; SECTOR_SIZE];
        let write_buf = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        write_buf
            .borrow_mut()
            .as_mut_slice()
            .copy_from_slice(&pattern);
        chan.add_write(0, 1, write_buf.clone(), 1);
        chan.submit()?;
        let result = spin_until_complete(&mut chan);
        assert_eq!(result, vec![(1, true)]);

        let read_buf = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        chan.add_read(0, 1, read_buf.clone(), 2);
        chan.submit()?;
        let result = spin_until_complete(&mut chan);
        assert_eq!(result, vec![(2, true)]);
        assert_eq!(read_buf.borrow().as_slice(), pattern.as_slice());

        Ok(())
    }

    // Ensure queue overflow handling also works when direct I/O is enabled.
    #[test]
    fn direct_io_queue_overflow() -> Result<()> {
        let tmpfile = NamedTempFile::new().map_err(|e| {
            error!("Failed to create temporary file: {e}");
            VhostUserBlockError::IoError { source: e }
        })?;
        let path = tmpfile.path().to_owned();
        let block_dev = UringBlockDevice::new(path.clone(), 1, false, true, false)?;
        let mut chan = block_dev.create_channel()?;

        let write_buf1 = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        write_buf1.borrow_mut().as_mut_slice().fill(0xAAu8);
        chan.add_write(0, 1, write_buf1.clone(), 1);

        let write_buf2 = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        write_buf2.borrow_mut().as_mut_slice().fill(0xBBu8);
        chan.add_write(1, 1, write_buf2.clone(), 2);
        chan.submit()?;
        let result = spin_until_complete(&mut chan);
        assert!(result.contains(&(1, true)));
        assert!(result.contains(&(2, false)));
        Ok(())
    }
}
