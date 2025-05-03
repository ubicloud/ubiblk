use super::{BlockDevice, IoChannel, SharedBuffer};
use crate::{vhost_backend::SECTOR_SIZE, Error, Result};
use io_uring::IoUring;
use log::error;
use std::{
    fs::{File, OpenOptions},
    os::fd::AsRawFd,
    path::PathBuf,
};

struct UringIoChannel {
    file: File,
    ring: IoUring,
    submissions: u64,
    completions: u64,
    finished_requests: Vec<(usize, bool)>,
}

impl UringIoChannel {
    fn new(path: &str, queue_size: usize) -> Result<Self> {
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .open(path)
            .map_err(|e| {
                error!("Failed to open file {}: {}", path, e);
                Error::IoError
            })?;
        let io_uring_entries: u32 = queue_size.try_into().map_err(|_| {
            error!("Invalid queue size: {}", queue_size);
            Error::InvalidParameter
        })?;
        let ring = IoUring::new(io_uring_entries).map_err(|e| {
            error!("Failed to create io_uring: {}", e);
            Error::IoError
        })?;
        Ok(UringIoChannel {
            file,
            ring,
            submissions: 0,
            completions: 0,
            finished_requests: Vec::new(),
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
        if let Err(_) = push_result {
            self.finished_requests.push((id, false));
            return;
        }
        self.submissions += 1;
    }

    fn add_write(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        let buf = buf.borrow();
        let fd = self.file.as_raw_fd();
        let len = sector_count * SECTOR_SIZE as u32;
        let write_e =
            io_uring::opcode::Write::new(io_uring::types::Fd(fd), buf.as_ptr(), len as u32)
                .offset(sector_offset * SECTOR_SIZE as u64)
                .build()
                .user_data(id as u64);
        let push_result = unsafe { self.ring.submission().push(&write_e) };
        if let Err(_) = push_result {
            self.finished_requests.push((id, false));
            return;
        }
        self.submissions += 1;
    }

    fn add_flush(&mut self, id: usize) {
        let fd = self.file.as_raw_fd();
        let flush_e = io_uring::opcode::Fsync::new(io_uring::types::Fd(fd))
            .build()
            .user_data(id as u64);
        let push_result = unsafe { self.ring.submission().push(&flush_e) };
        if let Err(_) = push_result {
            self.finished_requests.push((id, false));
            return;
        }
        self.submissions += 1;
    }

    fn submit(&mut self) -> Result<()> {
        if let Err(_) = self.ring.submit() {
            error!("Failed to submit IO request");
            return Err(Error::IoError);
        }
        Ok(())
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        let mut finished_requests = self.finished_requests.clone();
        self.finished_requests.clear();
        loop {
            let maybe_entry = { self.ring.completion().next() };
            match maybe_entry {
                Some(entry) => {
                    let result = entry.result();
                    let id = entry.user_data();
                    if result < 0 {
                        finished_requests.push((id as usize, false));
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

    fn busy(&mut self) -> bool {
        self.submissions > self.completions
    }
}

pub struct UringBlockDevice {
    path: PathBuf,
    sector_count: u64,
    queue_size: usize,
}

impl BlockDevice for UringBlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>> {
        let channel = UringIoChannel::new(self.path.to_str().unwrap(), self.queue_size)?;
        Ok(Box::new(channel))
    }

    fn sector_count(&self) -> u64 {
        self.sector_count
    }
}

impl UringBlockDevice {
    pub fn new(path: PathBuf, queue_size: usize) -> Result<Box<Self>> {
        match std::fs::metadata(&path) {
            Ok(metadata) => {
                let size = metadata.len();
                if size % SECTOR_SIZE as u64 != 0 {
                    error!("File size is not a multiple of sector size");
                    return Err(Error::InvalidParameter);
                }
                let sector_count = size / SECTOR_SIZE as u64;
                Ok(Box::new(UringBlockDevice {
                    path,
                    sector_count,
                    queue_size,
                }))
            }
            Err(e) => {
                error!("Failed to get metadata for {}: {}", path.display(), e);
                Err(Error::IoError)
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

    #[test]
    fn create_channel_and_basic_io() -> Result<()> {
        let tmpfile = NamedTempFile::new().map_err(|e| {
            error!("Failed to create temporary file: {}", e);
            Error::IoError
        })?;
        let path = tmpfile.path().to_owned();
        let block_dev = UringBlockDevice::new(path.clone(), 8)?;
        let mut chan = block_dev.create_channel()?;

        // Write sector 0
        let pattern = vec![0xABu8; SECTOR_SIZE];
        let write_buf = Rc::new(RefCell::new(pattern.clone()));
        chan.add_write(0, 1, write_buf.clone(), 1);
        chan.submit()?;
        let result = spin_until_complete(&mut chan);
        assert_eq!(result, vec![(1, true)]);

        // Read it back
        let read_buf = Rc::new(RefCell::new(vec![0u8; SECTOR_SIZE]));
        chan.add_read(0, 1, read_buf.clone(), 2);
        chan.submit()?;
        let result = spin_until_complete(&mut chan);
        assert_eq!(result, vec![(2, true)]);
        assert_eq!(*read_buf.borrow(), pattern);

        Ok(())
    }
}
