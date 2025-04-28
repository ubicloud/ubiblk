use super::{BlockDevice, IoChannel, SharedBuffer};
use crate::{Error, Result};
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
    fn add_read(&mut self, sector: u64, buf: SharedBuffer, len: usize, id: usize) {
        let mut buf = buf.borrow_mut();
        let fd = self.file.as_raw_fd();
        let read_e =
            io_uring::opcode::Read::new(io_uring::types::Fd(fd), buf.as_mut_ptr(), len as u32)
                .offset(sector * 512)
                .build()
                .user_data(id as u64);
        let push_result = unsafe { self.ring.submission().push(&read_e) };
        if let Err(_) = push_result {
            self.finished_requests.push((id, false));
            return;
        }
        self.submissions += 1;
    }

    fn add_write(&mut self, sector: u64, buf: SharedBuffer, len: usize, id: usize) {
        let buf = buf.borrow();
        let fd = self.file.as_raw_fd();
        let write_e =
            io_uring::opcode::Write::new(io_uring::types::Fd(fd), buf.as_ptr(), len as u32)
                .offset(sector * 512)
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
    size: u64,
    queue_size: usize,
}

impl BlockDevice for UringBlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>> {
        let channel = UringIoChannel::new(self.path.to_str().unwrap(), self.queue_size)?;
        Ok(Box::new(channel))
    }

    fn size(&self) -> u64 {
        self.size
    }
}

impl UringBlockDevice {
    pub fn new(path: PathBuf, queue_size: usize) -> Result<Box<Self>> {
        match std::fs::metadata(&path) {
            Ok(metadata) => {
                let size = metadata.len();
                Ok(Box::new(UringBlockDevice {
                    path,
                    size,
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
