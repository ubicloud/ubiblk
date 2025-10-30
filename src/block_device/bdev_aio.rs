use super::{BlockDevice, IoChannel, SharedBuffer};
#[cfg(test)]
use crate::utils::aligned_buffer::AlignedBuf;
use crate::{vhost_backend::SECTOR_SIZE, Result, VhostUserBlockError};
use log::error;
use nix::errno::Errno;
use std::fs::{File, OpenOptions};
use std::os::fd::AsRawFd;
use std::path::{Path, PathBuf};
#[cfg(test)]
use tempfile::NamedTempFile;

struct QueuedRequest {
    sector_offset: u64,
    sector_count: u32,
    buffer: Option<SharedBuffer>,
    id: usize,
    operation: Operation,
}

#[derive(Clone, Copy)]
enum Operation {
    Read,
    Write,
    Flush,
}

struct PendingRequest {
    id: usize,
    aiocb: Box<libc::aiocb>,
    _buffer: Option<SharedBuffer>,
    expected_len: usize,
}

struct AioIoChannel {
    file: File,
    readonly: bool,
    queued: Vec<QueuedRequest>,
    pending: Vec<PendingRequest>,
    finished_requests: Vec<(usize, bool)>,
}

impl AioIoChannel {
    fn new(path: &Path, readonly: bool) -> Result<Self> {
        let file = OpenOptions::new()
            .read(true)
            .write(!readonly)
            .open(path)
            .map_err(|e| {
                error!("Failed to open file {}: {e}", path.display());
                VhostUserBlockError::IoError { source: e }
            })?;

        Ok(AioIoChannel {
            file,
            readonly,
            queued: Vec::new(),
            pending: Vec::new(),
            finished_requests: Vec::new(),
        })
    }

    fn submit_queued(&mut self) {
        let mut queued = std::mem::take(&mut self.queued);
        for request in queued.drain(..) {
            let operation = request.operation;
            match operation {
                Operation::Write if self.readonly => {
                    self.finished_requests.push((request.id, false));
                }
                Operation::Flush => {
                    if unsafe { libc::fsync(self.file.as_raw_fd()) } == 0 {
                        self.finished_requests.push((request.id, true));
                    } else {
                        let err = std::io::Error::last_os_error();
                        error!("Failed to fsync: {err}");
                        self.finished_requests.push((request.id, false));
                    }
                }
                _ => match self.submit_request(request, operation) {
                    Ok(pending) => self.pending.push(pending),
                    Err((id, err)) => {
                        error!("AIO submission failed: {err}");
                        self.finished_requests.push((id, false));
                    }
                },
            }
        }
        self.queued = queued;
    }

    fn submit_request(
        &self,
        request: QueuedRequest,
        operation: Operation,
    ) -> std::result::Result<PendingRequest, (usize, String)> {
        let buffer = request.buffer.expect("buffer required for IO");
        let expected_len = (request.sector_count as usize).saturating_mul(SECTOR_SIZE);
        let offset_bytes = match request
            .sector_offset
            .checked_mul(SECTOR_SIZE as u64)
            .and_then(|v| i64::try_from(v).ok())
        {
            Some(v) => v,
            None => return Err((request.id, "offset overflow".to_string())),
        };

        let mut aiocb = Box::new(unsafe { std::mem::zeroed::<libc::aiocb>() });
        aiocb.aio_fildes = self.file.as_raw_fd();
        aiocb.aio_offset = offset_bytes;
        aiocb.aio_nbytes = expected_len;
        aiocb.aio_reqprio = 0;
        aiocb.aio_sigevent = unsafe { std::mem::zeroed() };
        aiocb.aio_sigevent.sigev_notify = libc::SIGEV_NONE;

        let submit_result = match operation {
            Operation::Read => {
                let mut borrow = buffer.borrow_mut();
                aiocb.aio_buf = borrow.as_mut_ptr() as *mut _;
                let res = unsafe { libc::aio_read(&mut *aiocb) };
                drop(borrow);
                res
            }
            Operation::Write => {
                let borrow = buffer.borrow();
                aiocb.aio_buf = borrow.as_ptr() as *mut _;
                let res = unsafe { libc::aio_write(&mut *aiocb) };
                drop(borrow);
                res
            }
            Operation::Flush => unreachable!(),
        };

        if submit_result == 0 {
            Ok(PendingRequest {
                id: request.id,
                aiocb,
                _buffer: Some(buffer),
                expected_len,
            })
        } else {
            let err = std::io::Error::last_os_error();
            Err((request.id, err.to_string()))
        }
    }
}

impl IoChannel for AioIoChannel {
    fn add_read(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        self.queued.push(QueuedRequest {
            sector_offset,
            sector_count,
            buffer: Some(buf),
            id,
            operation: Operation::Read,
        });
    }

    fn add_write(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        self.queued.push(QueuedRequest {
            sector_offset,
            sector_count,
            buffer: Some(buf),
            id,
            operation: Operation::Write,
        });
    }

    fn add_flush(&mut self, id: usize) {
        self.queued.push(QueuedRequest {
            sector_offset: 0,
            sector_count: 0,
            buffer: None,
            id,
            operation: Operation::Flush,
        });
    }

    fn submit(&mut self) -> Result<()> {
        self.submit_queued();
        Ok(())
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        self.submit_queued();

        let mut remaining = Vec::new();
        for mut pending in self.pending.drain(..) {
            let status = unsafe { libc::aio_error(&*pending.aiocb) };
            if status == libc::EINPROGRESS {
                remaining.push(pending);
                continue;
            }

            if status != 0 {
                let errno = Errno::from_raw(status);
                if errno == Errno::UnknownErrno {
                    error!("AIO request {} failed with status {status}", pending.id);
                } else {
                    error!("AIO request {} failed: {errno}", pending.id);
                }
                self.finished_requests.push((pending.id, false));
                continue;
            }

            let ret = unsafe { libc::aio_return(&mut *pending.aiocb) };
            if ret < 0 || ret as usize != pending.expected_len {
                if ret < 0 {
                    let err = std::io::Error::last_os_error();
                    error!("AIO completion {} failed: {err}", pending.id);
                } else {
                    error!(
                        "AIO completion {} returned unexpected length {} (expected {})",
                        pending.id, ret, pending.expected_len
                    );
                }
                self.finished_requests.push((pending.id, false));
            } else {
                self.finished_requests.push((pending.id, true));
            }
        }
        self.pending = remaining;

        std::mem::take(&mut self.finished_requests)
    }

    fn busy(&self) -> bool {
        !self.finished_requests.is_empty() || !self.pending.is_empty() || !self.queued.is_empty()
    }
}

pub struct AioBlockDevice {
    path: PathBuf,
    sector_count: u64,
    readonly: bool,
}

impl BlockDevice for AioBlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>> {
        let channel = AioIoChannel::new(&self.path, self.readonly)?;
        Ok(Box::new(channel))
    }

    fn sector_count(&self) -> u64 {
        self.sector_count
    }

    fn clone(&self) -> Box<dyn BlockDevice> {
        Box::new(AioBlockDevice {
            path: self.path.clone(),
            sector_count: self.sector_count,
            readonly: self.readonly,
        })
    }
}

impl AioBlockDevice {
    pub fn new(path: PathBuf, readonly: bool) -> Result<Box<Self>> {
        let metadata = std::fs::metadata(&path).map_err(|e| {
            error!("Failed to get metadata for file {}: {e}", path.display());
            VhostUserBlockError::IoError { source: e }
        })?;

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
        Ok(Box::new(AioBlockDevice {
            path,
            sector_count,
            readonly,
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;
    use std::io::Write;
    use std::rc::Rc;
    use std::thread;
    use std::time::Duration;

    fn wait_for_completion(chan: &mut dyn IoChannel, expected: usize) -> Vec<(usize, bool)> {
        for _ in 0..20 {
            let results = chan.poll();
            if results.iter().any(|(id, _)| *id == expected) {
                return results;
            }
            thread::sleep(Duration::from_millis(10));
        }
        chan.poll()
    }

    #[test]
    fn basic_read_write() -> Result<()> {
        let tmpfile =
            NamedTempFile::new().map_err(|e| VhostUserBlockError::IoError { source: e })?;
        tmpfile
            .as_file()
            .set_len((SECTOR_SIZE * 4) as u64)
            .map_err(|e| VhostUserBlockError::IoError { source: e })?;

        let device = AioBlockDevice::new(tmpfile.path().to_path_buf(), false)?;
        let mut chan = device.create_channel()?;

        let pattern = vec![0x55u8; SECTOR_SIZE];
        let write_buf = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        write_buf
            .borrow_mut()
            .as_mut_slice()
            .copy_from_slice(&pattern);

        chan.add_write(0, 1, write_buf.clone(), 1);
        chan.submit()?;
        let result = wait_for_completion(chan.as_mut(), 1);
        assert_eq!(result, vec![(1, true)]);

        let read_buf = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        chan.add_read(0, 1, read_buf.clone(), 2);
        chan.submit()?;
        let result = wait_for_completion(chan.as_mut(), 2);
        assert_eq!(result, vec![(2, true)]);
        assert_eq!(read_buf.borrow().as_slice(), pattern.as_slice());

        Ok(())
    }

    #[test]
    fn readonly_write_fails() -> Result<()> {
        let tmpfile =
            NamedTempFile::new().map_err(|e| VhostUserBlockError::IoError { source: e })?;
        tmpfile
            .as_file()
            .set_len((SECTOR_SIZE * 2) as u64)
            .map_err(|e| VhostUserBlockError::IoError { source: e })?;

        let device = AioBlockDevice::new(tmpfile.path().to_path_buf(), true)?;
        let mut chan = device.create_channel()?;
        let write_buf = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        chan.add_write(0, 1, write_buf.clone(), 1);
        chan.submit()?;
        let result = wait_for_completion(chan.as_mut(), 1);
        assert_eq!(result, vec![(1, false)]);
        Ok(())
    }

    #[test]
    fn flush_request() -> Result<()> {
        let tmpfile =
            NamedTempFile::new().map_err(|e| VhostUserBlockError::IoError { source: e })?;
        tmpfile
            .as_file()
            .set_len((SECTOR_SIZE * 2) as u64)
            .map_err(|e| VhostUserBlockError::IoError { source: e })?;

        let device = AioBlockDevice::new(tmpfile.path().to_path_buf(), false)?;
        let mut chan = device.create_channel()?;
        assert!(!chan.busy());
        chan.add_flush(1);
        chan.submit()?;
        let result = chan.poll();
        assert_eq!(result, vec![(1, true)]);
        assert!(!chan.busy());
        Ok(())
    }

    #[test]
    fn busy_state() -> Result<()> {
        let tmpfile =
            NamedTempFile::new().map_err(|e| VhostUserBlockError::IoError { source: e })?;
        tmpfile
            .as_file()
            .set_len((SECTOR_SIZE * 2) as u64)
            .map_err(|e| VhostUserBlockError::IoError { source: e })?;

        let device = AioBlockDevice::new(tmpfile.path().to_path_buf(), false)?;
        let mut chan = device.create_channel()?;
        let read_buf = Rc::new(RefCell::new(AlignedBuf::new(SECTOR_SIZE)));
        chan.add_read(0, 1, read_buf.clone(), 1);
        assert!(chan.busy());
        chan.submit()?;
        assert!(chan.busy());
        let _ = wait_for_completion(chan.as_mut(), 1);
        assert!(!chan.busy());
        Ok(())
    }

    #[test]
    fn device_creation_errors() {
        let path = PathBuf::from("/no/such/file");
        assert!(matches!(
            AioBlockDevice::new(path, false),
            Err(VhostUserBlockError::IoError { .. })
        ));

        let tmpfile = NamedTempFile::new().unwrap();
        tmpfile
            .as_file()
            .write_all(&[0u8; SECTOR_SIZE / 2])
            .unwrap();
        let path = tmpfile.path().to_path_buf();
        assert!(matches!(
            AioBlockDevice::new(path, false),
            Err(VhostUserBlockError::InvalidParameter { .. })
        ));
    }

    #[test]
    fn aio_channel_open_failure() {
        let path = Path::new("/this/file/does/not/exist");
        assert!(AioIoChannel::new(path, false).is_err());
    }
}
