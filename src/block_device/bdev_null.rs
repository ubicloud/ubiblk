use super::{BlockDevice, IoChannel, SharedBuffer};
use crate::vhost_backend::SECTOR_SIZE;
use crate::Result;

/// A block device that emulates `/dev/null`.
///
/// The device has a configurable capacity and always reports success for any
/// issued request. Read operations zero the provided buffer, while writes and
/// flushes are acknowledged immediately.
pub struct NullBlockDevice {
    sector_count: u64,
}

struct NullIoChannel {
    finished_requests: Vec<(usize, bool)>,
}

impl NullIoChannel {
    fn new() -> Self {
        NullIoChannel {
            finished_requests: Vec::new(),
        }
    }

    fn complete_success(&mut self, id: usize) {
        self.finished_requests.push((id, true));
    }
}

impl IoChannel for NullIoChannel {
    fn add_read(&mut self, _sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        let mut buf = buf.borrow_mut();
        let len = (sector_count as usize).saturating_mul(SECTOR_SIZE);
        let buf_slice = buf.as_mut_slice();
        let fill_len = std::cmp::min(buf_slice.len(), len);
        buf_slice[..fill_len].fill(0);
        self.complete_success(id);
    }

    fn add_write(
        &mut self,
        _sector_offset: u64,
        _sector_count: u32,
        _buf: SharedBuffer,
        id: usize,
    ) {
        self.complete_success(id);
    }

    fn add_flush(&mut self, id: usize) {
        self.complete_success(id);
    }

    fn submit(&mut self) -> Result<()> {
        Ok(())
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        std::mem::take(&mut self.finished_requests)
    }

    fn busy(&self) -> bool {
        false
    }
}

impl NullBlockDevice {
    pub fn new() -> Box<Self> {
        Box::new(NullBlockDevice { sector_count: 0 })
    }

    pub fn new_with_sector_count(sector_count: u64) -> Box<Self> {
        Box::new(NullBlockDevice { sector_count })
    }
}

impl BlockDevice for NullBlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>> {
        Ok(Box::new(NullIoChannel::new()))
    }

    fn sector_count(&self) -> u64 {
        self.sector_count
    }

    fn clone(&self) -> Box<dyn BlockDevice> {
        Box::new(NullBlockDevice {
            sector_count: self.sector_count,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block_device::shared_buffer;
    use crate::vhost_backend::SECTOR_SIZE;

    #[test]
    fn reports_zero_capacity() {
        let dev = NullBlockDevice::new();
        assert_eq!(dev.sector_count(), 0);
    }

    #[test]
    fn completes_requests_successfully() {
        let dev = NullBlockDevice::new();
        let mut chan = dev.create_channel().unwrap();

        let buf: SharedBuffer = shared_buffer(SECTOR_SIZE * 2);
        chan.add_read(10, 2, buf.clone(), 1);
        chan.add_write(20, 2, buf.clone(), 2);
        chan.add_flush(3);
        chan.submit().unwrap();

        let mut results = chan.poll();
        results.sort_by_key(|entry| entry.0);
        assert_eq!(results, vec![(1, true), (2, true), (3, true)]);

        let buf = buf.borrow();
        assert!(buf.as_slice()[..SECTOR_SIZE * 2]
            .iter()
            .all(|byte| *byte == 0));
    }
}
