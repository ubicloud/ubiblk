use std::sync::{atomic::AtomicBool, Arc, RwLock};

use crate::vhost_backend::SECTOR_SIZE;

use super::*;

pub struct TestDeviceMetrics {
    pub reads: usize,
    pub writes: usize,
    pub flushes: usize,
}

struct TestIoChannel {
    mem: Arc<RwLock<Vec<u8>>>,
    fail_next: Arc<AtomicBool>,
    finished_requests: Vec<(usize, bool)>,
    metrics: Arc<RwLock<TestDeviceMetrics>>,
}

impl IoChannel for TestIoChannel {
    fn add_read(&mut self, sector_offset: u64, sector_count: u32, _buf: SharedBuffer, _id: usize) {
        if self
            .fail_next
            .swap(false, std::sync::atomic::Ordering::SeqCst)
        {
            self.finished_requests.push((_id, false));
            return;
        }

        let mem = self.mem.read().unwrap();
        let mut buf = _buf.borrow_mut();
        let len = sector_count as usize * SECTOR_SIZE;
        let start = sector_offset as usize * SECTOR_SIZE;
        let end = start + len;
        if end > mem.len() {
            self.finished_requests.push((_id, false));
            return;
        }

        buf.as_mut_slice()[..len].copy_from_slice(&mem[start..end]);
        self.finished_requests.push((_id, true));
        self.metrics.write().unwrap().reads += 1;
    }

    fn add_write(&mut self, sector_offset: u64, sector_count: u32, _buf: SharedBuffer, _id: usize) {
        if self
            .fail_next
            .swap(false, std::sync::atomic::Ordering::SeqCst)
        {
            self.finished_requests.push((_id, false));
            return;
        }

        let mut mem = self.mem.write().unwrap();
        let buf = _buf.borrow();
        let len = sector_count as usize * SECTOR_SIZE;
        let start = sector_offset as usize * SECTOR_SIZE;
        let end = start + len;
        if end > mem.len() {
            self.finished_requests.push((_id, false));
            return;
        }

        mem[start..end].copy_from_slice(&buf.as_slice()[..len]);
        self.finished_requests.push((_id, true));
        self.metrics.write().unwrap().writes += 1;
    }

    fn add_flush(&mut self, _id: usize) {
        if self
            .fail_next
            .swap(false, std::sync::atomic::Ordering::SeqCst)
        {
            self.finished_requests.push((_id, false));
            return;
        }

        self.finished_requests.push((_id, true));
        self.metrics.write().unwrap().flushes += 1;
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

pub struct TestBlockDevice {
    sector_count: u64,
    pub mem: Arc<RwLock<Vec<u8>>>,
    pub metrics: Arc<RwLock<TestDeviceMetrics>>,
    pub fail_next: Arc<AtomicBool>,
}

impl TestBlockDevice {
    pub fn new(size: u64) -> Self {
        assert!(
            size.is_multiple_of(SECTOR_SIZE as u64),
            "Size must be a multiple of SECTOR_SIZE"
        );
        let sector_count = size / SECTOR_SIZE as u64;
        let mem = Arc::new(RwLock::new(vec![0u8; size as usize]));
        let fail_next = Arc::new(AtomicBool::new(false));
        TestBlockDevice {
            sector_count,
            mem,
            metrics: Arc::new(RwLock::new(TestDeviceMetrics {
                reads: 0,
                writes: 0,
                flushes: 0,
            })),
            fail_next,
        }
    }

    pub fn read(&self, offset: usize, buf: &mut [u8], len: usize) {
        let mem = self.mem.read().unwrap();
        let start = offset;
        let end = start + len;
        buf.copy_from_slice(&mem[start..end]);
    }

    pub fn write(&self, offset: usize, buf: &[u8], len: usize) {
        let mut mem = self.mem.write().unwrap();
        let start = offset;
        let end = start + len;
        mem[start..end].copy_from_slice(buf);
    }

    pub fn flushes(&self) -> usize {
        self.metrics.read().unwrap().flushes
    }
}

impl BlockDevice for TestBlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>> {
        Ok(Box::new(TestIoChannel {
            mem: self.mem.clone(),
            finished_requests: Vec::new(),
            metrics: self.metrics.clone(),
            fail_next: self.fail_next.clone(),
        }))
    }

    fn sector_count(&self) -> u64 {
        self.sector_count
    }

    fn clone(&self) -> Box<dyn BlockDevice> {
        Box::new(TestBlockDevice {
            sector_count: self.sector_count,
            mem: self.mem.clone(),
            metrics: self.metrics.clone(),
            fail_next: self.fail_next.clone(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    // Validate that a basic read operation succeeds on a new channel.
    fn test_io_channel() {
        let device = TestBlockDevice::new(1024 * 1024);
        let mut channel = device.create_channel().unwrap();

        let buf: SharedBuffer = shared_buffer(SECTOR_SIZE);
        channel.add_read(0, 1, buf.clone(), 1);
        channel.submit().unwrap();
        let results = channel.poll();
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].0, 1);
        assert!(results[0].1);
    }

    #[test]
    // Exercise read, write and flush operations and verify metrics.
    fn test_read_write_and_flush_metrics() {
        let device = TestBlockDevice::new(2 * SECTOR_SIZE as u64);
        let mut channel = device.create_channel().unwrap();

        let pattern = vec![0x55u8; SECTOR_SIZE];
        let write_buf: SharedBuffer = shared_buffer(SECTOR_SIZE);
        write_buf
            .borrow_mut()
            .as_mut_slice()
            .copy_from_slice(&pattern);
        channel.add_write(0, 1, write_buf.clone(), 1);
        channel.add_flush(2);
        channel.submit().unwrap();
        let mut results = channel.poll();
        results.sort_by_key(|x| x.0);
        assert_eq!(results, vec![(1, true), (2, true)]);

        let read_buf: SharedBuffer = shared_buffer(SECTOR_SIZE);
        channel.add_read(0, 1, read_buf.clone(), 3);
        channel.submit().unwrap();
        let results = channel.poll();
        assert_eq!(results, vec![(3, true)]);
        assert_eq!(read_buf.borrow().as_slice(), pattern.as_slice());

        let metrics = device.metrics.read().unwrap();
        assert_eq!(metrics.reads, 1);
        assert_eq!(metrics.writes, 1);
        assert_eq!(metrics.flushes, 1);
        drop(metrics);
        assert_eq!(device.flushes(), 1);
    }

    #[test]
    // Trigger out-of-bounds operations and verify helper methods work.
    fn test_overflow_operations_and_helpers() {
        let device = TestBlockDevice::new(SECTOR_SIZE as u64);
        let mut channel = device.create_channel().unwrap();

        let buf: SharedBuffer = shared_buffer(SECTOR_SIZE);
        channel.add_read(1, 1, buf.clone(), 1);
        channel.add_write(1, 1, buf.clone(), 2);
        channel.submit().unwrap();
        let mut results = channel.poll();
        results.sort_by_key(|x| x.0);
        assert_eq!(results, vec![(1, false), (2, false)]);

        // Test direct read/write helpers
        let pattern = vec![1u8, 2, 3, 4];
        let len = pattern.len();
        device.write(0, &pattern, len);
        let mut out = vec![0u8; len];
        device.read(0, &mut out, len);
        assert_eq!(out, pattern);
    }
}
