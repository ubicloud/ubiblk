use std::sync::{Arc, RwLock};

use super::*;

pub struct TestDeviceMetrics {
    pub reads: usize,
    pub writes: usize,
    pub flushes: usize,
}

struct TestIoChannel {
    mem: Arc<RwLock<Vec<u8>>>,
    finished_requests: Vec<(usize, bool)>,
    metrics: Arc<RwLock<TestDeviceMetrics>>,
}

impl IoChannel for TestIoChannel {
    fn add_read(&mut self, _sector: u64, _buf: SharedBuffer, _len: usize, _id: usize) {
        let mem = self.mem.read().unwrap();
        let mut buf = _buf.borrow_mut();
        let len = buf.len();
        let start = (_sector * 512) as usize;
        let end = start + len;
        if end > mem.len() {
            self.finished_requests.push((_id, false));
            return;
        }

        buf.copy_from_slice(&mem[start..end]);
        self.finished_requests.push((_id, true));
        self.metrics.write().unwrap().reads += 1;
    }

    fn add_write(&mut self, _sector: u64, _buf: SharedBuffer, _len: usize, _id: usize) {
        let mut mem = self.mem.write().unwrap();
        let buf = _buf.borrow();
        let len = buf.len();
        let start = (_sector * 512) as usize;
        let end = start + len;
        if end > mem.len() {
            self.finished_requests.push((_id, false));
            return;
        }

        mem[start..end].copy_from_slice(&buf);
        self.finished_requests.push((_id, true));
        self.metrics.write().unwrap().writes += 1;
    }

    fn add_flush(&mut self, _id: usize) {
        self.finished_requests.push((_id, true));
        self.metrics.write().unwrap().flushes += 1;
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

pub struct TestBlockDevice {
    size: u64,
    pub mem: Arc<RwLock<Vec<u8>>>,
    pub metrics: Arc<RwLock<TestDeviceMetrics>>,
}

impl TestBlockDevice {
    pub fn new(size: u64) -> Self {
        let mem = Arc::new(RwLock::new(vec![0u8; size as usize]));
        TestBlockDevice {
            size,
            mem,
            metrics: Arc::new(RwLock::new(TestDeviceMetrics {
                reads: 0,
                writes: 0,
                flushes: 0,
            })),
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
        }))
    }

    fn size(&self) -> u64 {
        self.size
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_io_channel() {
        let device = TestBlockDevice::new(1024 * 1024);
        let mut channel = device.create_channel().unwrap();

        let buf: SharedBuffer = Rc::new(RefCell::new(vec![0u8; 512]));
        channel.add_read(0, buf.clone(), 512, 1);
        channel.submit().unwrap();
        let results = channel.poll();
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].0, 1);
        assert_eq!(results[0].1, true);
    }
}
