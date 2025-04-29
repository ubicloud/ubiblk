use std::sync::atomic::Ordering;
use std::sync::{atomic::AtomicUsize, Arc, Mutex};

use super::*;

struct TestIoChannel {
    mem: Arc<Mutex<Vec<u8>>>,
    finished_requests: Vec<(usize, bool)>,
    reads: Arc<AtomicUsize>,
    writes: Arc<AtomicUsize>,
    flushes: Arc<AtomicUsize>,
}

impl IoChannel for TestIoChannel {
    fn add_read(&mut self, _sector: u64, _buf: SharedBuffer, _len: usize, _id: usize) {
        let mem = self.mem.lock().unwrap();
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
        self.reads.fetch_add(1, Ordering::SeqCst);
    }

    fn add_write(&mut self, _sector: u64, _buf: SharedBuffer, _len: usize, _id: usize) {
        let mut mem = self.mem.lock().unwrap();
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
        self.writes.fetch_add(1, Ordering::SeqCst);
    }

    fn add_flush(&mut self, _id: usize) {
        self.finished_requests.push((_id, true));
        self.flushes.fetch_add(1, Ordering::SeqCst);
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
    mem: Arc<Mutex<Vec<u8>>>,
    reads: Arc<AtomicUsize>,
    writes: Arc<AtomicUsize>,
    flushes: Arc<AtomicUsize>,
}

impl TestBlockDevice {
    pub fn new(size: u64) -> Self {
        let mem = Arc::new(Mutex::new(vec![0u8; size as usize]));
        TestBlockDevice {
            size,
            mem,
            reads: Arc::new(AtomicUsize::new(0)),
            writes: Arc::new(AtomicUsize::new(0)),
            flushes: Arc::new(AtomicUsize::new(0)),
        }
    }

    pub fn read(&self, offset: usize, buf: &mut [u8], len: usize) {
        let mem = self.mem.lock().unwrap();
        let start = offset;
        let end = start + len;
        buf.copy_from_slice(&mem[start..end]);
    }

    pub fn write(&self, offset: usize, buf: &[u8], len: usize) {
        let mut mem = self.mem.lock().unwrap();
        let start = offset;
        let end = start + len;
        mem[start..end].copy_from_slice(buf);
    }

    pub fn flushes(&self) -> usize {
        self.flushes.load(Ordering::SeqCst)
    }
}

impl BlockDevice for TestBlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>> {
        Ok(Box::new(TestIoChannel {
            mem: self.mem.clone(),
            finished_requests: Vec::new(),
            reads: self.reads.clone(),
            writes: self.writes.clone(),
            flushes: self.flushes.clone(),
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
