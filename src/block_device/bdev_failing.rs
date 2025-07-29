use crate::block_device::bdev_test::TestBlockDevice;
use crate::block_device::{BlockDevice, IoChannel, SharedBuffer};
use crate::Result;
use log::error;
use std::sync::{Arc, Mutex};

#[derive(Default)]
pub struct FailState {
    fail_next_write: bool,
    fail_next_flush: bool,
}

pub struct FailingIoChannel {
    inner: Box<dyn IoChannel>,
    state: Arc<Mutex<FailState>>,
    pending: Vec<(usize, bool)>,
}

impl IoChannel for FailingIoChannel {
    fn add_read(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        self.inner.add_read(sector_offset, sector_count, buf, id);
    }

    fn add_write(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        let mut state = match self.state.lock() {
            Ok(s) => s,
            Err(e) => {
                error!("Failed to lock state mutex: {e}");
                self.pending.push((id, false));
                return;
            }
        };
        if state.fail_next_write {
            state.fail_next_write = false;
            self.pending.push((id, false));
        } else {
            self.inner.add_write(sector_offset, sector_count, buf, id);
        }
    }

    fn add_flush(&mut self, id: usize) {
        let mut state = match self.state.lock() {
            Ok(s) => s,
            Err(e) => {
                error!("Failed to lock state mutex: {e}");
                self.pending.push((id, false));
                return;
            }
        };
        if state.fail_next_flush {
            state.fail_next_flush = false;
            self.pending.push((id, false));
        } else {
            self.inner.add_flush(id);
        }
    }

    fn submit(&mut self) -> Result<()> {
        self.inner.submit()
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        let mut results = std::mem::take(&mut self.pending);
        results.extend(self.inner.poll());
        results
    }

    fn busy(&mut self) -> bool {
        self.inner.busy()
    }
}

pub struct FailingBlockDevice {
    inner: TestBlockDevice,
    state: Arc<Mutex<FailState>>,
}

impl FailingBlockDevice {
    pub fn new(size: u64) -> Self {
        FailingBlockDevice {
            inner: TestBlockDevice::new(size),
            state: Arc::new(Mutex::new(FailState::default())),
        }
    }

    pub fn fail_next_write(&self) {
        if let Ok(mut state) = self.state.lock() {
            state.fail_next_write = true;
        } else {
            error!("Failed to lock state mutex");
        }
    }

    pub fn fail_next_flush(&self) {
        if let Ok(mut state) = self.state.lock() {
            state.fail_next_flush = true;
        } else {
            error!("Failed to lock state mutex");
        }
    }
}

impl BlockDevice for FailingBlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>> {
        Ok(Box::new(FailingIoChannel {
            inner: self.inner.create_channel()?,
            state: self.state.clone(),
            pending: Vec::new(),
        }))
    }

    fn sector_count(&self) -> u64 {
        self.inner.sector_count()
    }
}
