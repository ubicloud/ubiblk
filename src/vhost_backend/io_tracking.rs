use std::sync::{
    atomic::{AtomicU64, AtomicU8},
    Arc,
};

use log::{info, warn};

pub enum IoKind {
    Read = 1,
    Write = 2,
    Flush = 3,
}

pub struct IoRecord {
    pub kind: AtomicU8,
    pub offset_sectors: AtomicU64,
    pub length_sectors: AtomicU64,
}

#[derive(Clone)]
pub struct IoTracker {
    ios: Vec<Arc<IoRecord>>,
}

impl IoTracker {
    pub fn new(size: usize) -> Self {
        let vec = (0..size)
            .map(|_| {
                Arc::new(IoRecord {
                    kind: AtomicU8::new(0),
                    offset_sectors: AtomicU64::new(0),
                    length_sectors: AtomicU64::new(0),
                })
            })
            .collect();
        IoTracker { ios: vec }
    }

    pub fn add_read(&mut self, slot: usize, offset_sectors: u64, length_sectors: u64) {
        if slot >= self.ios.len() {
            info!(
                "Large IO (read): slot {}, offset {}, length {}",
                slot, offset_sectors, length_sectors
            );
            return;
        }
        self.warn_if_already_used(slot);
        let io = &self.ios[slot];
        io.offset_sectors
            .store(offset_sectors, std::sync::atomic::Ordering::Relaxed);
        io.length_sectors
            .store(length_sectors, std::sync::atomic::Ordering::Relaxed);
        io.kind
            .store(IoKind::Read as u8, std::sync::atomic::Ordering::Release);
    }

    pub fn add_write(&mut self, slot: usize, offset_sectors: u64, length_sectors: u64) {
        if slot >= self.ios.len() {
            info!(
                "Large IO (write): slot {}, offset {}, length {}",
                slot, offset_sectors, length_sectors
            );
            return;
        }
        self.warn_if_already_used(slot);
        let io = &self.ios[slot];
        io.offset_sectors
            .store(offset_sectors, std::sync::atomic::Ordering::Relaxed);
        io.length_sectors
            .store(length_sectors, std::sync::atomic::Ordering::Relaxed);
        io.kind
            .store(IoKind::Write as u8, std::sync::atomic::Ordering::Release);
    }

    pub fn add_flush(&mut self, slot: usize) {
        if slot >= self.ios.len() {
            info!("Large IO (flush): slot {}", slot);
            return;
        }
        self.warn_if_already_used(slot);
        let io = &self.ios[slot];
        io.kind
            .store(IoKind::Flush as u8, std::sync::atomic::Ordering::Release);
    }

    fn warn_if_already_used(&self, slot: usize) {
        let io = &self.ios[slot];
        let kind = io.kind.load(std::sync::atomic::Ordering::Acquire);
        if kind != 0 {
            warn!("IO slot {} is already in use", slot);
        }
    }

    pub fn clear(&mut self, slot: usize) {
        if slot >= self.ios.len() {
            return;
        }
        let io = &self.ios[slot];
        io.kind.store(0, std::sync::atomic::Ordering::Release);
    }

    pub fn snapshot(&self) -> Vec<(IoKind, u64, u64)> {
        self.ios
            .iter()
            .filter_map(|io| {
                let kind = io.kind.load(std::sync::atomic::Ordering::Acquire);
                if kind == 0 {
                    None
                } else {
                    let offset = io.offset_sectors.load(std::sync::atomic::Ordering::Relaxed);
                    let length = io.length_sectors.load(std::sync::atomic::Ordering::Relaxed);
                    Some((
                        match kind {
                            1 => IoKind::Read,
                            2 => IoKind::Write,
                            3 => IoKind::Flush,
                            _ => unreachable!(),
                        },
                        offset,
                        length,
                    ))
                }
            })
            .collect()
    }
}
