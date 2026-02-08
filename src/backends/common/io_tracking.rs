use std::sync::{
    atomic::{AtomicU64, AtomicU8},
    Arc,
};

use log::{info, warn};

use crate::backends::SECTOR_SIZE;

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
    total_bytes_read: Arc<AtomicU64>,
    total_bytes_written: Arc<AtomicU64>,
    total_read_ops: Arc<AtomicU64>,
    total_write_ops: Arc<AtomicU64>,
    total_flush_ops: Arc<AtomicU64>,
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
        IoTracker {
            ios: vec,
            total_bytes_read: Arc::new(AtomicU64::new(0)),
            total_bytes_written: Arc::new(AtomicU64::new(0)),
            total_read_ops: Arc::new(AtomicU64::new(0)),
            total_write_ops: Arc::new(AtomicU64::new(0)),
            total_flush_ops: Arc::new(AtomicU64::new(0)),
        }
    }

    pub fn add_read(&self, slot: usize, offset_sectors: u64, length_sectors: u64) {
        // Update cumulative counters
        self.total_bytes_read.fetch_add(
            length_sectors * SECTOR_SIZE as u64,
            std::sync::atomic::Ordering::Relaxed,
        );
        self.total_read_ops
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);

        if slot >= self.ios.len() {
            info!(
                "Large IO (read): slot {}, offset {} sectors, length {} sectors",
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

    pub fn add_write(&self, slot: usize, offset_sectors: u64, length_sectors: u64) {
        // Update cumulative counters
        self.total_bytes_written.fetch_add(
            length_sectors * SECTOR_SIZE as u64,
            std::sync::atomic::Ordering::Relaxed,
        );
        self.total_write_ops
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);

        if slot >= self.ios.len() {
            info!(
                "Large IO (write): slot {}, offset {} sectors, length {} sectors",
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

    pub fn add_flush(&self, slot: usize) {
        // Update cumulative counter
        self.total_flush_ops
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);

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

    /// Returns cumulative statistics: (bytes_read, bytes_written, read_ops, write_ops, flush_ops)
    pub fn cumulative_stats(&self) -> (u64, u64, u64, u64, u64) {
        (
            self.total_bytes_read
                .load(std::sync::atomic::Ordering::Relaxed),
            self.total_bytes_written
                .load(std::sync::atomic::Ordering::Relaxed),
            self.total_read_ops
                .load(std::sync::atomic::Ordering::Relaxed),
            self.total_write_ops
                .load(std::sync::atomic::Ordering::Relaxed),
            self.total_flush_ops
                .load(std::sync::atomic::Ordering::Relaxed),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cumulative_counters() {
        let tracker = IoTracker::new(10);
        let clone = tracker.clone();

        // Perform operations on the original
        tracker.add_read(0, 100, 8);
        tracker.add_write(1, 200, 16);
        tracker.add_flush(2);

        // Verify stats on original
        let (bytes_read, bytes_written, read_ops, write_ops, flush_ops) =
            tracker.cumulative_stats();
        assert_eq!(bytes_read, 8 * SECTOR_SIZE as u64);
        assert_eq!(bytes_written, 16 * SECTOR_SIZE as u64);
        assert_eq!(read_ops, 1);
        assert_eq!(write_ops, 1);
        assert_eq!(flush_ops, 1);

        // Verify clone sees the same values (critical: Arc sharing)
        let (
            bytes_read_clone,
            bytes_written_clone,
            read_ops_clone,
            write_ops_clone,
            flush_ops_clone,
        ) = clone.cumulative_stats();
        assert_eq!(bytes_read_clone, 8 * SECTOR_SIZE as u64);
        assert_eq!(bytes_written_clone, 16 * SECTOR_SIZE as u64);
        assert_eq!(read_ops_clone, 1);
        assert_eq!(write_ops_clone, 1);
        assert_eq!(flush_ops_clone, 1);

        // Add more operations on original
        tracker.add_read(3, 300, 2);
        tracker.add_write(4, 400, 4);

        // Verify updated stats on both
        let (bytes_read, bytes_written, read_ops, write_ops, _) = tracker.cumulative_stats();
        assert_eq!(bytes_read, (8 + 2) * SECTOR_SIZE as u64);
        assert_eq!(bytes_written, (16 + 4) * SECTOR_SIZE as u64);
        assert_eq!(read_ops, 2);
        assert_eq!(write_ops, 2);

        let (bytes_read_clone, bytes_written_clone, read_ops_clone, write_ops_clone, _) =
            clone.cumulative_stats();
        assert_eq!(bytes_read_clone, (8 + 2) * SECTOR_SIZE as u64);
        assert_eq!(bytes_written_clone, (16 + 4) * SECTOR_SIZE as u64);
        assert_eq!(read_ops_clone, 2);
        assert_eq!(write_ops_clone, 2);
    }
}
