//! The durable map: where the authoritative copy of each chunk is.

pub mod checkpoint;
pub mod format;
pub mod journal;
pub mod storage;
pub mod superblock;

#[cfg(test)]
pub mod fake;
