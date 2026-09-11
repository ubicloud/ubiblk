//! The durable map: where the authoritative copy of each chunk is.

pub mod format;
pub mod journal;
pub mod storage;

#[cfg(test)]
pub mod fake;
