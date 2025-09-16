use std::{cell::RefCell, collections::VecDeque, rc::Rc};

use crate::block_device::SharedBuffer;

use super::aligned_buffer::AlignedBuf;

pub struct AlignedBufferPool {
    buffers: Vec<SharedBuffer>,
    available_buffers: VecDeque<usize>,
    in_use: Vec<bool>,
}

impl AlignedBufferPool {
    pub fn new(alignment: usize, count: usize, size: usize) -> Self {
        let mut buffers = Vec::with_capacity(count);
        let mut available_buffers = VecDeque::with_capacity(count);
        let mut in_use = Vec::with_capacity(count);
        for _ in 0..count {
            buffers.push(Rc::new(RefCell::new(AlignedBuf::new_with_alignment(
                size, alignment,
            ))));
            available_buffers.push_back(buffers.len() - 1);
            in_use.push(false);
        }
        Self {
            buffers,
            available_buffers,
            in_use,
        }
    }

    pub fn get_buffer(&mut self) -> Option<(SharedBuffer, usize)> {
        self.available_buffers.pop_front().map(|index| {
            self.in_use[index] = true;
            (self.buffers[index].clone(), index)
        })
    }

    pub fn return_buffer(&mut self, index: usize) {
        assert!(
            index < self.buffers.len(),
            "Invalid buffer index {} returned to pool (max: {})",
            index,
            self.buffers.len() - 1
        );

        if !self.in_use[index] {
            panic!("Buffer index {index} was returned to the pool but is not currently in use");
        }

        self.in_use[index] = false;
        self.available_buffers.push_back(index);
    }

    pub fn has_available(&self) -> bool {
        !self.available_buffers.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_aligned_buffer_pool() {
        let mut pool = AlignedBufferPool::new(4096, 10, 8192);
        let (buffer, index) = pool.get_buffer().unwrap();
        assert_eq!(buffer.borrow().len(), 8192);
        pool.return_buffer(index);
    }

    #[test]
    fn test_get_buffer_none_when_exhausted() {
        let mut pool = AlignedBufferPool::new(4096, 1, 512);
        // First buffer is available
        assert!(pool.get_buffer().is_some());
        // Pool is now empty
        assert!(pool.get_buffer().is_none());
    }

    #[test]
    #[should_panic(expected = "Invalid buffer index")]
    fn test_returning_invalid_index_panics() {
        let mut pool = AlignedBufferPool::new(4096, 1, 512);
        // Only index 0 is valid
        pool.return_buffer(1);
    }

    #[test]
    #[should_panic(expected = "not currently in use")]
    fn test_returning_same_index_twice_panics() {
        let mut pool = AlignedBufferPool::new(4096, 1, 512);
        let (_, index) = pool.get_buffer().unwrap();
        pool.return_buffer(index);
        pool.return_buffer(index);
    }

    #[test]
    fn test_has_available_tracks_availability() {
        let mut pool = AlignedBufferPool::new(4096, 2, 512);
        assert!(pool.has_available());
        // Exhaust the pool
        let _ = pool.get_buffer().unwrap();
        let _ = pool.get_buffer().unwrap();
        assert!(!pool.has_available());
    }
}
