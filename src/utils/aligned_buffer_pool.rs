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
        let buffers = (0..count)
            .map(|index| {
                let mut buf = AlignedBuf::new_with_alignment(size, alignment);
                buf.id = index;
                Rc::new(RefCell::new(buf))
            })
            .collect();

        Self {
            buffers,
            available_buffers: (0..count).collect(),
            in_use: vec![false; count],
        }
    }

    pub fn get_buffer(&mut self) -> Option<SharedBuffer> {
        self.available_buffers.pop_front().map(|index| {
            self.in_use[index] = true;
            self.buffers[index].clone()
        })
    }

    pub fn return_buffer(&mut self, buffer: &SharedBuffer) {
        let index = buffer.borrow().id;
        assert!(
            index < self.buffers.len(),
            "Invalid buffer index {} returned to pool (max: {})",
            index,
            self.buffers.len() - 1
        );

        assert!(
            self.in_use[index],
            "Buffer index {index} was returned to the pool but is not currently in use"
        );

        assert!(
            Rc::ptr_eq(buffer, &self.buffers[index]),
            "Returned buffer does not match the pool's buffer at index {index}"
        );

        self.in_use[index] = false;
        self.available_buffers.push_back(index);
    }

    pub fn has_available(&self) -> bool {
        !self.available_buffers.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use crate::{backends::SECTOR_SIZE, block_device::shared_buffer};

    use super::*;

    #[test]
    fn test_aligned_buffer_pool() {
        let mut pool = AlignedBufferPool::new(4096, 10, 8192);
        let buffer = pool.get_buffer().unwrap();
        assert_eq!(buffer.borrow().len(), 8192);
        pool.return_buffer(&buffer);
    }

    #[test]
    fn test_get_buffer_none_when_exhausted() {
        let mut pool = AlignedBufferPool::new(4096, 1, SECTOR_SIZE);
        // First buffer is available
        assert!(pool.get_buffer().is_some());
        // Pool is now empty
        assert!(pool.get_buffer().is_none());
    }

    #[test]
    #[should_panic(expected = "Invalid buffer index")]
    fn test_returning_buffer_with_index_out_of_bounds_panics() {
        let mut pool = AlignedBufferPool::new(4096, 1, SECTOR_SIZE);
        let buffer = shared_buffer(1024);
        buffer.borrow_mut().id = 128;
        pool.return_buffer(&buffer);
    }

    #[test]
    #[should_panic(expected = "Returned buffer does not match the pool's buffer")]
    fn test_returning_buffer_not_from_pool_panics() {
        let mut pool = AlignedBufferPool::new(4096, 1, SECTOR_SIZE);
        let _borrowed_buffer = pool.get_buffer().unwrap();
        let buffer = shared_buffer(1024);
        pool.return_buffer(&buffer);
    }

    #[test]
    #[should_panic(expected = "not currently in use")]
    fn test_returning_same_buffer_twice_panics() {
        let mut pool = AlignedBufferPool::new(4096, 1, SECTOR_SIZE);
        let buffer = pool.get_buffer().unwrap();
        pool.return_buffer(&buffer);
        pool.return_buffer(&buffer);
    }

    #[test]
    fn test_has_available_tracks_availability() {
        let mut pool = AlignedBufferPool::new(4096, 2, SECTOR_SIZE);
        assert!(pool.has_available());
        // Exhaust the pool
        let _ = pool.get_buffer().unwrap();
        let _ = pool.get_buffer().unwrap();
        assert!(!pool.has_available());
    }
}
