use std::{cell::RefCell, collections::VecDeque, rc::Rc};

use crate::block_device::SharedBuffer;

use super::aligned_buffer::AlignedBuf;

pub struct AlignedBufferPool {
    buffers: Vec<SharedBuffer>,
    available_buffers: VecDeque<usize>,
}

impl AlignedBufferPool {
    pub fn new(alignment: usize, count: usize, size: usize) -> Self {
        let mut buffers = Vec::with_capacity(count);
        let mut available_buffers = VecDeque::with_capacity(count);
        for _ in 0..count {
            buffers.push(Rc::new(RefCell::new(AlignedBuf::new_with_alignment(
                size, alignment,
            ))));
            available_buffers.push_back(buffers.len() - 1);
        }
        Self {
            buffers,
            available_buffers,
        }
    }

    pub fn get_buffer(&mut self) -> Option<(SharedBuffer, usize)> {
        if let Some(index) = self.available_buffers.pop_front() {
            let buffer = self.buffers[index].clone();
            Some((buffer, index))
        } else {
            None
        }
    }

    pub fn return_buffer(&mut self, index: usize) {
        if index < self.buffers.len() {
            self.available_buffers.push_back(index);
        } else {
            panic!(
                "Invalid buffer index {} returned to pool (max: {})",
                index,
                self.buffers.len() - 1
            );
        }
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
}
