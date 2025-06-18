use std::slice;

/// Default alignment for buffers used with O_DIRECT.
pub const BUFFER_ALIGNMENT: usize = 4096;

/// A byte buffer with guaranteed alignment.
///
/// Internally this allocates a vector slightly larger than requested so that
/// the returned slice is aligned to `BUFFER_ALIGNMENT` bytes.
#[derive(Debug)]
pub struct AlignedBuf {
    vec: Vec<u8>,
    offset: usize,
    len: usize,
}

impl AlignedBuf {
    /// Create a new zeroed buffer aligned to `BUFFER_ALIGNMENT` bytes.
    pub fn new(len: usize) -> Self {
        Self::new_with_alignment(len, BUFFER_ALIGNMENT)
    }

    /// Create a new zeroed buffer with a specific alignment.
    pub fn new_with_alignment(len: usize, align: usize) -> Self {
        let align = if align & (align - 1) != 0 {
            panic!("Alignment must be a power of two, got: {}", align);
        } else {
            align
        };
        let vec = vec![0u8; len + align];
        let ptr = vec.as_ptr() as usize;
        let offset = (align - (ptr % align)) % align;
        AlignedBuf { vec, offset, len }
    }

    pub fn as_ptr(&self) -> *const u8 {
        unsafe { self.vec.as_ptr().add(self.offset) }
    }

    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        unsafe { self.vec.as_mut_ptr().add(self.offset) }
    }

    pub fn as_slice(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.as_ptr(), self.len) }
    }

    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        unsafe { slice::from_raw_parts_mut(self.as_mut_ptr(), self.len) }
    }

    pub fn len(&self) -> usize {
        self.len
    }
}

impl Clone for AlignedBuf {
    fn clone(&self) -> Self {
        let mut new = AlignedBuf::new_with_alignment(self.len, BUFFER_ALIGNMENT);
        new.as_mut_slice().copy_from_slice(self.as_slice());
        new
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_aligned_buffer() {
        let len = 1024;
        let mut buf = AlignedBuf::new(len);
        assert_eq!(buf.len(), len);
        assert_eq!(buf.as_slice().len(), len);
        assert_eq!(buf.as_mut_slice().len(), len);
        assert_eq!(buf.as_ptr() as usize % BUFFER_ALIGNMENT, 0);
        assert_eq!(buf.as_mut_ptr() as usize % BUFFER_ALIGNMENT, 0);
    }

    #[test]
    fn test_8kb_aligned_buffer() {
        let len = 8192;
        let mut buf = AlignedBuf::new_with_alignment(len, 8192);
        assert_eq!(buf.len(), len);
        assert_eq!(buf.as_slice().len(), len);
        assert_eq!(buf.as_mut_slice().len(), len);
        assert_eq!(buf.as_ptr() as usize % 8192, 0);
        assert_eq!(buf.as_mut_ptr() as usize % 8192, 0);
    }

    #[test]
    #[should_panic(expected = "Alignment must be a power of two")]
    fn test_invalid_alignment() {
        let _ = AlignedBuf::new_with_alignment(1024, 3000);
    }
}
