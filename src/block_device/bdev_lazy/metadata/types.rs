use std::{
    mem::MaybeUninit,
    ptr,
    sync::{atomic::AtomicU8, Arc},
};

#[cfg(test)]
use std::sync::atomic::Ordering;

use static_assertions::const_assert;

pub const UBI_MAGIC_SIZE: usize = 9;
pub const UBI_MAGIC: &[u8] = b"BDEV_UBI\0"; // 9 bytes

// Ensure AtomicU8 has the same in-memory layout as u8 so we can copy headers
// using raw byte pointers.
const_assert!(std::mem::size_of::<AtomicU8>() == std::mem::size_of::<u8>());

#[repr(C)]
#[derive(Debug, Clone)]
pub struct UbiMetadata {
    pub magic: [u8; UBI_MAGIC_SIZE],

    // Little-endian encoded u16 values as byte arrays
    pub version_major: [u8; 2],
    pub version_minor: [u8; 2],

    pub stripe_sector_count_shift: u8,

    // bit 0: fetched or not
    // bit 1: written or not
    pub stripe_headers: Arc<Vec<AtomicU8>>,
}

impl UbiMetadata {
    pub const HEADER_SIZE: usize = UBI_MAGIC_SIZE + 2 + 2 + 1;

    pub fn metadata_size(&self) -> usize {
        Self::HEADER_SIZE + self.stripe_headers.len()
    }

    pub fn stripe_size(&self) -> u64 {
        1u64 << self.stripe_sector_count_shift
    }

    pub fn stripe_count(&self) -> u64 {
        self.stripe_headers.len() as u64
    }

    #[cfg(test)]
    pub fn stripe_headers_offset(&self, stripe_id: usize) -> usize {
        stripe_id + Self::HEADER_SIZE
    }

    #[cfg(test)]
    pub fn stripe_header(&self, stripe_id: usize) -> u8 {
        self.stripe_headers[stripe_id].load(Ordering::SeqCst)
    }

    #[cfg(test)]
    pub fn set_stripe_header(&self, stripe_id: usize, value: u8) {
        self.stripe_headers[stripe_id].store(value, Ordering::SeqCst);
    }

    pub fn new(stripe_sector_count_shift: u8, stripe_count: usize) -> Box<Self> {
        let mut metadata: Box<MaybeUninit<Self>> = Box::new_uninit();

        let headers = (0..stripe_count)
            .map(|_| AtomicU8::new(0))
            .collect::<Vec<_>>();

        unsafe {
            let md = metadata.assume_init_mut();

            md.magic.copy_from_slice(UBI_MAGIC);
            md.version_major.copy_from_slice(&[0; 2]);
            md.version_minor.copy_from_slice(&[0; 2]);
            md.stripe_sector_count_shift = stripe_sector_count_shift;

            ptr::write(&mut md.stripe_headers, Arc::new(headers));

            metadata.assume_init()
        }
    }

    pub fn from_bytes(buf: &[u8]) -> Box<Self> {
        // copy the fixed‐size header fields
        let mut magic = [0u8; UBI_MAGIC_SIZE];
        magic.copy_from_slice(&buf[0..UBI_MAGIC_SIZE]);

        let mut version_major = [0u8; 2];
        version_major.copy_from_slice(&buf[UBI_MAGIC_SIZE..UBI_MAGIC_SIZE + 2]);

        let mut version_minor = [0u8; 2];
        version_minor.copy_from_slice(&buf[UBI_MAGIC_SIZE + 2..UBI_MAGIC_SIZE + 4]);

        let stripe_sector_count_shift = buf[UBI_MAGIC_SIZE + 4];

        let stripe_count = buf.len() - Self::HEADER_SIZE;

        // initialize all headers to zero and then copy the provided stripe data
        let mut stripe_headers = (0..stripe_count)
            .map(|_| AtomicU8::new(0))
            .collect::<Vec<_>>();

        // copy any stripe headers that are actually present in `buf`
        unsafe {
            let dst = stripe_headers.as_mut_ptr() as *mut u8;
            let src = buf.as_ptr().add(Self::HEADER_SIZE);
            ptr::copy_nonoverlapping(src, dst, stripe_count);
        }
        let stripe_headers = Arc::new(stripe_headers);

        // finally, box up the new struct
        Box::new(UbiMetadata {
            magic,
            version_major,
            version_minor,
            stripe_sector_count_shift,
            stripe_headers,
        })
    }

    /// Serialize `self` into the given buffer
    pub fn write_to_buf(&self, buf: &mut [u8]) {
        let total_len: usize = self.metadata_size();
        assert!(
            buf.len() >= total_len,
            "buffer too small: {} < {}",
            buf.len(),
            total_len
        );

        let dst = buf.as_mut_ptr();
        let stripe_count = self.stripe_headers.len();

        unsafe {
            // build and copy the header
            let mut header = [0u8; Self::HEADER_SIZE];
            header[..UBI_MAGIC_SIZE].copy_from_slice(&self.magic);
            header[UBI_MAGIC_SIZE..UBI_MAGIC_SIZE + 2].copy_from_slice(&self.version_major);
            header[UBI_MAGIC_SIZE + 2..UBI_MAGIC_SIZE + 4].copy_from_slice(&self.version_minor);
            header[UBI_MAGIC_SIZE + 4] = self.stripe_sector_count_shift;
            ptr::copy_nonoverlapping(header.as_ptr(), dst, Self::HEADER_SIZE);

            // Copy the stripe headers.
            let stripes_ptr = self.stripe_headers.as_ptr() as *const u8;
            ptr::copy_nonoverlapping(stripes_ptr, dst.add(Self::HEADER_SIZE), stripe_count);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ubi_metadata_serialization() {
        const STRIPES: usize = 20;
        let metadata = UbiMetadata::new(9, STRIPES);

        for i in 0..STRIPES {
            metadata.set_stripe_header(i, (i * 2) as u8);
        }

        let metadata_size: usize = metadata.metadata_size();
        let buf_size: usize = metadata_size.div_ceil(512) * 512;

        let mut buf = vec![0u8; buf_size];
        metadata.write_to_buf(&mut buf);

        let loaded_metadata = UbiMetadata::from_bytes(&buf);

        assert_eq!(loaded_metadata.magic, metadata.magic);
        assert_eq!(loaded_metadata.version_major, metadata.version_major);
        assert_eq!(loaded_metadata.version_minor, metadata.version_minor);
        assert_eq!(
            loaded_metadata.stripe_sector_count_shift,
            metadata.stripe_sector_count_shift
        );

        for i in 0..STRIPES {
            assert_eq!(loaded_metadata.stripe_header(i), metadata.stripe_header(i));
        }
    }
}
