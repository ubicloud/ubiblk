use crate::vhost_backend::SECTOR_SIZE;
use std::{mem::MaybeUninit, ptr};

pub const UBI_MAGIC_SIZE: usize = 9;
pub const UBI_MAGIC: &[u8] = b"BDEV_UBI\0"; // 9 bytes

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
    // bit 2: no source data
    // bits 3-7: reserved
    pub stripe_headers: Vec<u8>,
}

impl UbiMetadata {
    pub const HEADER_SIZE: usize = UBI_MAGIC_SIZE + 2 + 2 + 1;

    pub fn metadata_size(&self) -> usize {
        SECTOR_SIZE + self.stripe_headers.len()
    }

    pub fn stripe_size(&self) -> u64 {
        1u64 << self.stripe_sector_count_shift
    }

    pub fn stripe_count(&self) -> u64 {
        self.stripe_headers.len() as u64
    }

    #[cfg(test)]
    pub fn stripe_headers_offset(&self, stripe_id: usize) -> usize {
        SECTOR_SIZE + stripe_id
    }

    #[cfg(test)]
    pub fn stripe_header(&self, stripe_id: usize) -> u8 {
        self.stripe_headers[stripe_id]
    }

    #[cfg(test)]
    pub fn set_stripe_header(&mut self, stripe_id: usize, value: u8) {
        self.stripe_headers[stripe_id] = value;
    }

    pub fn new(
        stripe_sector_count_shift: u8,
        base_stripe_count: usize,
        image_stripe_count: usize,
    ) -> Box<Self> {
        let mut metadata: Box<MaybeUninit<Self>> = Box::new_uninit();

        let headers = (0..base_stripe_count)
            .map(|i| if i < image_stripe_count { 0 } else { 1 << 2 })
            .collect::<Vec<_>>();

        unsafe {
            let md = metadata.assume_init_mut();

            md.magic.copy_from_slice(UBI_MAGIC);
            md.version_major.copy_from_slice(&[0; 2]);
            md.version_minor.copy_from_slice(&[0; 2]);
            md.stripe_sector_count_shift = stripe_sector_count_shift;

            ptr::write(&mut md.stripe_headers, headers);

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

        let stripe_count = buf.len() - SECTOR_SIZE;

        // initialize all headers to zero and then copy the provided stripe data
        let mut stripe_headers = vec![0u8; stripe_count];

        // copy any stripe headers that are actually present in `buf`
        unsafe {
            let dst = stripe_headers.as_mut_ptr();
            let src = buf.as_ptr().add(SECTOR_SIZE);
            ptr::copy_nonoverlapping(src, dst, stripe_count);
        }

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

            // Copy the stripe headers starting from sector 1.
            let stripes_ptr = self.stripe_headers.as_ptr();
            ptr::copy_nonoverlapping(stripes_ptr, dst.add(SECTOR_SIZE), stripe_count);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vhost_backend::SECTOR_SIZE;

    #[test]
    fn test_ubi_metadata_serialization() {
        const STRIPES: usize = 20;
        let mut metadata = UbiMetadata::new(9, STRIPES, STRIPES);

        for i in 0..STRIPES {
            metadata.set_stripe_header(i, (i * 2) as u8);
        }

        let metadata_size: usize = metadata.metadata_size();
        let buf_size: usize = metadata_size.div_ceil(SECTOR_SIZE) * SECTOR_SIZE;

        let mut buf = vec![0u8; buf_size];
        metadata.write_to_buf(&mut buf[..metadata_size]);

        let loaded_metadata = UbiMetadata::from_bytes(&buf[..metadata_size]);

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

    #[test]
    fn new_marks_stripes_past_image_as_no_source() {
        let metadata = UbiMetadata::new(9, 10, 4);
        for i in 0..4 {
            assert_eq!(metadata.stripe_header(i), 0);
        }
        for i in 4..10 {
            assert_eq!(metadata.stripe_header(i), 1 << 2);
        }
    }
}
