use std::mem::MaybeUninit;

pub const UBI_MAGIC_SIZE: usize = 9;
pub const UBI_MAX_STRIPES: usize = 2 * 1024 * 1024;
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
    pub stripe_headers: [u8; UBI_MAX_STRIPES],
}

impl UbiMetadata {
    #[cfg(test)]
    pub fn stripe_headers_offset(&self, stripe_id: usize) -> usize {
        stripe_id + UBI_MAGIC_SIZE + 5
    }

    pub fn new(stripe_sector_count_shift: u8) -> Box<Self> {
        let mut metadata: Box<MaybeUninit<Self>> = Box::new_uninit();
        unsafe {
            let metadata_ptr = metadata.assume_init_mut();
            metadata_ptr.magic.copy_from_slice(UBI_MAGIC);
            metadata_ptr.version_major.copy_from_slice(&[0, 0]);
            metadata_ptr.version_minor.copy_from_slice(&[0, 0]);
            metadata_ptr.stripe_sector_count_shift = stripe_sector_count_shift;
            metadata_ptr.stripe_headers.fill(0);
        }
        unsafe { metadata.assume_init() }
    }
}
