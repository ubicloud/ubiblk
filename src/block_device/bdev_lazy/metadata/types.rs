use crate::vhost_backend::SECTOR_SIZE;

pub const UBI_MAGIC_SIZE: usize = 9;
pub const UBI_MAGIC: &[u8] = b"BDEV_UBI\0"; // 9 bytes
pub const STRIPE_FETCHED_MASK: u8 = 1 << 0;
pub const STRIPE_WRITTEN_MASK: u8 = 1 << 1;
pub const STRIPE_NO_SOURCE_MASK: u8 = 1 << 2;

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
        let headers = (0..base_stripe_count)
            .map(|i| {
                if i < image_stripe_count {
                    0
                } else {
                    STRIPE_NO_SOURCE_MASK
                }
            })
            .collect::<Vec<_>>();

        let mut magic = [0u8; UBI_MAGIC_SIZE];
        magic.copy_from_slice(UBI_MAGIC);

        Box::new(UbiMetadata {
            magic,
            version_major: [0; 2],
            version_minor: [0; 2],
            stripe_sector_count_shift,
            stripe_headers: headers,
        })
    }

    pub fn new_from_remote(
        stripe_sector_count_shift: u8,
        base_stripe_count: usize,
        remote_metadata: &UbiMetadata,
    ) -> Box<Self> {
        let headers = (0..base_stripe_count)
            .map(|i| {
                // The number of stripe headers in remote_metadata represents the stripe count
                // of the remote image. Each header corresponds to one stripe in the remote device.
                if i < remote_metadata.stripe_headers.len() {
                    // Check if stripe is written on remote
                    if remote_metadata.stripe_headers[i] & STRIPE_WRITTEN_MASK != 0 {
                        0 // Has source (written on remote)
                    } else {
                        STRIPE_NO_SOURCE_MASK // No source (unwritten on remote)
                    }
                } else {
                    STRIPE_NO_SOURCE_MASK // Beyond remote image size
                }
            })
            .collect::<Vec<_>>();

        let mut magic = [0u8; UBI_MAGIC_SIZE];
        magic.copy_from_slice(UBI_MAGIC);

        Box::new(UbiMetadata {
            magic,
            version_major: [0; 2],
            version_minor: [0; 2],
            stripe_sector_count_shift,
            stripe_headers: headers,
        })
    }

    pub fn from_bytes(buf: &[u8]) -> Box<Self> {
        assert!(
            buf.len() >= SECTOR_SIZE,
            "buffer too small: {} < {}",
            buf.len(),
            SECTOR_SIZE
        );
        // copy the fixed‐size header fields
        let mut magic = [0u8; UBI_MAGIC_SIZE];
        magic.copy_from_slice(&buf[0..UBI_MAGIC_SIZE]);

        let mut version_major = [0u8; 2];
        version_major.copy_from_slice(&buf[UBI_MAGIC_SIZE..UBI_MAGIC_SIZE + 2]);

        let mut version_minor = [0u8; 2];
        version_minor.copy_from_slice(&buf[UBI_MAGIC_SIZE + 2..UBI_MAGIC_SIZE + 4]);

        let stripe_sector_count_shift = buf[UBI_MAGIC_SIZE + 4];

        let stripe_count = buf.len() - SECTOR_SIZE;

        let mut stripe_headers = vec![0u8; stripe_count];
        stripe_headers.copy_from_slice(&buf[SECTOR_SIZE..]);

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

        let stripe_count = self.stripe_headers.len();

        let mut header = [0u8; Self::HEADER_SIZE];
        header[..UBI_MAGIC_SIZE].copy_from_slice(&self.magic);
        header[UBI_MAGIC_SIZE..UBI_MAGIC_SIZE + 2].copy_from_slice(&self.version_major);
        header[UBI_MAGIC_SIZE + 2..UBI_MAGIC_SIZE + 4].copy_from_slice(&self.version_minor);
        header[UBI_MAGIC_SIZE + 4] = self.stripe_sector_count_shift;
        buf[..Self::HEADER_SIZE].copy_from_slice(&header);

        buf[SECTOR_SIZE..SECTOR_SIZE + stripe_count].copy_from_slice(&self.stripe_headers);
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
            assert_eq!(metadata.stripe_header(i), STRIPE_NO_SOURCE_MASK);
        }
    }

    #[test]
    fn new_from_remote_marks_unwritten_stripes_as_no_source() {
        // Create a remote metadata with some stripes written
        let mut remote_metadata = UbiMetadata::new(9, 8, 8);
        // Mark stripes 0, 2, 4 as written
        remote_metadata.set_stripe_header(0, STRIPE_WRITTEN_MASK);
        remote_metadata.set_stripe_header(2, STRIPE_WRITTEN_MASK);
        remote_metadata.set_stripe_header(4, STRIPE_WRITTEN_MASK);

        // Create new metadata from remote with 10 total stripes
        let metadata = UbiMetadata::new_from_remote(9, 10, &remote_metadata);

        // Written stripes should have source (header = 0)
        assert_eq!(
            metadata.stripe_header(0),
            0,
            "Written stripe 0 should have source"
        );
        assert_eq!(
            metadata.stripe_header(2),
            0,
            "Written stripe 2 should have source"
        );
        assert_eq!(
            metadata.stripe_header(4),
            0,
            "Written stripe 4 should have source"
        );

        // Unwritten stripes should be marked as no source (bit 2 set)
        assert_eq!(
            metadata.stripe_header(1),
            STRIPE_NO_SOURCE_MASK,
            "Unwritten stripe 1 should have no source"
        );
        assert_eq!(
            metadata.stripe_header(3),
            STRIPE_NO_SOURCE_MASK,
            "Unwritten stripe 3 should have no source"
        );
        assert_eq!(
            metadata.stripe_header(5),
            STRIPE_NO_SOURCE_MASK,
            "Unwritten stripe 5 should have no source"
        );

        // Stripes beyond remote image should be marked as no source
        assert_eq!(
            metadata.stripe_header(8),
            STRIPE_NO_SOURCE_MASK,
            "Stripe 8 beyond remote should have no source"
        );
        assert_eq!(
            metadata.stripe_header(9),
            STRIPE_NO_SOURCE_MASK,
            "Stripe 9 beyond remote should have no source"
        );
    }
}
