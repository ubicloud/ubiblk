use ubiblk_macros::error_context;

use crate::{backends::SECTOR_SIZE, stripe_source::StripeSource, Result};

pub const UBI_MAGIC_SIZE: usize = 9;
pub const UBI_MAGIC: &[u8] = b"BDEV_UBI\0"; // 9 bytes
pub const METADATA_VERSION_MAJOR: u16 = 2;
pub const METADATA_VERSION_MINOR: u16 = 1;

pub const CRC32_SIZE: usize = 4;
pub const STRIPE_HEADERS_PER_SECTOR: usize = SECTOR_SIZE - CRC32_SIZE; // 508
pub const STRIPE_COUNT_OFFSET: usize = UBI_MAGIC_SIZE + 2 + 2 + 1;
const MAX_STRIPE_SECTOR_COUNT_SHIFT: u8 = 17; // Max stripe size of 2^17 sectors = 64 MiB

/// Flags used in stripe headers within UbiMetadata
pub mod metadata_flags {
    /// Stripe data has been fetched from the stripe source and is present in
    /// the disk device.
    pub const FETCHED: u8 = 1 << 0;
    /// Stripe has been written to the disk device.
    pub const WRITTEN: u8 = 1 << 1;
    /// Stripe exists in the base source. Such a stripe might have been fetched
    /// already, or not yet.
    pub const HAS_SOURCE: u8 = 1 << 2;
    /// Stripe is locked by an active operation (snapshot/rekey). Set at
    /// begin_operating, cleared per-stripe as processing completes. Used for
    /// crash recovery: on startup, stripes with this bit still set must be
    /// re-processed.
    pub const OPS_LOCKED: u8 = 1 << 3;
}

/// Operation phase values stored in sector 0 at offset 18.
pub mod ops_phase {
    /// No operation in progress.
    pub const NORMAL: u8 = 0;
    /// Operation is active, stripes are being processed.
    /// Stalling (phase 1) is never persisted — a crash during stalling
    /// reverts to Normal since no on-disk state was written.
    pub const OPERATING: u8 = 2;
}

/// Operation type values stored in sector 0 at offset 19.
pub mod ops_type {
    pub const NONE: u8 = 0;
    pub const SNAPSHOT: u8 = 1;
    pub const REKEY: u8 = 2;
}

/// Offsets within sector 0 for operation state (v2.1 extension).
pub const OPS_PHASE_OFFSET: usize = 18;
pub const OPS_TYPE_OFFSET: usize = 19;
pub const OPS_ID_OFFSET: usize = 20;
pub const OPS_STAGING_PATH_OFFSET: usize = 28;
pub const OPS_STAGING_PATH_MAX: usize = 256;

/// Recovery information extracted from metadata when ops_phase == OPERATING.
#[derive(Debug, Clone)]
pub struct OpsRecoveryInfo {
    pub ops_type: u8,
    pub ops_id: u64,
    pub staging_path: Option<String>,
    pub locked_stripes: Vec<usize>,
}

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
    // bit 2: exists in source
    // bit 3: ops_locked (active operation lock)
    // bits 4-7: reserved
    pub stripe_headers: Vec<u8>,

    // Operation state (v2.1 extension, stored in sector 0 padding area)
    pub ops_phase: u8,
    pub ops_type: u8,
    pub ops_id: u64,
    pub ops_staging_path: Option<String>,
}

/// Compute CRC32 over a slice and return as little-endian bytes.
fn compute_sector_crc32(data: &[u8]) -> [u8; CRC32_SIZE] {
    crc32fast::hash(data).to_le_bytes()
}

/// Write a single metadata sector into `sector_buf`. `contents` is the data
/// without the CRC32 and must be at most 508 bytes.
pub(crate) fn write_sector_with_crc32(sector_buf: &mut [u8], contents: &[u8]) {
    debug_assert!(sector_buf.len().is_multiple_of(SECTOR_SIZE));
    debug_assert!(contents.len() <= SECTOR_SIZE - CRC32_SIZE);

    sector_buf.fill(0);
    sector_buf[..contents.len()].copy_from_slice(contents);

    let crc = compute_sector_crc32(&sector_buf[..SECTOR_SIZE - CRC32_SIZE]);
    sector_buf[SECTOR_SIZE - CRC32_SIZE..SECTOR_SIZE].copy_from_slice(&crc);
}

/// Verify CRC32 for a metadata sector.
fn sector_crc32_is_valid(sector_buf: &[u8]) -> bool {
    debug_assert!(sector_buf.len().is_multiple_of(SECTOR_SIZE));
    let computed_crc = compute_sector_crc32(&sector_buf[..SECTOR_SIZE - CRC32_SIZE]);
    sector_buf[SECTOR_SIZE - CRC32_SIZE..SECTOR_SIZE] == computed_crc
}

impl UbiMetadata {
    // V2 header layout in sector 0:
    //    [0..8]     magic
    //    [9..10]    version_major: u16 LE (now 2)
    //    [11.12]    version_minor: u16 LE (0)
    //    [13]       stripe_sector_count_shift: u8
    //    [14..17]   stripe_count: u32 LE (new field)
    //    [18..507]  padding
    //    [508..511] CRC32 LE over bytes [0..507]
    pub const HEADER_SIZE: usize = UBI_MAGIC_SIZE + 2 + 2 + 1 + 4; // 18

    /// Number of metadata sectors needed for stripe headers (excluding the
    /// header sector 0).
    pub fn stripe_header_sector_count(&self) -> usize {
        self.stripe_headers
            .len()
            .div_ceil(STRIPE_HEADERS_PER_SECTOR)
    }

    pub fn metadata_size(&self) -> usize {
        // Sector 0 (header) + N sectors for stripe headers (each with CRC32)
        SECTOR_SIZE + self.stripe_header_sector_count() * SECTOR_SIZE
    }

    /// Which metadata sector (1-based) contains the given stripe_id.
    pub fn stripe_id_to_sector(stripe_id: usize) -> u64 {
        (stripe_id / STRIPE_HEADERS_PER_SECTOR + 1) as u64
    }

    /// Which group index (0-based) contains the given stripe_id.
    pub fn stripe_id_to_group(stripe_id: usize) -> usize {
        stripe_id / STRIPE_HEADERS_PER_SECTOR
    }

    pub fn stripe_sector_count(&self) -> u64 {
        1u64 << self.stripe_sector_count_shift
    }

    pub fn stripe_size(&self) -> usize {
        (self.stripe_sector_count() as usize) * SECTOR_SIZE
    }

    pub fn stripe_count(&self) -> u64 {
        self.stripe_headers.len() as u64
    }

    pub fn version_major_u16(&self) -> u16 {
        u16::from_le_bytes(self.version_major)
    }

    pub fn version_minor_u16(&self) -> u16 {
        u16::from_le_bytes(self.version_minor)
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
                    metadata_flags::HAS_SOURCE
                } else {
                    0
                }
            })
            .collect::<Vec<_>>();

        let mut magic = [0u8; UBI_MAGIC_SIZE];
        magic.copy_from_slice(UBI_MAGIC);

        Box::new(UbiMetadata {
            magic,
            version_major: METADATA_VERSION_MAJOR.to_le_bytes(),
            version_minor: METADATA_VERSION_MINOR.to_le_bytes(),
            stripe_sector_count_shift,
            stripe_headers: headers,
            ops_phase: ops_phase::NORMAL,
            ops_type: ops_type::NONE,
            ops_id: 0,
            ops_staging_path: None,
        })
    }

    pub fn new_from_stripe_source(
        stripe_sector_count_shift: u8,
        base_stripe_count: usize,
        stripe_source: &dyn StripeSource,
    ) -> Box<Self> {
        let headers = (0..base_stripe_count)
            .map(|i| {
                if stripe_source.has_stripe(i) {
                    metadata_flags::HAS_SOURCE
                } else {
                    0
                }
            })
            .collect::<Vec<_>>();

        let mut magic = [0u8; UBI_MAGIC_SIZE];
        magic.copy_from_slice(UBI_MAGIC);

        Box::new(UbiMetadata {
            magic,
            version_major: METADATA_VERSION_MAJOR.to_le_bytes(),
            version_minor: METADATA_VERSION_MINOR.to_le_bytes(),
            stripe_sector_count_shift,
            stripe_headers: headers,
            ops_phase: ops_phase::NORMAL,
            ops_type: ops_type::NONE,
            ops_id: 0,
            ops_staging_path: None,
        })
    }

    /// Deserialize and validate metadata from a byte buffer.
    #[error_context("Failed to deserialize UBI metadata from buffer")]
    pub fn from_bytes(buf: &[u8]) -> Result<Box<Self>> {
        if buf.len() < SECTOR_SIZE {
            return Err(crate::ubiblk_error!(MetadataError {
                description: format!("Metadata buffer too small: {} < {}", buf.len(), SECTOR_SIZE),
            }));
        }
        if !buf.len().is_multiple_of(SECTOR_SIZE) {
            return Err(crate::ubiblk_error!(MetadataError {
                description: format!(
                    "Metadata buffer size must be a multiple of sector size {}: found {}",
                    SECTOR_SIZE,
                    buf.len()
                ),
            }));
        }

        let header_crc_valid = sector_crc32_is_valid(&buf[..SECTOR_SIZE]);
        if !header_crc_valid {
            return Err(crate::ubiblk_error!(MetadataError {
                description: "Metadata header CRC32 mismatch".to_string(),
            }));
        }

        let mut magic = [0u8; UBI_MAGIC_SIZE];
        magic.copy_from_slice(&buf[0..UBI_MAGIC_SIZE]);
        if magic != *UBI_MAGIC {
            return Err(crate::ubiblk_error!(MetadataError {
                description: format!(
                    "Metadata magic mismatch! Expected: {:?}, Found: {:?}",
                    UBI_MAGIC, magic
                ),
            }));
        }

        let mut version_major = [0u8; 2];
        version_major.copy_from_slice(&buf[UBI_MAGIC_SIZE..UBI_MAGIC_SIZE + 2]);

        let mut version_minor = [0u8; 2];
        version_minor.copy_from_slice(&buf[UBI_MAGIC_SIZE + 2..UBI_MAGIC_SIZE + 4]);
        let found_minor = u16::from_le_bytes(version_minor);
        if version_major != METADATA_VERSION_MAJOR.to_le_bytes()
            || found_minor > METADATA_VERSION_MINOR
        {
            return Err(crate::ubiblk_error!(MetadataError {
                description: format!(
                    "Metadata version mismatch! Expected: {}.0-{}.{}, Found: {}.{}",
                    METADATA_VERSION_MAJOR,
                    METADATA_VERSION_MAJOR,
                    METADATA_VERSION_MINOR,
                    u16::from_le_bytes(version_major),
                    found_minor
                ),
            }));
        }

        let stripe_sector_count_shift = buf[UBI_MAGIC_SIZE + 4];
        if stripe_sector_count_shift > MAX_STRIPE_SECTOR_COUNT_SHIFT {
            return Err(crate::ubiblk_error!(MetadataError {
                description: format!(
                    "Metadata stripe sector count shift {stripe_sector_count_shift} exceeds maximum {MAX_STRIPE_SECTOR_COUNT_SHIFT}"
                ),
            }));
        }

        // Read stripe count from header (u32 LE at offset 14)
        let stripe_count = u32::from_le_bytes([
            buf[STRIPE_COUNT_OFFSET],
            buf[STRIPE_COUNT_OFFSET + 1],
            buf[STRIPE_COUNT_OFFSET + 2],
            buf[STRIPE_COUNT_OFFSET + 3],
        ]) as usize;

        let data_sectors_max = (buf.len() - SECTOR_SIZE) / SECTOR_SIZE;
        let max_stripe_count = data_sectors_max * STRIPE_HEADERS_PER_SECTOR;
        if stripe_count > max_stripe_count {
            return Err(crate::ubiblk_error!(MetadataError {
                description: format!(
                    "Metadata stripe count {stripe_count} exceeds buffer capacity {max_stripe_count}"
                ),
            }));
        }

        // Parse only the sectors needed for stripe headers (ignore trailing device sectors).
        let data_sectors = stripe_count.div_ceil(STRIPE_HEADERS_PER_SECTOR);
        let mut all_headers = Vec::new();

        for group in 0..data_sectors {
            let sector_start = SECTOR_SIZE + group * SECTOR_SIZE;
            assert!(sector_start + SECTOR_SIZE <= buf.len());

            let sector_data = &buf[sector_start..sector_start + SECTOR_SIZE];
            let header_data = &sector_data[..STRIPE_HEADERS_PER_SECTOR];
            if !sector_crc32_is_valid(sector_data) {
                return Err(crate::ubiblk_error!(MetadataError {
                    description: format!("CRC32 mismatch in metadata sector group {group}"),
                }));
            }

            all_headers.extend_from_slice(header_data);
        }

        // Truncate to actual stripe count (sectors may be zero-padded)
        assert!(all_headers.len() >= stripe_count);
        all_headers.truncate(stripe_count);

        // Parse operation state from sector 0 extension area (v2.1+).
        // For v2.0 metadata these bytes are zero (padding), so ops_phase=0
        // (NORMAL) which is the correct default.
        let ops_phase_val = buf[OPS_PHASE_OFFSET];
        let ops_type_val = buf[OPS_TYPE_OFFSET];
        let ops_id_val = u64::from_le_bytes([
            buf[OPS_ID_OFFSET],
            buf[OPS_ID_OFFSET + 1],
            buf[OPS_ID_OFFSET + 2],
            buf[OPS_ID_OFFSET + 3],
            buf[OPS_ID_OFFSET + 4],
            buf[OPS_ID_OFFSET + 5],
            buf[OPS_ID_OFFSET + 6],
            buf[OPS_ID_OFFSET + 7],
        ]);
        let ops_staging_path_val = {
            let path_bytes =
                &buf[OPS_STAGING_PATH_OFFSET..OPS_STAGING_PATH_OFFSET + OPS_STAGING_PATH_MAX];
            let nul_pos = path_bytes
                .iter()
                .position(|&b| b == 0)
                .unwrap_or(OPS_STAGING_PATH_MAX);
            if nul_pos > 0 {
                String::from_utf8(path_bytes[..nul_pos].to_vec()).ok()
            } else {
                None
            }
        };

        Ok(Box::new(UbiMetadata {
            magic,
            version_major,
            version_minor,
            stripe_sector_count_shift,
            stripe_headers: all_headers,
            ops_phase: ops_phase_val,
            ops_type: ops_type_val,
            ops_id: ops_id_val,
            ops_staging_path: ops_staging_path_val,
        }))
    }

    /// Serialize `self` into the given buffer.
    #[error_context("Failed to serialize UBI metadata into buffer")]
    pub fn write_to_buf(&self, buf: &mut [u8]) -> Result<()> {
        let total_len: usize = self.metadata_size();
        if buf.len() < total_len {
            return Err(crate::ubiblk_error!(MetadataError {
                description: format!("Metadata buffer too small: {} < {}", buf.len(), total_len),
            }));
        }

        // Write header sector (sector 0).
        // Build the full sector 0 content area (508 bytes, before CRC32).
        let mut sector0_content = [0u8; SECTOR_SIZE - CRC32_SIZE];
        sector0_content[..UBI_MAGIC_SIZE].copy_from_slice(&self.magic);
        sector0_content[UBI_MAGIC_SIZE..UBI_MAGIC_SIZE + 2].copy_from_slice(&self.version_major);
        sector0_content[UBI_MAGIC_SIZE + 2..UBI_MAGIC_SIZE + 4]
            .copy_from_slice(&self.version_minor);
        sector0_content[UBI_MAGIC_SIZE + 4] = self.stripe_sector_count_shift;

        let stripe_count = self.stripe_headers.len();
        let stripe_count_bytes = u32::try_from(stripe_count)
            .map_err(|e| {
                crate::ubiblk_error!(MetadataError {
                    description: format!("Stripe count {stripe_count} exceeds u32 max: {e}"),
                })
            })?
            .to_le_bytes();
        sector0_content[STRIPE_COUNT_OFFSET..STRIPE_COUNT_OFFSET + 4]
            .copy_from_slice(&stripe_count_bytes);

        // Operation state fields (v2.1 extension)
        sector0_content[OPS_PHASE_OFFSET] = self.ops_phase;
        sector0_content[OPS_TYPE_OFFSET] = self.ops_type;
        sector0_content[OPS_ID_OFFSET..OPS_ID_OFFSET + 8]
            .copy_from_slice(&self.ops_id.to_le_bytes());
        if let Some(ref path) = self.ops_staging_path {
            let path_bytes = path.as_bytes();
            let len = path_bytes.len().min(OPS_STAGING_PATH_MAX - 1);
            sector0_content[OPS_STAGING_PATH_OFFSET..OPS_STAGING_PATH_OFFSET + len]
                .copy_from_slice(&path_bytes[..len]);
            // null terminator is already zero from initialization
        }

        // Write sector 0 with CRC32 (write_sector_with_crc32 expects the
        // content portion only; it zero-fills and appends CRC32).
        // Since sector0_content is exactly 508 bytes, pass it directly.
        buf[..SECTOR_SIZE].fill(0);
        buf[..sector0_content.len()].copy_from_slice(&sector0_content);
        let crc = crc32fast::hash(&buf[..SECTOR_SIZE - CRC32_SIZE]).to_le_bytes();
        buf[SECTOR_SIZE - CRC32_SIZE..SECTOR_SIZE].copy_from_slice(&crc);

        // Write stripe header sectors with CRC32
        let num_sectors = self.stripe_header_sector_count();
        for group in 0..num_sectors {
            let start = group * STRIPE_HEADERS_PER_SECTOR;
            let end = (start + STRIPE_HEADERS_PER_SECTOR).min(self.stripe_headers.len());
            let headers = &self.stripe_headers[start..end];

            let sector_start = SECTOR_SIZE + group * SECTOR_SIZE;
            assert!(sector_start + SECTOR_SIZE <= buf.len());
            write_sector_with_crc32(&mut buf[sector_start..sector_start + SECTOR_SIZE], headers);
        }
        Ok(())
    }

    /// Check if an operation was in progress when metadata was last written.
    /// Returns recovery info if ops_phase == OPERATING.
    pub fn ops_recovery_info(&self) -> Option<OpsRecoveryInfo> {
        if self.ops_phase != ops_phase::OPERATING {
            return None;
        }
        let locked_stripes = self
            .stripe_headers
            .iter()
            .enumerate()
            .filter(|(_, &h)| h & metadata_flags::OPS_LOCKED != 0)
            .map(|(i, _)| i)
            .collect();
        Some(OpsRecoveryInfo {
            ops_type: self.ops_type,
            ops_id: self.ops_id,
            staging_path: self.ops_staging_path.clone(),
            locked_stripes,
        })
    }

    /// Set operation state fields. Call before writing metadata to persist
    /// the operation phase transition.
    pub fn set_ops_state(
        &mut self,
        phase: u8,
        op_type: u8,
        op_id: u64,
        staging_path: Option<String>,
    ) {
        self.ops_phase = phase;
        self.ops_type = op_type;
        self.ops_id = op_id;
        self.ops_staging_path = staging_path;
    }

    /// Clear operation state, returning to normal.
    pub fn clear_ops_state(&mut self) {
        self.ops_phase = ops_phase::NORMAL;
        self.ops_type = ops_type::NONE;
        self.ops_id = 0;
        self.ops_staging_path = None;
    }

    /// Set the OPS_LOCKED bit on all stripes.
    pub fn set_all_ops_locked(&mut self) {
        for h in self.stripe_headers.iter_mut() {
            *h |= metadata_flags::OPS_LOCKED;
        }
    }

    /// Clear the OPS_LOCKED bit on a single stripe.
    pub fn clear_ops_locked(&mut self, stripe_id: usize) {
        self.stripe_headers[stripe_id] &= !metadata_flags::OPS_LOCKED;
    }

    pub fn has_fetched_all_stripes(&self) -> bool {
        self.stripe_headers.iter().all(|&header| {
            (header & metadata_flags::HAS_SOURCE) == 0 || (header & metadata_flags::FETCHED) != 0
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backends::SECTOR_SIZE;

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
        metadata
            .write_to_buf(&mut buf[..metadata_size])
            .expect("write to buffer");

        let loaded_metadata =
            UbiMetadata::from_bytes(&buf[..metadata_size]).expect("deserialize metadata");

        assert_eq!(loaded_metadata.magic, metadata.magic);
        assert_eq!(loaded_metadata.version_major, metadata.version_major);
        assert_eq!(loaded_metadata.version_minor, metadata.version_minor);
        assert_eq!(
            loaded_metadata.stripe_sector_count_shift,
            metadata.stripe_sector_count_shift
        );
        assert_eq!(loaded_metadata.stripe_headers.len(), STRIPES);

        for i in 0..STRIPES {
            assert_eq!(loaded_metadata.stripe_header(i), metadata.stripe_header(i));
        }
    }

    #[test]
    fn test_serialization_multiple_sectors() {
        // Use enough stripes to span multiple sectors (508 per sector)
        const STRIPES: usize = 1200;
        let mut metadata = UbiMetadata::new(9, STRIPES, STRIPES);

        for i in 0..STRIPES {
            metadata.set_stripe_header(i, (i % 7) as u8);
        }

        assert_eq!(metadata.stripe_header_sector_count(), 3); // ceil(1200/508) = 3

        let metadata_size = metadata.metadata_size();
        let buf_size = metadata_size.div_ceil(SECTOR_SIZE) * SECTOR_SIZE;
        let mut buf = vec![0u8; buf_size];
        metadata
            .write_to_buf(&mut buf[..metadata_size])
            .expect("write to buffer");

        let loaded_metadata =
            UbiMetadata::from_bytes(&buf[..metadata_size]).expect("deserialize metadata");
        assert_eq!(loaded_metadata.stripe_headers.len(), STRIPES);

        for i in 0..STRIPES {
            assert_eq!(loaded_metadata.stripe_header(i), metadata.stripe_header(i));
        }
    }

    #[test]
    fn test_crc32_detects_single_bit_flip() {
        const STRIPES: usize = 20;
        let metadata = UbiMetadata::new(9, STRIPES, STRIPES);

        let metadata_size = metadata.metadata_size();
        let mut buf = vec![0u8; metadata_size];
        metadata.write_to_buf(&mut buf).expect("write to buffer");

        // Flip a bit in the first stripe header sector (byte 0 of sector 1)
        buf[SECTOR_SIZE] ^= 0x01;

        let result = UbiMetadata::from_bytes(&buf);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("CRC32 mismatch in metadata sector group 0"));
    }

    #[test]
    fn test_crc32_detects_corruption_in_specific_sector() {
        const STRIPES: usize = 1200; // spans 3 sectors
        let metadata = UbiMetadata::new(9, STRIPES, STRIPES);

        let metadata_size = metadata.metadata_size();
        let mut buf = vec![0u8; metadata_size];
        metadata.write_to_buf(&mut buf).expect("write to buffer");

        // Corrupt only the second stripe header sector (group 1)
        buf[SECTOR_SIZE + SECTOR_SIZE + 100] ^= 0xFF;

        let result = UbiMetadata::from_bytes(&buf);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("CRC32 mismatch in metadata sector group 1"));
    }

    #[test]
    fn new_marks_stripes_past_image_as_not_in_source() {
        let metadata = UbiMetadata::new(9, 10, 4);
        for i in 0..4 {
            assert_eq!(metadata.stripe_header(i), metadata_flags::HAS_SOURCE);
        }
        for i in 4..10 {
            assert_eq!(metadata.stripe_header(i), 0);
        }
    }

    #[test]
    fn new_from_stripe_source_marks_stripes_correctly() {
        struct TestStripeSource {
            available_stripes: Vec<usize>,
        }

        impl StripeSource for TestStripeSource {
            fn request(
                &mut self,
                _stripe_id: usize,
                _buffer: crate::block_device::SharedBuffer,
            ) -> crate::Result<()> {
                unimplemented!()
            }

            fn poll(&mut self) -> Vec<(usize, bool)> {
                unimplemented!()
            }

            fn busy(&self) -> bool {
                unimplemented!()
            }

            fn sector_count(&self) -> u64 {
                unimplemented!()
            }

            fn has_stripe(&self, stripe_id: usize) -> bool {
                self.available_stripes.contains(&stripe_id)
            }
        }

        let stripe_source = TestStripeSource {
            available_stripes: vec![0, 2, 3, 6, 8],
        };

        let metadata = UbiMetadata::new_from_stripe_source(9, 10, &stripe_source);

        for i in 0..10 {
            let expected = if stripe_source.has_stripe(i) {
                metadata_flags::HAS_SOURCE
            } else {
                0
            };
            assert_eq!(metadata.stripe_header(i), expected);
        }
    }

    #[test]
    fn test_has_fetched_all_stripes() {
        let mut metadata = UbiMetadata::new(0, 10, 5);
        metadata.set_stripe_header(0, metadata_flags::FETCHED | metadata_flags::HAS_SOURCE);
        assert!(!metadata.has_fetched_all_stripes());
        metadata.set_stripe_header(1, metadata_flags::FETCHED | metadata_flags::HAS_SOURCE);
        assert!(!metadata.has_fetched_all_stripes());
        metadata.set_stripe_header(2, metadata_flags::FETCHED | metadata_flags::HAS_SOURCE);
        assert!(!metadata.has_fetched_all_stripes());
        metadata.set_stripe_header(3, 0); // No source
        assert!(!metadata.has_fetched_all_stripes());
        metadata.set_stripe_header(4, metadata_flags::FETCHED | metadata_flags::HAS_SOURCE);
        assert!(metadata.has_fetched_all_stripes());
    }

    #[test]
    fn test_stripe_id_to_sector() {
        assert_eq!(UbiMetadata::stripe_id_to_sector(0), 1);
        assert_eq!(UbiMetadata::stripe_id_to_sector(507), 1);
        assert_eq!(UbiMetadata::stripe_id_to_sector(508), 2);
        assert_eq!(UbiMetadata::stripe_id_to_sector(1015), 2);
        assert_eq!(UbiMetadata::stripe_id_to_sector(1016), 3);
    }

    #[test]
    fn test_metadata_size_v2() {
        // 20 stripes: 1 header sector + 1 data sector = 1024 bytes
        let metadata = UbiMetadata::new(9, 20, 20);
        assert_eq!(metadata.metadata_size(), 2 * SECTOR_SIZE);

        // 508 stripes: 1 header sector + 1 data sector = 1024 bytes
        let metadata = UbiMetadata::new(9, 508, 508);
        assert_eq!(metadata.metadata_size(), 2 * SECTOR_SIZE);

        // 509 stripes: 1 header sector + 2 data sectors = 1536 bytes
        let metadata = UbiMetadata::new(9, 509, 509);
        assert_eq!(metadata.metadata_size(), 3 * SECTOR_SIZE);
    }

    #[test]
    fn test_write_sector_with_crc32() {
        let headers = [0x04u8; 100]; // 100 stripes with HAS_SOURCE
        let mut sector_buf = [0u8; SECTOR_SIZE];
        write_sector_with_crc32(&mut sector_buf, &headers);

        // Headers should be at the start
        assert_eq!(&sector_buf[..100], &headers[..]);
        // Rest of header area should be zero-padded
        assert!(sector_buf[100..STRIPE_HEADERS_PER_SECTOR]
            .iter()
            .all(|&b| b == 0));
        // CRC32 should be non-zero (data is non-zero)
        let crc_bytes = &sector_buf[STRIPE_HEADERS_PER_SECTOR..SECTOR_SIZE];
        assert_ne!(
            crc_bytes,
            &[0, 0, 0, 0],
            "CRC32 should be non-zero for non-zero data"
        );
    }

    #[test]
    fn test_stripe_count_preserved_through_roundtrip() {
        // Small stripe counts should be preserved exactly
        for &count in &[1, 2, 16, 100, 507, 508, 509, 1016, 1200] {
            let metadata = UbiMetadata::new(9, count, count);
            let metadata_size = metadata.metadata_size();
            // try a size independent of count, as long as it fits within the
            // buffer
            assert!(metadata_size <= 4 * 1024 * 1024);
            let mut buf = vec![0u8; 4 * 1024 * 1024];
            metadata.write_to_buf(&mut buf).expect("write to buffer");

            let loaded_metadata = UbiMetadata::from_bytes(&buf).expect("deserialize metadata");
            assert_eq!(
                loaded_metadata.stripe_headers.len(),
                count,
                "stripe count {} should be preserved through roundtrip",
                count
            );
        }
    }

    #[test]
    fn test_crc32_detects_header_sector_corruption() {
        let metadata = UbiMetadata::new(9, 16, 16);
        let metadata_size = metadata.metadata_size();
        let mut buf = vec![0u8; metadata_size];
        metadata.write_to_buf(&mut buf).expect("write to buffer");

        // Corrupt sector 0 payload (without updating CRC)
        buf[1] ^= 0x01;

        let result = UbiMetadata::from_bytes(&buf);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Metadata header CRC32 mismatch"));
    }

    #[test]
    fn test_invalid_stripe_sector_count_shift() {
        let mut metadata = UbiMetadata::new(9, 16, 16);
        metadata.stripe_sector_count_shift = MAX_STRIPE_SECTOR_COUNT_SHIFT + 1;
        let metadata_size = metadata.metadata_size();
        let mut buf = vec![0u8; metadata_size];
        metadata.write_to_buf(&mut buf).expect("write to buffer");

        let result = UbiMetadata::from_bytes(&buf);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("stripe sector count shift"));
    }

    #[test]
    fn test_ops_state_roundtrip() {
        let mut metadata = UbiMetadata::new(9, 16, 16);
        metadata.set_ops_state(
            ops_phase::OPERATING,
            ops_type::SNAPSHOT,
            42,
            Some("/tmp/staging".to_string()),
        );
        metadata.set_all_ops_locked();

        let metadata_size = metadata.metadata_size();
        let mut buf = vec![0u8; metadata_size];
        metadata.write_to_buf(&mut buf).expect("write to buffer");

        let loaded = UbiMetadata::from_bytes(&buf).expect("deserialize");
        assert_eq!(loaded.ops_phase, ops_phase::OPERATING);
        assert_eq!(loaded.ops_type, ops_type::SNAPSHOT);
        assert_eq!(loaded.ops_id, 42);
        assert_eq!(loaded.ops_staging_path.as_deref(), Some("/tmp/staging"));

        // All stripes should have OPS_LOCKED set
        for i in 0..16 {
            assert_ne!(
                loaded.stripe_headers[i] & metadata_flags::OPS_LOCKED,
                0,
                "stripe {i} should have OPS_LOCKED"
            );
        }
    }

    #[test]
    fn test_ops_recovery_info() {
        let mut metadata = UbiMetadata::new(9, 8, 8);
        // No operation in progress
        assert!(metadata.ops_recovery_info().is_none());

        // Set up an in-progress operation with some stripes locked
        metadata.set_ops_state(ops_phase::OPERATING, ops_type::REKEY, 99, None);
        metadata.set_all_ops_locked();
        // Clear locks on stripes 0, 1, 2 (already processed)
        metadata.clear_ops_locked(0);
        metadata.clear_ops_locked(1);
        metadata.clear_ops_locked(2);

        let info = metadata.ops_recovery_info().unwrap();
        assert_eq!(info.ops_type, ops_type::REKEY);
        assert_eq!(info.ops_id, 99);
        assert!(info.staging_path.is_none());
        assert_eq!(info.locked_stripes, vec![3, 4, 5, 6, 7]);
    }

    #[test]
    fn test_ops_clear_state() {
        let mut metadata = UbiMetadata::new(9, 8, 8);
        metadata.set_ops_state(
            ops_phase::OPERATING,
            ops_type::SNAPSHOT,
            1,
            Some("/staging".to_string()),
        );
        assert_eq!(metadata.ops_phase, ops_phase::OPERATING);

        metadata.clear_ops_state();
        assert_eq!(metadata.ops_phase, ops_phase::NORMAL);
        assert_eq!(metadata.ops_type, ops_type::NONE);
        assert_eq!(metadata.ops_id, 0);
        assert!(metadata.ops_staging_path.is_none());
    }

    #[test]
    fn test_ops_state_roundtrip_through_bdev() {
        // Full roundtrip: write metadata with ops state, reload, verify.
        // This exercises save_to_bdev + load_from_bdev with the new fields.
        let mut metadata = UbiMetadata::new(9, 16, 16);
        metadata.set_ops_state(
            ops_phase::OPERATING,
            ops_type::SNAPSHOT,
            12345,
            Some("/mnt/staging/snap-12345".to_string()),
        );
        metadata.set_all_ops_locked();
        // Simulate partial progress: clear locks on first 5 stripes
        for i in 0..5 {
            metadata.clear_ops_locked(i);
        }

        let metadata_size = metadata.metadata_size();
        let mut buf = vec![0u8; metadata_size];
        metadata.write_to_buf(&mut buf).expect("write to buffer");

        let loaded = UbiMetadata::from_bytes(&buf).expect("deserialize");

        // Verify ops state
        let info = loaded.ops_recovery_info().unwrap();
        assert_eq!(info.ops_type, ops_type::SNAPSHOT);
        assert_eq!(info.ops_id, 12345);
        assert_eq!(
            info.staging_path.as_deref(),
            Some("/mnt/staging/snap-12345")
        );
        assert_eq!(
            info.locked_stripes,
            vec![5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
        );

        // Verify stripe headers preserved correctly
        for i in 0..5 {
            assert_eq!(
                loaded.stripe_headers[i] & metadata_flags::OPS_LOCKED,
                0,
                "stripe {i} lock should be cleared"
            );
        }
        for i in 5..16 {
            assert_ne!(
                loaded.stripe_headers[i] & metadata_flags::OPS_LOCKED,
                0,
                "stripe {i} should still be locked"
            );
        }
    }

    #[test]
    fn test_v2_0_metadata_zero_ops_state() {
        // v2.0 metadata has zero bytes in the extension area.
        // Verify that parsing produces NORMAL phase.
        let mut metadata = UbiMetadata::new(9, 4, 4);
        metadata.version_minor = 0u16.to_le_bytes();

        let metadata_size = metadata.metadata_size();
        let mut buf = vec![0u8; metadata_size];
        metadata.write_to_buf(&mut buf).expect("write to buffer");

        let loaded = UbiMetadata::from_bytes(&buf).expect("deserialize");
        assert_eq!(loaded.ops_phase, ops_phase::NORMAL);
        assert_eq!(loaded.ops_type, ops_type::NONE);
        assert_eq!(loaded.ops_id, 0);
        assert!(loaded.ops_staging_path.is_none());
        assert!(loaded.ops_recovery_info().is_none());
    }
}
