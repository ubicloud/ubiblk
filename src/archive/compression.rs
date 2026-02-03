use crate::backends::SECTOR_SIZE;

use super::*;

impl ArchiveCompressionAlgorithm {
    pub fn compress(&self, data: &[u8]) -> Result<Vec<u8>> {
        assert!(
            data.len().is_multiple_of(SECTOR_SIZE),
            "Data length must be a multiple of sector size"
        );
        match self {
            ArchiveCompressionAlgorithm::None => Ok(data.to_vec()),
            ArchiveCompressionAlgorithm::Snappy => {
                let mut compressed = snap::raw::Encoder::new().compress_vec(data)?;
                let size = compressed.len() as u32;
                compressed.splice(0..0, size.to_le_bytes().iter().cloned());
                let padding = (SECTOR_SIZE - (compressed.len() % SECTOR_SIZE)) % SECTOR_SIZE;
                compressed.extend(vec![0u8; padding]);
                Ok(compressed)
            }
        }
    }
    pub fn decompress(&self, data: &[u8]) -> Result<Vec<u8>> {
        match self {
            ArchiveCompressionAlgorithm::None => Ok(data.to_vec()),
            ArchiveCompressionAlgorithm::Snappy => {
                if data.len() < 4 {
                    return Err(crate::ubiblk_error!(ArchiveError {
                        description: "Data too short to contain size header".to_string(),
                    }));
                }
                let size_bytes: [u8; 4] = data[0..4].try_into().unwrap();
                let compressed_size = u32::from_le_bytes(size_bytes) as usize;
                if compressed_size + 4 > data.len() {
                    return Err(crate::ubiblk_error!(ArchiveError {
                        description: format!(
                            "Compressed size {} exceeds available data {}",
                            compressed_size,
                            data.len().saturating_sub(4)
                        ),
                    }));
                }
                let compressed_data = &data[4..compressed_size + 4];
                let decompressed = snap::raw::Decoder::new().decompress_vec(compressed_data)?;
                Ok(decompressed)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_snappy_compression() {
        let algorithm = ArchiveCompressionAlgorithm::Snappy;
        let data = vec![0xFFu8; SECTOR_SIZE * 10]; // 10 sectors of 0xFF

        let result = algorithm.compress(&data);
        assert!(result.is_ok());
        let compressed = result.unwrap();
        assert!(compressed.len().is_multiple_of(SECTOR_SIZE));

        let result = algorithm.decompress(&compressed);
        assert!(result.is_ok());
        let decompressed = result.unwrap();
        assert_eq!(decompressed, data);
    }

    #[test]
    fn test_snappy_decompression_invalid_data() {
        let algorithm = ArchiveCompressionAlgorithm::Snappy;
        let invalid_data = vec![0x00u8; 16];

        let result = algorithm.decompress(&invalid_data);
        assert!(result.is_err());
        assert!(result
            .err()
            .unwrap()
            .to_string()
            .contains("snappy: corrupt input"));
    }

    #[test]
    fn test_snappy_decompression_data_too_short() {
        let algorithm = ArchiveCompressionAlgorithm::Snappy;
        let data = vec![0x00u8; 3];

        let result = algorithm.decompress(&data);
        assert!(result.is_err());
        assert!(result
            .err()
            .unwrap()
            .to_string()
            .contains("Data too short to contain size header"));
    }

    #[test]
    fn test_snappy_decompression_size_out_of_bounds() {
        let algorithm = ArchiveCompressionAlgorithm::Snappy;
        let mut data = vec![0x00u8; 8];
        data[0..4].copy_from_slice(&16u32.to_le_bytes());

        let result = algorithm.decompress(&data);
        assert!(result.is_err());
        assert!(result
            .err()
            .unwrap()
            .to_string()
            .contains("Compressed size 16 exceeds available data 4"));
    }

    #[test]
    fn test_none_compression() {
        let algorithm = ArchiveCompressionAlgorithm::None;
        let data = vec![0xAAu8; SECTOR_SIZE * 5];
        let compressed = algorithm.compress(&data).unwrap();
        assert_eq!(compressed, data);
        let decompressed = algorithm.decompress(&compressed).unwrap();
        assert_eq!(decompressed, data);
    }

    #[test]
    #[should_panic(expected = "Data length must be a multiple of sector size")]
    fn test_panics_on_non_sector_size_data() {
        let algorithm = ArchiveCompressionAlgorithm::Snappy;
        let data = vec![0xFFu8; SECTOR_SIZE * 10 + 1]; // Not a multiple of sector size
        let _ = algorithm.compress(&data);
    }
}
