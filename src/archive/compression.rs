use ubiblk_macros::error_context;

use crate::backends::SECTOR_SIZE;

use super::*;

impl ArchiveCompressionAlgorithm {
    #[error_context("Failed to compress data")]
    pub fn compress(&self, data: &[u8]) -> Result<Vec<u8>> {
        assert!(
            data.len().is_multiple_of(SECTOR_SIZE),
            "Data length must be a multiple of sector size"
        );
        match self {
            ArchiveCompressionAlgorithm::None => Ok(data.to_vec()),
            ArchiveCompressionAlgorithm::Zstd { level } => {
                let compressed = zstd::stream::encode_all(data, *level)?;
                Ok(with_size_header_and_padding(compressed)?)
            }
        }
    }

    #[error_context("Failed to decompress data")]
    pub fn decompress(&self, data: &[u8]) -> Result<Vec<u8>> {
        match self {
            ArchiveCompressionAlgorithm::None => Ok(data.to_vec()),
            ArchiveCompressionAlgorithm::Zstd { .. } => {
                let compressed_data = compressed_payload(data)?;
                let decompressed = zstd::stream::decode_all(compressed_data).map_err(|source| {
                    crate::ubiblk_error!(ArchiveError {
                        description: format!(
                            "Failed to decompress using Zstd algorithm (possible algorithm mismatch or corrupt data): {source}"
                        ),
                    })
                })?;
                ensure_sector_aligned(decompressed)
            }
        }
    }
}

fn ensure_sector_aligned(decompressed: Vec<u8>) -> Result<Vec<u8>> {
    if !decompressed.len().is_multiple_of(SECTOR_SIZE) {
        return Err(crate::ubiblk_error!(ArchiveError {
            description: format!(
                "Decompressed data size {} is not a multiple of sector size {}",
                decompressed.len(),
                SECTOR_SIZE
            ),
        }));
    }
    Ok(decompressed)
}

fn with_size_header_and_padding(mut compressed: Vec<u8>) -> Result<Vec<u8>> {
    let size = u32::try_from(compressed.len()).map_err(|_| {
        crate::ubiblk_error!(ArchiveError {
            description: "Compressed data size exceeds u32".to_string(),
        })
    })?;
    compressed.splice(0..0, size.to_le_bytes());
    let padding = (SECTOR_SIZE - (compressed.len() % SECTOR_SIZE)) % SECTOR_SIZE;
    let new_len = compressed.len() + padding;
    compressed.resize(new_len, 0);
    Ok(compressed)
}

fn compressed_payload(data: &[u8]) -> Result<&[u8]> {
    if data.len() < 4 {
        return Err(crate::ubiblk_error!(ArchiveError {
            description: "Data too short to contain size header".to_string(),
        }));
    }
    let size_bytes: [u8; 4] = data[0..4]
        .try_into()
        .expect("slice is exactly 4 bytes after length check");
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
    Ok(&data[4..compressed_size + 4])
}

#[cfg(test)]
mod tests {
    use super::*;

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
    fn test_zstd_compression_level_1() {
        let algorithm = ArchiveCompressionAlgorithm::Zstd { level: 1 };
        let data = vec![0xBBu8; SECTOR_SIZE * 6];
        let compressed = algorithm.compress(&data).unwrap();
        assert!(compressed.len().is_multiple_of(SECTOR_SIZE));
        let decompressed = algorithm.decompress(&compressed).unwrap();
        assert_eq!(decompressed, data);
    }

    #[test]
    fn test_zstd_decompression_invalid_data() {
        let algorithm = ArchiveCompressionAlgorithm::Zstd { level: 1 };
        let invalid_data = vec![0x00u8; 16];

        let result = algorithm.decompress(&invalid_data);
        assert!(result.is_err());
        let err = result.err().unwrap().to_string();
        assert!(err.contains("Failed to decompress using Zstd algorithm"));
    }

    #[test]
    fn test_zstd_decompression_non_sector_aligned_output() {
        let algorithm = ArchiveCompressionAlgorithm::Zstd { level: 1 };
        let compressed = zstd::stream::encode_all(&[0xABu8; 3][..], 1).unwrap();
        let data = with_size_header_and_padding(compressed).unwrap();

        let result = algorithm.decompress(&data);
        assert!(result.is_err());
        assert!(result
            .err()
            .unwrap()
            .to_string()
            .contains("is not a multiple of sector size"));
    }

    #[test]
    fn test_zstd_decompression_data_too_short() {
        let algorithm = ArchiveCompressionAlgorithm::Zstd { level: 1 };
        let data = vec![0x00u8; 3];

        let result = algorithm.decompress(&data);
        assert!(result.is_err());
        let error_message = result.err().unwrap().to_string();
        assert!(error_message.contains("Data too short to contain size header"));
        assert!(error_message.contains("Failed to decompress data"));
    }

    #[test]
    #[should_panic(expected = "Data length must be a multiple of sector size")]
    fn test_panics_on_non_sector_size_data() {
        let algorithm = ArchiveCompressionAlgorithm::None;
        let data = vec![0xFFu8; SECTOR_SIZE * 10 + 1]; // Not a multiple of sector size
        let _ = algorithm.compress(&data);
    }

    #[test]
    fn test_with_size_header_and_padding() {
        let data = vec![0xABu8; 1000];
        let result = with_size_header_and_padding(data.clone()).unwrap();
        assert_eq!(&result[0..4], &(1000u32.to_le_bytes()));
        assert_eq!(&result[4..1004], &data[..]);
        assert_eq!(
            &result[1004..],
            &[0u8; SECTOR_SIZE - (1004 % SECTOR_SIZE)][..]
        );
        assert!(result.len().is_multiple_of(SECTOR_SIZE));
    }
}
