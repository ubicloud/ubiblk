use std::io::Read;

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
                let compressed = snap::raw::Encoder::new().compress_vec(data)?;
                Ok(with_size_header_and_padding(compressed)?)
            }
            ArchiveCompressionAlgorithm::Zstd { level } => {
                let compressed = zstd::stream::encode_all(data, *level)?;
                Ok(with_size_header_and_padding(compressed)?)
            }
        }
    }

    /// Decompress data, rejecting output that would exceed `max_output_size` bytes.
    ///
    /// This prevents decompression bombs from causing OOM: the output size is
    /// checked *before* allocating the full decompressed buffer.
    pub fn decompress(&self, data: &[u8], max_output_size: usize) -> Result<Vec<u8>> {
        match self {
            ArchiveCompressionAlgorithm::None => {
                if data.len() > max_output_size {
                    return Err(crate::ubiblk_error!(ArchiveError {
                        description: format!(
                            "Uncompressed data size {} exceeds maximum allowed output size {}",
                            data.len(),
                            max_output_size
                        ),
                    }));
                }
                Ok(data.to_vec())
            }
            ArchiveCompressionAlgorithm::Snappy => {
                let compressed_data = compressed_payload(data)?;
                // Check declared decompressed size before allocating.
                let declared_size =
                    snap::raw::decompress_len(compressed_data).map_err(|source| {
                        crate::ubiblk_error!(ArchiveError {
                            description: format!(
                                "Failed to read Snappy decompressed length: {source}"
                            ),
                        })
                    })?;
                if declared_size > max_output_size {
                    return Err(crate::ubiblk_error!(ArchiveError {
                        description: format!(
                            "Snappy decompressed size {} exceeds maximum allowed output size {}",
                            declared_size, max_output_size
                        ),
                    }));
                }
                let decompressed = snap::raw::Decoder::new()
                    .decompress_vec(compressed_data)
                    .map_err(|source| {
                        crate::ubiblk_error!(ArchiveError {
                            description: format!(
                                "Failed to decompress using Snappy algorithm (possible algorithm mismatch or corrupt data): {source}"
                            ),
                        })
                    })?;
                ensure_sector_aligned(decompressed)
            }
            ArchiveCompressionAlgorithm::Zstd { .. } => {
                let compressed_data = compressed_payload(data)?;
                // Use streaming decompression with a bounded output to prevent
                // decompression bombs from allocating unbounded memory.
                let decoder = zstd::stream::Decoder::new(compressed_data).map_err(|source| {
                    crate::ubiblk_error!(ArchiveError {
                        description: format!(
                            "Failed to decompress using Zstd algorithm (possible algorithm mismatch or corrupt data): {source}"
                        ),
                    })
                })?;
                // Read up to max_output_size + 1 to detect overflow.
                let limit = (max_output_size as u64).saturating_add(1);
                let mut bounded = decoder.take(limit);
                let mut decompressed = Vec::with_capacity(max_output_size.min(16 * 1024 * 1024));
                bounded.read_to_end(&mut decompressed).map_err(|source| {
                    crate::ubiblk_error!(ArchiveError {
                        description: format!(
                            "Failed to decompress using Zstd algorithm (possible algorithm mismatch or corrupt data): {source}"
                        ),
                    })
                })?;
                if decompressed.len() > max_output_size {
                    return Err(crate::ubiblk_error!(ArchiveError {
                        description: format!(
                            "Zstd decompressed size exceeds maximum allowed output size {}",
                            max_output_size
                        ),
                    }));
                }
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
    Ok(&data[4..compressed_size + 4])
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

        let result = algorithm.decompress(&compressed, SECTOR_SIZE * 10);
        assert!(result.is_ok());
        let decompressed = result.unwrap();
        assert_eq!(decompressed, data);
    }

    #[test]
    fn test_snappy_decompression_invalid_data() {
        let algorithm = ArchiveCompressionAlgorithm::Snappy;
        let invalid_data = vec![0x00u8; 16];

        let result = algorithm.decompress(&invalid_data, SECTOR_SIZE * 128);
        assert!(result.is_err());
        assert!(result
            .err()
            .unwrap()
            .to_string()
            .contains("Failed to decompress using Snappy algorithm"));
    }

    #[test]
    fn test_snappy_decompression_non_sector_aligned_output() {
        let algorithm = ArchiveCompressionAlgorithm::Snappy;
        let compressed = snap::raw::Encoder::new()
            .compress_vec(&[0xABu8; 3])
            .unwrap();
        let data = with_size_header_and_padding(compressed).unwrap();

        let result = algorithm.decompress(&data, SECTOR_SIZE * 128);
        assert!(result.is_err());
        assert!(result
            .err()
            .unwrap()
            .to_string()
            .contains("is not a multiple of sector size"));
    }

    #[test]
    fn test_snappy_decompression_data_too_short() {
        let algorithm = ArchiveCompressionAlgorithm::Snappy;
        let data = vec![0x00u8; 3];

        let result = algorithm.decompress(&data, SECTOR_SIZE * 128);
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

        let result = algorithm.decompress(&data, SECTOR_SIZE * 128);
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
        let decompressed = algorithm.decompress(&compressed, SECTOR_SIZE * 5).unwrap();
        assert_eq!(decompressed, data);
    }

    #[test]
    fn test_zstd_compression_level_1() {
        let algorithm = ArchiveCompressionAlgorithm::Zstd { level: 1 };
        let data = vec![0xBBu8; SECTOR_SIZE * 6];
        let compressed = algorithm.compress(&data).unwrap();
        assert!(compressed.len().is_multiple_of(SECTOR_SIZE));
        let decompressed = algorithm.decompress(&compressed, SECTOR_SIZE * 6).unwrap();
        assert_eq!(decompressed, data);
    }

    #[test]
    fn test_zstd_decompression_invalid_data() {
        let algorithm = ArchiveCompressionAlgorithm::Zstd { level: 1 };
        let invalid_data = vec![0x00u8; 16];

        let result = algorithm.decompress(&invalid_data, SECTOR_SIZE * 128);
        assert!(result.is_err());
        let err = result.err().unwrap().to_string();
        assert!(err.contains("Failed to decompress using Zstd algorithm"));
    }

    #[test]
    fn test_zstd_decompression_non_sector_aligned_output() {
        let algorithm = ArchiveCompressionAlgorithm::Zstd { level: 1 };
        let compressed = zstd::stream::encode_all(&[0xABu8; 3][..], 1).unwrap();
        let data = with_size_header_and_padding(compressed).unwrap();

        let result = algorithm.decompress(&data, SECTOR_SIZE * 128);
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

        let result = algorithm.decompress(&data, SECTOR_SIZE * 128);
        assert!(result.is_err());
        assert!(result
            .err()
            .unwrap()
            .to_string()
            .contains("Data too short to contain size header"));
    }

    #[test]
    #[should_panic(expected = "Data length must be a multiple of sector size")]
    fn test_panics_on_non_sector_size_data() {
        let algorithm = ArchiveCompressionAlgorithm::Snappy;
        let data = vec![0xFFu8; SECTOR_SIZE * 10 + 1]; // Not a multiple of sector size
        let _ = algorithm.compress(&data);
    }

    #[test]
    fn test_snappy_rejects_oversized_output() {
        let algorithm = ArchiveCompressionAlgorithm::Snappy;
        // Compress 10 sectors of data
        let data = vec![0xFFu8; SECTOR_SIZE * 10];
        let compressed = algorithm.compress(&data).unwrap();

        // Try to decompress with a limit of only 5 sectors — should be rejected
        let result = algorithm.decompress(&compressed, SECTOR_SIZE * 5);
        assert!(result.is_err());
        let err = result.err().unwrap().to_string();
        assert!(
            err.contains("exceeds maximum allowed output size"),
            "Expected size limit error, got: {err}"
        );
    }

    #[test]
    fn test_zstd_rejects_oversized_output() {
        let algorithm = ArchiveCompressionAlgorithm::Zstd { level: 1 };
        // Compress 10 sectors of data
        let data = vec![0xFFu8; SECTOR_SIZE * 10];
        let compressed = algorithm.compress(&data).unwrap();

        // Try to decompress with a limit of only 5 sectors — should be rejected
        let result = algorithm.decompress(&compressed, SECTOR_SIZE * 5);
        assert!(result.is_err());
        let err = result.err().unwrap().to_string();
        assert!(
            err.contains("exceeds maximum allowed output size"),
            "Expected size limit error, got: {err}"
        );
    }

    #[test]
    fn test_none_rejects_oversized_output() {
        let algorithm = ArchiveCompressionAlgorithm::None;
        let data = vec![0xAAu8; SECTOR_SIZE * 10];

        // Try to decompress with a limit of only 5 sectors
        let result = algorithm.decompress(&data, SECTOR_SIZE * 5);
        assert!(result.is_err());
        let err = result.err().unwrap().to_string();
        assert!(
            err.contains("exceeds maximum allowed output size"),
            "Expected size limit error, got: {err}"
        );
    }

    #[test]
    fn test_snappy_accepts_exact_size_output() {
        let algorithm = ArchiveCompressionAlgorithm::Snappy;
        let data = vec![0xFFu8; SECTOR_SIZE * 10];
        let compressed = algorithm.compress(&data).unwrap();

        // Exact size should succeed
        let result = algorithm.decompress(&compressed, SECTOR_SIZE * 10);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), data);
    }

    #[test]
    fn test_zstd_accepts_exact_size_output() {
        let algorithm = ArchiveCompressionAlgorithm::Zstd { level: 1 };
        let data = vec![0xFFu8; SECTOR_SIZE * 10];
        let compressed = algorithm.compress(&data).unwrap();

        // Exact size should succeed
        let result = algorithm.decompress(&compressed, SECTOR_SIZE * 10);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), data);
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
