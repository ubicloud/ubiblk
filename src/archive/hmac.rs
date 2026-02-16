use hmac::{Hmac, Mac};
use sha2::Sha256;

use crate::{
    archive::{ArchiveCompressionAlgorithm, ArchiveMetadata},
    Result, ResultExt,
};

pub fn compute_hmac_tag(key: &[u8], bytes: &[u8]) -> Result<[u8; 32]> {
    let mut mac = Hmac::<Sha256>::new_from_slice(key).map_err(|e| {
        crate::ubiblk_error!(ArchiveError {
            description: format!("Failed to initialize HMAC: {e}"),
        })
    })?;
    mac.update(bytes);
    Ok(mac.finalize().into_bytes().into())
}

pub fn verify_hmac_tag(key: &[u8], bytes: &[u8], tag: &[u8]) -> Result<()> {
    let mut mac = Hmac::<Sha256>::new_from_slice(key).map_err(|e| {
        crate::ubiblk_error!(ArchiveError {
            description: format!("Failed to initialize HMAC: {e}"),
        })
    })?;
    mac.update(bytes);
    mac.verify_slice(tag).map_err(|_| {
        crate::ubiblk_error!(ArchiveError {
            description: "HMAC verification failed".to_string(),
        })
    })?;
    Ok(())
}

fn metadata_hmac_input(metadata: &ArchiveMetadata) -> Vec<u8> {
    let mut data = Vec::new();

    // Domain separator to avoid cross-protocol HMAC tag reuse and make the
    // metadata HMAC input self-describing. Keep this stable across versions.
    data.extend_from_slice(b"ARCHIVE_METADATA_HMAC_V1");

    data.extend_from_slice(&metadata.format_version.to_le_bytes());
    data.extend_from_slice(&metadata.stripe_sector_count.to_le_bytes());

    match &metadata.encryption_key {
        Some(key) => {
            data.push(1);
            push_len_prefixed(&mut data, key);
        }
        None => data.push(0),
    }

    match &metadata.compression {
        ArchiveCompressionAlgorithm::None => data.push(0),
        ArchiveCompressionAlgorithm::Zstd { level } => {
            data.push(2);
            data.extend_from_slice(&level.to_le_bytes());
        }
    }

    data
}

fn push_len_prefixed(buffer: &mut Vec<u8>, bytes: &[u8]) {
    buffer.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
    buffer.extend_from_slice(bytes);
}

pub fn compute_metadata_hmac_tag(key: &[u8], metadata: &ArchiveMetadata) -> Result<[u8; 32]> {
    let input = metadata_hmac_input(metadata);
    compute_hmac_tag(key, &input)
}

pub fn verify_metadata_hmac_tag(key: &[u8], metadata: &ArchiveMetadata) -> Result<()> {
    if metadata.metadata_hmac.len() != 32 {
        return Err(crate::ubiblk_error!(MetadataError {
            description: "Archive metadata HMAC tag has invalid length".to_string(),
        }));
    }
    let input = metadata_hmac_input(metadata);
    verify_hmac_tag(key, &input, &metadata.metadata_hmac)
        .context("Archive metadata HMAC verification failed")
}

#[cfg(test)]
mod tests {
    use crate::{archive::ArchiveCompressionAlgorithm, utils::hash::sha256_hex};

    use super::*;

    #[test]
    fn test_hmac_verification() {
        let key = [0x11u8; 32];
        let data = b"stripe-mapping";
        let tag = compute_hmac_tag(&key, data).unwrap();
        verify_hmac_tag(&key, data, &tag).unwrap();

        let mut tampered = data.to_vec();
        tampered[0] ^= 0xFF;
        assert!(verify_hmac_tag(&key, &tampered, &tag).is_err());
    }

    #[test]
    fn test_metadata_hmac() {
        let hmac_key = [0x22u8; 32];
        let metadata = ArchiveMetadata {
            format_version: 1,
            stripe_sector_count: 128,
            encryption_key: Some(vec![123u8; 64]),
            compression: ArchiveCompressionAlgorithm::None,
            hmac_key: hmac_key.to_vec(),
            metadata_hmac: Vec::new(),
        };
        let tag = compute_metadata_hmac_tag(&hmac_key, &metadata).unwrap();
        let mut verified_metadata = metadata.clone();
        verified_metadata.metadata_hmac = tag.to_vec();

        let result = verify_metadata_hmac_tag(&hmac_key, &verified_metadata);
        assert!(result.is_ok());

        let mut tampered_metadata = verified_metadata.clone();
        tampered_metadata.format_version = 2; // Change a field to invalidate the HMAC
        let result = verify_metadata_hmac_tag(&hmac_key, &tampered_metadata);
        assert!(result.is_err());
        let error_message = result.err().unwrap().to_string();
        assert!(error_message.contains("Archive metadata HMAC verification failed"));
    }

    #[test]
    fn test_metadata_hmac_input_stable_bytes() {
        let mut metadata = ArchiveMetadata {
            format_version: 1,
            stripe_sector_count: 128,
            encryption_key: Some(vec![123u8; 64]),
            compression: ArchiveCompressionAlgorithm::Zstd { level: 3 },
            hmac_key: vec![0x00u8; 32],
            metadata_hmac: vec![0xFFu8; 32],
        };

        let input1 = metadata_hmac_input(&metadata);
        let input2 = metadata_hmac_input(&metadata);
        assert_eq!(input1, input2, "metadata_hmac_input must be deterministic");

        // mutating hmac_key and metadata_hmac should not change the input bytes
        metadata.hmac_key[0] = 0xFF;
        metadata.metadata_hmac[0] = 0x22;
        let input3 = metadata_hmac_input(&metadata);
        assert_eq!(
            input1, input3,
            "metadata_hmac_input should not depend on hmac_key or metadata_hmac"
        );

        // bytes should be stable and match the expected value to catch
        // accidental changes
        let expect_sha256 = "779dd6db5299da3d7d1354c10e82111bed78d6265604c3a918457e922a66d6b6";
        assert_eq!(
            sha256_hex(&input1),
            expect_sha256,
            "metadata_hmac_input bytes changed"
        );
    }
}
