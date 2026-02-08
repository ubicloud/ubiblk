use hmac::{Hmac, Mac};
use sha2::Sha256;

use crate::{
    archive::{stripe_hashes::cbor_to_vec, ArchiveMetadata},
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

fn metadata_hmac_input(metadata: &ArchiveMetadata) -> Result<Vec<u8>> {
    let mut input = metadata.clone();
    input.metadata_hmac = Vec::new();

    cbor_to_vec(&input, "archive metadata HMAC input")
}

pub fn compute_metadata_hmac_tag(key: &[u8], metadata: &ArchiveMetadata) -> Result<[u8; 32]> {
    let input = metadata_hmac_input(metadata)?;
    compute_hmac_tag(key, &input)
}

pub fn verify_metadata_hmac_tag(key: &[u8], metadata: &ArchiveMetadata) -> Result<()> {
    if metadata.metadata_hmac.len() != 32 {
        return Err(crate::ubiblk_error!(MetadataError {
            description: "Archive metadata HMAC tag has invalid length".to_string(),
        }));
    }
    let input = metadata_hmac_input(metadata)?;
    verify_hmac_tag(key, &input, &metadata.metadata_hmac)
        .context("Archive metadata HMAC verification failed")
}

#[cfg(test)]
mod tests {
    use crate::archive::ArchiveCompressionAlgorithm;

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
            encryption_key: Some((vec![123u8; 32], vec![234u8; 32])),
            compression: ArchiveCompressionAlgorithm::Snappy,
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
}
