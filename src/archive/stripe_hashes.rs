use std::collections::{BTreeMap, HashMap};
use std::io::Cursor;

use super::bytes32;
use ciborium::{de, ser};
use hmac::{Hmac, Mac};
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use sha2::Sha256;
use ubiblk_macros::error_context;

use crate::{backends::SECTOR_SIZE, crypt::XtsBlockCipher, Result};

pub type StripeContentMap = HashMap<usize, StripeContentSpecifier>;

const ARCHIVE_STRIPE_MAPPING_VERSION: u32 = 1;
const ARCHIVE_STRIPE_MAPPING_DOMAIN: &[u8] = b"ubiblk-archive-stripe-mapping";

// Start XTS sectors at a clearly separate, high range to avoid collision
// with data stripe-derived sector numbers.
const XTS_SECTOR_START: u64 = 1 << 60; // 1 EiB sector offset

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct StripeMappingFile {
    pub domain: Vec<u8>,
    pub version: u32,
    /// Serialized mapping; padded to sector size. Optionally encrypted.
    pub ciphertext: Vec<u8>,
    /// Length of the original plaintext before padding
    pub plaintext_len: u64,
    /// HMAC tag computed over `domain || version || plaintext_len || ciphertext`
    #[serde(with = "bytes32")]
    pub hmac_tag: [u8; 32],
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum StripeContentSpecifier {
    Zero,
    #[serde(with = "bytes32")]
    Some([u8; 32]),
}

#[error_context("Failed to compute manifest HMAC tag")]
pub fn compute_manifest_hmac_tag(key: &[u8], bytes: &[u8]) -> Result<[u8; 32]> {
    let mut mac = Hmac::<Sha256>::new_from_slice(key).map_err(|e| {
        crate::ubiblk_error!(ArchiveError {
            description: format!("Failed to initialize HMAC: {e}"),
        })
    })?;
    mac.update(bytes);
    Ok(mac.finalize().into_bytes().into())
}

#[error_context("Failed to verify manifest HMAC tag")]
pub fn verify_manifest_hmac_tag(key: &[u8], bytes: &[u8], tag: &[u8]) -> Result<()> {
    let mut mac = Hmac::<Sha256>::new_from_slice(key).map_err(|e| {
        crate::ubiblk_error!(ArchiveError {
            description: format!("Failed to initialize HMAC: {e}"),
        })
    })?;
    mac.update(bytes);
    mac.verify_slice(tag).map_err(|_| {
        crate::ubiblk_error!(ArchiveError {
            description: "stripe-mapping HMAC verification failed".to_string(),
        })
    })?;
    Ok(())
}

#[error_context("Failed to serialize stripe mapping")]
pub fn serialize_stripe_mapping(
    map: &StripeContentMap,
    hmac_key: &[u8],
    cipher: Option<XtsBlockCipher>,
) -> Result<Vec<u8>> {
    let version = ARCHIVE_STRIPE_MAPPING_VERSION;
    let domain = ARCHIVE_STRIPE_MAPPING_DOMAIN;
    // Serialize keys as u64 for architectural independence. Use BTreeMap to
    // have deterministic ordering.
    let btree_map: BTreeMap<u64, StripeContentSpecifier> =
        map.iter().map(|(&k, v)| (k as u64, v.clone())).collect();

    let map_bytes = cbor_to_vec(&btree_map, "stripe mapping")?;
    let (mut padded, plaintext_len) = pad_to_sector(&map_bytes);
    if let Some(mut cipher) = cipher {
        let sector_count = padded.len() / SECTOR_SIZE;
        cipher.encrypt(&mut padded, XTS_SECTOR_START, sector_count as u64);
    }
    let hmac_tag = compute_manifest_hmac_tag(
        hmac_key,
        &manifest_hmac_input(domain, version, plaintext_len, &padded),
    )?;
    let mapping = StripeMappingFile {
        domain: domain.to_vec(),
        ciphertext: padded,
        plaintext_len,
        hmac_tag,
        version,
    };
    cbor_to_vec(&mapping, "stripe-mapping")
}

#[error_context("Failed to deserialize stripe mapping")]
pub fn deserialize_stripe_mapping(
    bytes: &[u8],
    hmac_key: &[u8],
    cipher: Option<XtsBlockCipher>,
) -> Result<StripeContentMap> {
    let StripeMappingFile {
        version,
        domain,
        ciphertext,
        plaintext_len: raw_plaintext_len,
        hmac_tag,
        ..
    } = cbor_from_slice(bytes, "stripe-mapping")?;

    if version != ARCHIVE_STRIPE_MAPPING_VERSION {
        return Err(crate::ubiblk_error!(ArchiveError {
            description: format!("unsupported stripe-mapping version {}", version),
        }));
    }

    if domain != ARCHIVE_STRIPE_MAPPING_DOMAIN {
        return Err(crate::ubiblk_error!(ArchiveError {
            description: "invalid stripe-mapping domain".to_string(),
        }));
    }

    if !ciphertext.len().is_multiple_of(SECTOR_SIZE) {
        return Err(crate::ubiblk_error!(ArchiveError {
            description: "stripe-mapping ciphertext is not sector-aligned".to_string(),
        }));
    }

    // verify HMAC
    let hmac_input = manifest_hmac_input(&domain, version, raw_plaintext_len, &ciphertext);
    verify_manifest_hmac_tag(hmac_key, &hmac_input, &hmac_tag)?;

    // decrypt
    let mut decrypted = ciphertext;
    if let Some(mut cipher) = cipher {
        let sector_count = decrypted.len() / SECTOR_SIZE;
        cipher.decrypt(&mut decrypted, XTS_SECTOR_START, sector_count as u64);
    }

    // truncate to original plaintext length
    let plaintext_len = usize::try_from(raw_plaintext_len).map_err(|_| {
        crate::ubiblk_error!(ArchiveError {
            description: "stripe-mapping plaintext length overflow".to_string(),
        })
    })?;
    if plaintext_len > decrypted.len() {
        return Err(crate::ubiblk_error!(ArchiveError {
            description: "stripe-mapping plaintext length exceeds ciphertext".to_string(),
        }));
    }
    decrypted.truncate(plaintext_len);

    // decode serialized map
    let btree_map: BTreeMap<u64, StripeContentSpecifier> =
        cbor_from_slice(&decrypted, "stripe mapping")?;
    let map: StripeContentMap = btree_map
        .into_iter()
        .map(|(k, v)| (k as usize, v))
        .collect();
    Ok(map)
}

fn cbor_to_vec<T: Serialize>(value: &T, context: &str) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    ser::into_writer(value, &mut bytes).map_err(|e| {
        crate::ubiblk_error!(ArchiveError {
            description: format!("Failed to serialize {context}: {e}"),
        })
    })?;
    Ok(bytes)
}

fn cbor_from_slice<T: DeserializeOwned>(bytes: &[u8], context: &str) -> Result<T> {
    de::from_reader(Cursor::new(bytes)).map_err(|e| {
        crate::ubiblk_error!(ArchiveError {
            description: format!("failed to parse {context}: {e}"),
        })
    })
}

fn pad_to_sector(bytes: &[u8]) -> (Vec<u8>, u64) {
    let len = bytes.len();
    let pad_len = (SECTOR_SIZE - (len % SECTOR_SIZE)) % SECTOR_SIZE;
    let mut padded = Vec::with_capacity(len + pad_len);
    padded.extend_from_slice(bytes);
    if pad_len > 0 {
        padded.resize(len + pad_len, 0);
    }
    (padded, len as u64)
}

fn manifest_hmac_input(domain: &[u8], version: u32, plaintext_len: u64, payload: &[u8]) -> Vec<u8> {
    let mut data = Vec::with_capacity(domain.len() + 4 + 8 + payload.len());
    data.extend_from_slice(domain);
    data.extend_from_slice(&version.to_le_bytes());
    data.extend_from_slice(&plaintext_len.to_le_bytes());
    data.extend_from_slice(payload);
    data
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_stripe_content_map_roundtrip() {
        let mut map = StripeContentMap::new();
        map.insert(1, StripeContentSpecifier::Zero);
        map.insert(2, StripeContentSpecifier::Some([0xAB; 32]));

        let bytes = cbor_to_vec(&map, "stripe content map").unwrap();
        let decoded: StripeContentMap = cbor_from_slice(&bytes, "stripe content map").unwrap();

        assert_eq!(map, decoded);
    }

    #[test]
    fn test_manifest_hmac_verification() {
        let key = [0x11u8; 32];
        let data = b"stripe-mapping";
        let tag = compute_manifest_hmac_tag(&key, data).unwrap();
        verify_manifest_hmac_tag(&key, data, &tag).unwrap();

        let mut tampered = data.to_vec();
        tampered[0] ^= 0xFF;
        assert!(verify_manifest_hmac_tag(&key, &tampered, &tag).is_err());
    }

    #[test]
    fn test_stripe_mapping_roundtrip() {
        let key = [0x22u8; 32];
        let mut map = StripeContentMap::new();
        map.insert(1, StripeContentSpecifier::Zero);
        map.insert(2, StripeContentSpecifier::Some([0xCD; 32]));

        let serialize_result = serialize_stripe_mapping(&map, &key, None);
        assert!(serialize_result.is_ok());

        let bytes = serialize_result.unwrap();
        let deserialize_result = deserialize_stripe_mapping(&bytes, &key, None);
        assert!(deserialize_result.is_ok());

        let decoded = deserialize_result.unwrap();
        assert_eq!(map, decoded);
    }

    #[test]
    fn test_stripe_mapping_roundtrip_encrypted() {
        let key = [0x33u8; 32];
        let mut map = StripeContentMap::new();
        map.insert(4, StripeContentSpecifier::Zero);
        map.insert(5, StripeContentSpecifier::Some([0xEF; 32]));

        let cipher = XtsBlockCipher::new(vec![0x11; 32], vec![0x22; 32]).unwrap();
        let serialize_result = serialize_stripe_mapping(&map, &key, Some(cipher.clone()));
        assert!(serialize_result.is_ok());
        let bytes = serialize_result.unwrap();

        let deserialize_result = deserialize_stripe_mapping(&bytes, &key, Some(cipher));
        assert!(deserialize_result.is_ok());
        let decoded = deserialize_result.unwrap();

        assert_eq!(map, decoded);
    }
}
