//! Serving-only compatibility for legacy v0.2.x volumes.
//!
//! v0.2.x metadata predates the current format: stripe headers carry only
//! fetched (bit 0) and written (bit 1) — no HAS_SOURCE bit — packed one byte
//! per stripe after sector 0, with no per-sector CRC32 or stored count. Its
//! config is a YAML `Options` file whose XTS keys are KEK-wrapped.
//!
//! This module reads those formats and produces an in-memory current-format
//! config + metadata so the existing serving path can migrate the volume. It is
//! intentionally narrow — serving only, no write support — and touches none of
//! the general metadata or config code.

use std::{collections::HashMap, fs::File, path::Path, time::Duration};

use aes_gcm::{
    aead::{Aead, AeadCore, KeyInit, Payload},
    Aes256Gcm, Nonce,
};
use serde::Deserialize;
use serde_with::{base64::Base64, serde_as};

use crate::{
    backends::SECTOR_SIZE,
    block_device::{
        metadata_flags, shared_buffer, wait_for_completion, BlockDevice, SharedBuffer, UbiMetadata,
    },
    config::v2::{
        self,
        secrets::{resolve_secrets, SecretDef, SecretEncoding, SecretRef, SecretSource},
        stripe_source::StripeSourceConfig,
        DangerZone, DeviceSection, EncryptionSection,
    },
    Result,
};
use log::info;
use ubiblk_macros::error_context;

/// AES-256-GCM nonce type, sized to match the cipher (12 bytes).
type LegacyNonce = Nonce<<Aes256Gcm as AeadCore>::NonceSize>;

/// Magic shared by all on-disk UBI metadata, legacy and current alike.
const UBI_MAGIC: &[u8] = b"BDEV_UBI\0";
/// Largest stripe shift a v0.2.x volume could have been created with (its
/// `init-metadata` capped it at 16 == 2^16 sectors == 32 MiB stripes). Bounding
/// it keeps `1 << shift` and the derived stripe size well within range.
const MAX_LEGACY_STRIPE_SECTOR_COUNT_SHIFT: u8 = 16;
/// Secret id for the XTS key synthesized from a legacy config.
const LEGACY_XTS_KEY_ID: &str = "__legacy_xts_key";

/// Load metadata for serving, accepting legacy v0.2.x volumes. Current-format
/// metadata (version_major 2) goes to the shared loader; v0.2.x metadata
/// (version_major 0) is translated, using `data_sector_count` (the data
/// device's size) to derive the stripe count — see `translate_v0_2_metadata`.
#[error_context("Failed to load metadata for serving")]
pub fn load_metadata_for_serving(
    bdev: &dyn BlockDevice,
    data_sector_count: u64,
) -> Result<Box<UbiMetadata>> {
    let buf = read_metadata_bytes(bdev)?;
    let buf = buf.borrow();
    let bytes = buf.as_slice();

    if is_legacy_v0_2(bytes) {
        info!("Metadata is legacy v0.2.x; translating for serving");
        translate_v0_2_metadata(bytes, data_sector_count)
    } else {
        UbiMetadata::from_bytes(bytes)
    }
}

/// True for v0.2.x metadata: same magic as current, but version_major 0
/// (u16 LE at offset 9) rather than 2.
fn is_legacy_v0_2(buf: &[u8]) -> bool {
    buf.len() >= 11 && buf[..9] == *UBI_MAGIC && buf[9] == 0 && buf[10] == 0
}

/// Read the whole metadata device into a buffer.
fn read_metadata_bytes(bdev: &dyn BlockDevice) -> Result<SharedBuffer> {
    let mut io_channel = bdev.create_channel()?;
    let sector_count = bdev.sector_count();

    // Validate the size fits in memory before allocating, so a bogus device
    // size can't overflow the buffer length.
    let sector_count_u32: u32 = sector_count.try_into().map_err(|_| {
        crate::ubiblk_error!(InvalidParameter {
            description: "Metadata file too large".to_string(),
        })
    })?;
    let byte_len = (sector_count_u32 as usize)
        .checked_mul(SECTOR_SIZE)
        .ok_or_else(|| {
            crate::ubiblk_error!(InvalidParameter {
                description: "Metadata file too large".to_string(),
            })
        })?;
    let buf = shared_buffer(byte_len);

    io_channel.add_read(0, sector_count_u32, buf.clone(), 0);
    io_channel.submit()?;
    wait_for_completion(io_channel.as_mut(), 0, Duration::from_secs(30))?;
    Ok(buf)
}

/// Translate v0.2.x metadata into the current in-memory layout for *serving*.
/// A header of 0 means the stripe is still in the source, so it becomes
/// HAS_SOURCE; anything already local (fetched and/or written) becomes WRITTEN.
/// The shift lives at byte 13, headers follow sector 0, one byte per stripe.
///
/// v0.2.x stores no stripe count: the effective count comes from the data
/// device size, and the metadata's header array is only a capacity that may be
/// larger. So derive the count from `data_sector_count` (matching v0.2.x's own
/// `source_sector_count.div_ceil(stripe_size)`) and read exactly that many
/// headers, rather than trusting the metadata file's size.
fn translate_v0_2_metadata(buf: &[u8], data_sector_count: u64) -> Result<Box<UbiMetadata>> {
    if buf.len() < SECTOR_SIZE {
        return Err(crate::ubiblk_error!(MetadataError {
            description: format!("Legacy metadata too small: {} < {SECTOR_SIZE}", buf.len()),
        }));
    }

    let shift = buf[13];
    if shift > MAX_LEGACY_STRIPE_SECTOR_COUNT_SHIFT {
        return Err(crate::ubiblk_error!(MetadataError {
            description: format!(
                "Legacy metadata stripe shift {shift} exceeds maximum {MAX_LEGACY_STRIPE_SECTOR_COUNT_SHIFT}"
            ),
        }));
    }
    let stripe_count = data_sector_count.div_ceil(1u64 << shift) as usize;

    let available = buf.len() - SECTOR_SIZE;
    if stripe_count > available {
        return Err(crate::ubiblk_error!(MetadataError {
            description: format!(
                "Legacy metadata holds {available} stripe headers, fewer than the {stripe_count} the data device needs"
            ),
        }));
    }

    let legacy_headers = &buf[SECTOR_SIZE..SECTOR_SIZE + stripe_count];
    let mut metadata = UbiMetadata::new(shift, stripe_count, 0);
    for (header, &legacy) in metadata.stripe_headers.iter_mut().zip(legacy_headers) {
        *header = if legacy == 0 {
            metadata_flags::HAS_SOURCE
        } else {
            metadata_flags::WRITTEN
        };
    }
    Ok(metadata)
}

/// Subset of the v0.2.x `Options` YAML config needed to serve a volume. Unknown
/// fields (socket, queue sizing, …) are ignored.
#[serde_as]
#[derive(Debug, Deserialize)]
struct LegacyOptions {
    path: String,
    #[serde(default)]
    image_path: Option<String>,
    #[serde(default)]
    metadata_path: Option<String>,
    #[serde(default)]
    track_written: bool,
    /// The two XTS keys, wrapped exactly as v0.2.x stored them (base64).
    #[serde_as(as = "Option<(Base64, Base64)>")]
    #[serde(default)]
    encryption_key: Option<(Vec<u8>, Vec<u8>)>,
}

/// v0.2.x key-encryption-key YAML — the same format as v0.2.x's `--kek` file.
#[serde_as]
#[derive(Debug, Default, Deserialize)]
struct LegacyKek {
    #[serde(default)]
    method: LegacyCipherMethod,
    #[serde_as(as = "Option<Base64>")]
    #[serde(default)]
    key: Option<Vec<u8>>,
    #[serde_as(as = "Option<Base64>")]
    #[serde(default)]
    init_vector: Option<Vec<u8>>,
    #[serde_as(as = "Option<Base64>")]
    #[serde(default)]
    auth_data: Option<Vec<u8>>,
}

#[derive(Debug, Default, Deserialize)]
#[serde(rename_all = "kebab-case")]
enum LegacyCipherMethod {
    #[default]
    None,
    Aes256Gcm,
}

/// Read a v0.2.x volume's YAML config (`-f`) and optional KEK (`--legacy-kek`)
/// and convert them into an in-memory current-format config, so the existing
/// serving path can migrate the volume.
pub fn load_legacy_config(config_path: &Path, kek_path: Option<&Path>) -> Result<v2::Config> {
    let options: LegacyOptions = read_yaml(config_path)?;
    let kek = match kek_path {
        Some(path) => read_yaml(path)?,
        None => LegacyKek::default(),
    };

    // Serve a local volume with an inline plaintext key and no remote hops;
    // permissive because none of these guardrails apply to an operator
    // migrating their own volume.
    let danger_zone = DangerZone {
        enabled: true,
        allow_unencrypted_disk: true,
        allow_inline_plaintext_secrets: true,
        allow_secret_over_regular_file: true,
        allow_unencrypted_connection: true,
        allow_env_secrets: false,
    };

    let (encryption, secrets) = match options.encryption_key.as_ref() {
        Some(wrapped) => {
            let xts_key = unwrap_xts_key(wrapped, &kek)?;
            let def = SecretDef {
                source: SecretSource::Inline(base64::Engine::encode(
                    &base64::engine::general_purpose::STANDARD,
                    xts_key,
                )),
                encoding: SecretEncoding::Base64,
                encrypted_by: None,
            };
            let secrets = resolve_secrets(
                &HashMap::from([(LEGACY_XTS_KEY_ID.to_string(), def)]),
                &danger_zone,
            )?;
            let encryption = EncryptionSection {
                xts_key: SecretRef::Ref(LEGACY_XTS_KEY_ID.to_string()),
            };
            (Some(encryption), secrets)
        }
        None => (None, HashMap::new()),
    };

    Ok(v2::Config {
        device: DeviceSection {
            data_path: options.path.into(),
            metadata_path: options.metadata_path.map(Into::into),
            vhost_socket: None,
            rpc_socket: None,
            device_id: "ubiblk".to_string(),
            track_written: options.track_written,
        },
        tuning: v2::tuning::TuningSection {
            queue_size: 128,
            ..Default::default()
        },
        encryption,
        danger_zone,
        stripe_source: options
            .image_path
            .map(|image_path| StripeSourceConfig::Raw {
                image_path: image_path.into(),
                autofetch: false,
                copy_on_read: false,
            }),
        secrets,
    })
}

fn read_yaml<T: serde::de::DeserializeOwned>(path: &Path) -> Result<T> {
    let file = File::open(path).map_err(|e| crate::ubiblk_error!(IoError { source: e }))?;
    serde_yaml_ng::from_reader(file).map_err(|e| {
        crate::ubiblk_error!(InvalidParameter {
            description: format!("Failed to parse legacy YAML {}: {e}", path.display()),
        })
    })
}

/// Unwrap the two wrapped XTS keys into a single 64-byte key (key1 ‖ key2),
/// reproducing v0.2.x's KEK handling: AES-256-GCM with the KEK's fixed
/// `init_vector` and `auth_data`, or plaintext when the KEK method is `none`.
fn unwrap_xts_key(wrapped: &(Vec<u8>, Vec<u8>), kek: &LegacyKek) -> Result<[u8; 64]> {
    let (key1, key2) = match kek.method {
        LegacyCipherMethod::None => (into_key(&wrapped.0)?, into_key(&wrapped.1)?),
        LegacyCipherMethod::Aes256Gcm => {
            let key = required(kek.key.as_deref(), "kek.key")?;
            let iv = required(kek.init_vector.as_deref(), "kek.init_vector")?;
            let aad = kek.auth_data.as_deref().unwrap_or_default();
            let cipher = Aes256Gcm::new_from_slice(key).map_err(|e| {
                crate::ubiblk_error!(InvalidParameter {
                    description: format!("Invalid legacy KEK key: {e}"),
                })
            })?;
            if iv.len() != 12 {
                return Err(crate::ubiblk_error!(InvalidParameter {
                    description: format!(
                        "Legacy KEK init_vector must be 12 bytes, got {}",
                        iv.len()
                    ),
                }));
            }
            let nonce = LegacyNonce::from_slice(iv);
            (
                decrypt_key(&cipher, nonce, aad, &wrapped.0)?,
                decrypt_key(&cipher, nonce, aad, &wrapped.1)?,
            )
        }
    };

    let mut combined = [0u8; 64];
    combined[..32].copy_from_slice(&key1);
    combined[32..].copy_from_slice(&key2);
    Ok(combined)
}

fn decrypt_key(
    cipher: &Aes256Gcm,
    nonce: &LegacyNonce,
    aad: &[u8],
    wrapped: &[u8],
) -> Result<[u8; 32]> {
    let plain = cipher
        .decrypt(nonce, Payload { msg: wrapped, aad })
        .map_err(|e| {
            crate::ubiblk_error!(InvalidParameter {
                description: format!("Failed to unwrap legacy XTS key: {e}"),
            })
        })?;
    into_key(&plain)
}

fn into_key(bytes: &[u8]) -> Result<[u8; 32]> {
    bytes.try_into().map_err(|_| {
        crate::ubiblk_error!(InvalidParameter {
            description: format!("XTS key must be 32 bytes, got {}", bytes.len()),
        })
    })
}

fn required<'a>(value: Option<&'a [u8]>, what: &str) -> Result<&'a [u8]> {
    value.ok_or_else(|| {
        crate::ubiblk_error!(InvalidParameter {
            description: format!("Legacy KEK is missing required field {what}"),
        })
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a v0.2.x metadata image: sector 0 header (magic + version 0.0 +
    /// shift) followed by one header byte per stripe.
    fn v0_2_metadata(shift: u8, headers: &[u8]) -> Vec<u8> {
        let mut buf = vec![0u8; 2 * SECTOR_SIZE];
        buf[..9].copy_from_slice(UBI_MAGIC);
        buf[13] = shift; // version_major / version_minor stay 0.0
        buf[SECTOR_SIZE..SECTOR_SIZE + headers.len()].copy_from_slice(headers);
        buf
    }

    #[test]
    fn translates_flags_for_serving() {
        // 0 = in-source/unfetched, non-zero = fetched and/or written (local).
        // The metadata sector has room for many headers, but the data device is
        // 5 stripes (5 << 11 sectors), so exactly 5 headers are translated.
        let buf = v0_2_metadata(11, &[0u8, 1, 2, 3, 0]);
        let md = translate_v0_2_metadata(&buf, 5 * (1 << 11)).expect("translate");

        assert_eq!(md.stripe_sector_count_shift, 11);
        assert_eq!(md.stripe_headers.len(), 5);
        assert_eq!(md.stripe_headers[0], metadata_flags::HAS_SOURCE);
        assert_eq!(md.stripe_headers[1], metadata_flags::WRITTEN);
        assert_eq!(md.stripe_headers[2], metadata_flags::WRITTEN);
        assert_eq!(md.stripe_headers[3], metadata_flags::WRITTEN);
        assert_eq!(md.stripe_headers[4], metadata_flags::HAS_SOURCE);
    }

    #[test]
    fn rejects_out_of_range_shift() {
        let buf = v0_2_metadata(MAX_LEGACY_STRIPE_SECTOR_COUNT_SHIFT + 1, &[0, 1]);
        assert!(translate_v0_2_metadata(&buf, 2 * (1 << 11)).is_err());
    }

    #[test]
    fn unwrap_xts_key_aes_gcm_roundtrip() {
        let key1 = [0xABu8; 32];
        let key2 = [0xCDu8; 32];
        let kek_key = [0x07u8; 32];
        let iv = [0x09u8; 12];
        let aad = b"authdata".to_vec();

        let cipher = Aes256Gcm::new_from_slice(&kek_key).unwrap();
        let nonce = LegacyNonce::from_slice(&iv);
        let wrap = |k: &[u8]| {
            cipher
                .encrypt(nonce, Payload { msg: k, aad: &aad })
                .unwrap()
        };

        let kek = LegacyKek {
            method: LegacyCipherMethod::Aes256Gcm,
            key: Some(kek_key.to_vec()),
            init_vector: Some(iv.to_vec()),
            auth_data: Some(aad.clone()),
        };
        let combined = unwrap_xts_key(&(wrap(&key1), wrap(&key2)), &kek).expect("unwrap");
        assert_eq!(&combined[..32], &key1);
        assert_eq!(&combined[32..], &key2);
    }

    #[test]
    fn load_legacy_config_unencrypted_yaml() {
        use std::io::Write as _;
        use tempfile::NamedTempFile;

        let mut cfg = NamedTempFile::new().unwrap();
        write!(
            cfg,
            "path: /d/disk.raw\nimage_path: /d/base.raw\ntrack_written: true\n"
        )
        .unwrap();

        let config = load_legacy_config(cfg.path(), None).expect("load");
        assert_eq!(config.device.data_path, Path::new("/d/disk.raw"));
        assert!(config.device.track_written);
        assert!(config.encryption.is_none());
        assert!(matches!(
            config.stripe_source,
            Some(StripeSourceConfig::Raw { .. })
        ));
    }
}
