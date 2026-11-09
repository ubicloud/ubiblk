use std::{os::unix::fs::MetadataExt, path::Path};

use log::info;
use ubiblk_macros::error_context;

use super::{build_block_device, ensure_metadata_file};
use crate::{config::v2, stripe_source::StripeSourceBuilder, Result, ResultExt};

/// Upgrade a v0.2.x volume in place: read its legacy metadata and write the
/// equivalent current-format metadata to `config.device.metadata_path`. The
/// data device and stripe source come from `config`, the volume's new config.
#[error_context("Failed to convert legacy metadata")]
pub fn convert_legacy_metadata(config: &v2::Config, legacy_metadata_path: &Path) -> Result<()> {
    let metadata_path = config.device.metadata_path.as_ref().ok_or_else(|| {
        crate::ubiblk_error!(InvalidParameter {
            description: "metadata_path is none".to_string(),
        })
    })?;
    ensure_not_an_input(metadata_path, legacy_metadata_path, config)?;

    // v0.2.x and v0.3.x write their metadata through the volume's XTS key, so
    // read it through the same encryption as the data device.
    let legacy_bdev = build_block_device(legacy_metadata_path, config, true)
        .context("Failed to build legacy metadata block device")?;
    let legacy_buf = crate::stripe_server::read_metadata_bytes(legacy_bdev.as_ref())?;

    let disk_bdev = build_block_device(&config.device.data_path, config, false)
        .context("Failed to build disk block device")?;
    let legacy_bytes = legacy_buf.borrow();
    let legacy = crate::stripe_server::parse_v0_2_metadata(
        legacy_bytes.as_slice(),
        disk_bdev.sector_count(),
    )?;

    let stripe_source = StripeSourceBuilder::new(
        config.clone(),
        1u64 << legacy.stripe_sector_count_shift,
        false,
    )
    .build()?;
    let metadata = legacy.convert(|stripe_id| stripe_source.has_stripe(stripe_id))?;

    ensure_metadata_file(metadata_path, metadata.metadata_size())?;
    let metadata_bdev = build_block_device(metadata_path, config, false)
        .context("Failed to build metadata block device")?;
    metadata.save_to_bdev(metadata_bdev.as_ref())?;
    info!(
        "Converted legacy metadata {} to {}",
        legacy_metadata_path.display(),
        metadata_path.display()
    );
    Ok(())
}

/// Fail if `output` already exists as the same file as the legacy metadata,
/// the data device or the raw image, whatever path it is reached by.
fn ensure_not_an_input(
    output: &Path,
    legacy_metadata_path: &Path,
    config: &v2::Config,
) -> Result<()> {
    let output_stat = match std::fs::metadata(output) {
        Ok(stat) => stat,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(()),
        Err(e) => return Err(crate::ubiblk_error!(IoError { source: e })),
    };

    let mut inputs = vec![legacy_metadata_path, config.device.data_path.as_path()];
    if let Some(v2::stripe_source::StripeSourceConfig::Raw { image_path, .. }) =
        &config.stripe_source
    {
        inputs.push(image_path.as_path());
    }
    for input in inputs {
        if let Ok(stat) = std::fs::metadata(input) {
            if stat.dev() == output_stat.dev() && stat.ino() == output_stat.ino() {
                return Err(crate::ubiblk_error!(InvalidParameter {
                    description: format!(
                        "metadata_path {} is the same file as {}",
                        output.display(),
                        input.display()
                    ),
                }));
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backends::common::{tests::test_config, SECTOR_SIZE};
    use crate::block_device::UbiMetadata;
    use crate::config::v2::stripe_source::StripeSourceConfig;

    fn write_v0_2_metadata(path: &Path, shift: u8, headers: &[u8]) {
        let mut buf = vec![0u8; 2 * SECTOR_SIZE];
        buf[..9].copy_from_slice(b"BDEV_UBI\0");
        buf[13] = shift;
        buf[SECTOR_SIZE..SECTOR_SIZE + headers.len()].copy_from_slice(headers);
        std::fs::write(path, buf).unwrap();
    }

    #[test]
    fn convert_legacy_metadata_with_raw_source() {
        use crate::block_device::metadata_flags::{FETCHED, HAS_SOURCE};

        let dir = tempfile::tempdir().unwrap();
        let stripe_size = 8 * SECTOR_SIZE;
        // Four data stripes; the image covers two and a half of them.
        std::fs::write(dir.path().join("disk"), vec![0; 4 * stripe_size]).unwrap();
        std::fs::write(dir.path().join("image"), vec![0; 5 * stripe_size / 2]).unwrap();
        // v0.2.x created stripe 3, past the image, as fetched.
        write_v0_2_metadata(&dir.path().join("legacy"), 3, &[0, 1, 0, 1]);

        let config = test_config(
            &dir.path().join("disk"),
            Some(&dir.path().join("metadata")),
            Some(StripeSourceConfig::Raw {
                image_path: dir.path().join("image"),
                autofetch: false,
                copy_on_read: false,
            }),
        );
        convert_legacy_metadata(&config, &dir.path().join("legacy")).unwrap();

        let metadata =
            UbiMetadata::from_bytes(&std::fs::read(dir.path().join("metadata")).unwrap()).unwrap();
        assert_eq!(metadata.stripe_sector_count_shift, 3);
        assert_eq!(
            metadata.stripe_headers,
            vec![HAS_SOURCE, HAS_SOURCE | FETCHED, HAS_SOURCE, 0]
        );
    }

    #[test]
    fn convert_legacy_metadata_without_source() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(dir.path().join("disk"), vec![0; 2 * 8 * SECTOR_SIZE]).unwrap();
        write_v0_2_metadata(&dir.path().join("legacy"), 3, &[1, 1]);

        let config = test_config(
            &dir.path().join("disk"),
            Some(&dir.path().join("metadata")),
            None,
        );
        convert_legacy_metadata(&config, &dir.path().join("legacy")).unwrap();

        let metadata =
            UbiMetadata::from_bytes(&std::fs::read(dir.path().join("metadata")).unwrap()).unwrap();
        assert_eq!(metadata.stripe_headers, vec![0, 0]);
    }

    #[test]
    fn convert_legacy_metadata_reads_encrypted_legacy_metadata() {
        use crate::block_device::metadata_flags::HAS_SOURCE;
        use crate::block_device::{shared_buffer, wait_for_completion};
        use crate::config::v2::secrets::{
            resolve_secrets, SecretDef, SecretEncoding, SecretRef, SecretSource,
        };
        use base64::Engine;

        let dir = tempfile::tempdir().unwrap();
        let stripe_size = 8 * SECTOR_SIZE;
        std::fs::write(dir.path().join("disk"), vec![0; 2 * stripe_size]).unwrap();
        std::fs::write(dir.path().join("image"), vec![0; 2 * stripe_size]).unwrap();
        std::fs::write(dir.path().join("legacy"), vec![0; 2 * SECTOR_SIZE]).unwrap();

        let mut config = test_config(
            &dir.path().join("disk"),
            Some(&dir.path().join("metadata")),
            Some(StripeSourceConfig::Raw {
                image_path: dir.path().join("image"),
                autofetch: false,
                copy_on_read: false,
            }),
        );
        let xts_key = base64::engine::general_purpose::STANDARD.encode([0x42u8; 64]);
        let secret_defs = std::collections::HashMap::from([(
            "xts-key".to_string(),
            SecretDef {
                source: SecretSource::Inline(xts_key),
                encrypted_by: None,
                encoding: SecretEncoding::Base64,
            },
        )]);
        config.secrets = resolve_secrets(&secret_defs, &config.danger_zone).unwrap();
        config.encryption = Some(v2::EncryptionSection {
            xts_key: SecretRef::Ref("xts-key".to_string()),
        });

        // Write v0.2.x metadata through the XTS key, as v0.2.x does.
        let legacy_bdev = build_block_device(&dir.path().join("legacy"), &config, false).unwrap();
        let buf = shared_buffer(2 * SECTOR_SIZE);
        {
            let mut b = buf.borrow_mut();
            let bytes = b.as_mut_slice();
            bytes[..9].copy_from_slice(b"BDEV_UBI\0");
            bytes[13] = 3;
        }
        let mut ch = legacy_bdev.create_channel().unwrap();
        ch.add_write(0, 2, buf, 0);
        ch.submit().unwrap();
        wait_for_completion(ch.as_mut(), 0, std::time::Duration::from_secs(5)).unwrap();
        assert_ne!(
            &std::fs::read(dir.path().join("legacy")).unwrap()[..9],
            b"BDEV_UBI\0"
        );

        convert_legacy_metadata(&config, &dir.path().join("legacy")).unwrap();

        let metadata_bdev =
            build_block_device(&dir.path().join("metadata"), &config, true).unwrap();
        let converted = crate::stripe_server::read_metadata_bytes(metadata_bdev.as_ref()).unwrap();
        let metadata = UbiMetadata::from_bytes(converted.borrow().as_slice()).unwrap();
        assert_eq!(metadata.stripe_headers, vec![HAS_SOURCE, HAS_SOURCE]);
    }

    #[test]
    fn convert_legacy_metadata_rejects_same_path() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(dir.path().join("disk"), vec![0; 8 * SECTOR_SIZE]).unwrap();
        write_v0_2_metadata(&dir.path().join("legacy"), 3, &[1]);

        let config = test_config(
            &dir.path().join("disk"),
            Some(&dir.path().join("legacy")),
            None,
        );
        let err = convert_legacy_metadata(&config, &dir.path().join("legacy")).unwrap_err();
        assert!(err.to_string().contains("is the same file as"));
    }

    #[test]
    fn convert_legacy_metadata_rejects_a_link_to_the_legacy_metadata() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(dir.path().join("disk"), vec![0; 8 * SECTOR_SIZE]).unwrap();
        write_v0_2_metadata(&dir.path().join("legacy"), 3, &[1]);
        std::fs::hard_link(dir.path().join("legacy"), dir.path().join("metadata")).unwrap();
        let before = std::fs::read(dir.path().join("legacy")).unwrap();

        let config = test_config(
            &dir.path().join("disk"),
            Some(&dir.path().join("metadata")),
            None,
        );
        let err = convert_legacy_metadata(&config, &dir.path().join("legacy")).unwrap_err();
        assert!(err.to_string().contains("is the same file as"));
        assert_eq!(std::fs::read(dir.path().join("legacy")).unwrap(), before);
    }

    #[test]
    fn convert_legacy_metadata_rejects_the_data_device_as_output() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(dir.path().join("disk"), vec![7; 8 * SECTOR_SIZE]).unwrap();
        write_v0_2_metadata(&dir.path().join("legacy"), 3, &[1]);

        let config = test_config(
            &dir.path().join("disk"),
            Some(&dir.path().join("disk")),
            None,
        );
        let err = convert_legacy_metadata(&config, &dir.path().join("legacy")).unwrap_err();
        assert!(err.to_string().contains("is the same file as"));
        assert_eq!(
            std::fs::read(dir.path().join("disk")).unwrap(),
            vec![7; 8 * SECTOR_SIZE]
        );
    }

    #[test]
    fn convert_legacy_metadata_rejects_an_out_of_range_shift_with_a_source() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(dir.path().join("disk"), vec![0; 8 * SECTOR_SIZE]).unwrap();
        std::fs::write(dir.path().join("image"), vec![0; 8 * SECTOR_SIZE]).unwrap();
        write_v0_2_metadata(&dir.path().join("legacy"), 255, &[0]);

        let config = test_config(
            &dir.path().join("disk"),
            Some(&dir.path().join("metadata")),
            Some(StripeSourceConfig::Raw {
                image_path: dir.path().join("image"),
                autofetch: false,
                copy_on_read: false,
            }),
        );
        let err = convert_legacy_metadata(&config, &dir.path().join("legacy")).unwrap_err();
        assert!(err.to_string().contains("exceeds maximum"));
    }
}
