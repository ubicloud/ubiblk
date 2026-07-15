use std::sync::Arc;

use crate::{
    backends::build_block_device,
    block_device::{metadata_flags, UbiMetadata, DEFAULT_STRIPE_SECTOR_COUNT_SHIFT},
    config::v2,
    stripe_server::StripeServer,
    stripe_source::StripeSourceBuilder,
    Result,
};

/// A `track_written = false` device does not record guest writes, so a stripe
/// with no source may still hold written data that the WRITTEN bit does not
/// reflect. Mark every no-source stripe as written so it is served from the
/// local device. Stripes that have a source are left untouched.
fn mark_no_source_stripes_written(metadata: &mut UbiMetadata) {
    for header in metadata.stripe_headers.iter_mut() {
        if *header & metadata_flags::HAS_SOURCE == 0 {
            *header |= metadata_flags::WRITTEN;
        }
    }
}

pub fn prepare_stripe_server(config: &v2::Config) -> Result<Arc<StripeServer>> {
    let stripe_device = build_block_device(&config.device.data_path, config, false)?;
    let (metadata, source_builder): (Arc<UbiMetadata>, Option<StripeSourceBuilder>) =
        if let Some(metadata_path) = config.device.metadata_path.as_deref() {
            let metadata_device = build_block_device(metadata_path, config, false)?;
            let mut metadata = UbiMetadata::load_from_bdev(metadata_device.as_ref())?;
            let all_fetched = metadata.has_fetched_all_stripes();
            // Unfetched source stripes are served from the stripe source, so one
            // must be configured when the device is not fully fetched; otherwise
            // reads of those stripes would fail at request time.
            if !all_fetched && config.stripe_source.is_none() {
                return Err(crate::ubiblk_error!(InvalidParameter {
                    description:
                        "device has unfetched source stripes but no stripe_source is configured"
                            .to_string(),
                }));
            }
            // The builder yields a null source when everything is already
            // fetched; otherwise it builds the configured source.
            let source_builder = StripeSourceBuilder::new(
                config.clone(),
                metadata.stripe_sector_count(),
                all_fetched,
            );
            if !config.device.track_written {
                mark_no_source_stripes_written(&mut metadata);
            }
            (Arc::from(metadata), Some(source_builder))
        } else {
            let stripe_sector_count_shift = DEFAULT_STRIPE_SECTOR_COUNT_SHIFT;
            let stripe_sector_count = 1u64 << stripe_sector_count_shift;
            let stripe_count = stripe_device.stripe_count(stripe_sector_count);
            let mut metadata =
                UbiMetadata::new(stripe_sector_count_shift, stripe_count, stripe_count);
            for stripe_header in metadata.stripe_headers.iter_mut() {
                *stripe_header |= metadata_flags::WRITTEN | metadata_flags::FETCHED;
            }
            (Arc::from(metadata), None)
        };

    Ok(Arc::new(StripeServer::new(
        Arc::from(stripe_device),
        metadata,
        source_builder,
    )))
}

#[cfg(test)]
mod tests {
    use crate::backends::SECTOR_SIZE;

    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    const STRIPE_SIZE: u64 = (1 << DEFAULT_STRIPE_SECTOR_COUNT_SHIFT) * SECTOR_SIZE as u64;

    fn config(path: String, metadata_path: Option<String>, track_written: bool) -> v2::Config {
        v2::Config {
            device: v2::DeviceSection {
                data_path: path.into(),
                metadata_path: metadata_path.map(Into::into),
                vhost_socket: None,
                rpc_socket: None,
                device_id: "ubiblk".to_string(),
                track_written,
            },
            tuning: v2::tuning::TuningSection {
                queue_size: 128,
                ..Default::default()
            },
            encryption: None,
            danger_zone: v2::DangerZone {
                enabled: true,
                allow_unencrypted_disk: true,
                allow_inline_plaintext_secrets: true,
                allow_secret_over_regular_file: true,
                allow_unencrypted_connection: true,
                allow_env_secrets: false,
            },
            stripe_source: None,
            secrets: std::collections::HashMap::new(),
        }
    }

    #[test]
    fn test_prepare_stripe_server_without_metadata() -> Result<()> {
        let stripe_count = 16;
        let storage_file = NamedTempFile::new()?;
        storage_file.as_file().set_len(stripe_count * STRIPE_SIZE)?;

        let config = config(
            storage_file.path().to_str().unwrap().to_string(),
            None,
            false,
        );

        let server = prepare_stripe_server(&config)?;

        let metadata = server.metadata.as_ref();
        assert_eq!(metadata.stripe_headers.len(), stripe_count as usize);

        for header in metadata.stripe_headers.iter() {
            assert_eq!(*header & metadata_flags::WRITTEN, metadata_flags::WRITTEN);
        }

        Ok(())
    }

    #[test]
    fn test_prepare_stripe_server_with_metadata() -> Result<()> {
        let stripe_count = 1024;
        let storage_file = NamedTempFile::new()?;
        let metadata_file = NamedTempFile::new()?;

        storage_file.as_file().set_len(stripe_count * STRIPE_SIZE)?;

        let mut metadata =
            UbiMetadata::new(DEFAULT_STRIPE_SECTOR_COUNT_SHIFT, stripe_count as usize, 0);

        for i in 0..stripe_count as usize {
            if i % 3 == 0 || i % 5 == 0 {
                metadata.stripe_headers[i] |= metadata_flags::WRITTEN;
            }
        }

        metadata_file.as_file().set_len(4 * 1024 * 1024)?;
        let mut buf = vec![0u8; metadata.metadata_size()];
        metadata.write_to_buf(&mut buf)?;
        metadata_file.as_file().write_all(&buf)?;

        // track_written = true: loaded headers are served verbatim.
        let config = config(
            storage_file.path().to_str().unwrap().to_string(),
            Some(metadata_file.path().to_str().unwrap().to_string()),
            true,
        );

        let server = prepare_stripe_server(&config)?;

        let loaded_metadata = server.metadata.as_ref();
        for i in 0..stripe_count as usize {
            assert_eq!(
                loaded_metadata.stripe_headers[i],
                metadata.stripe_headers[i]
            );
        }

        Ok(())
    }

    #[test]
    fn mark_no_source_stripes_written_sets_only_no_source() {
        // stripes 0..3 have HAS_SOURCE; 3..6 have no source.
        let mut metadata = UbiMetadata::new(DEFAULT_STRIPE_SECTOR_COUNT_SHIFT, 6, 3);
        metadata.stripe_headers[1] |= metadata_flags::FETCHED;

        mark_no_source_stripes_written(&mut metadata);

        // Source stripes are untouched (no WRITTEN added).
        assert_eq!(metadata.stripe_headers[0], metadata_flags::HAS_SOURCE);
        assert_eq!(
            metadata.stripe_headers[1],
            metadata_flags::HAS_SOURCE | metadata_flags::FETCHED
        );
        assert_eq!(metadata.stripe_headers[2], metadata_flags::HAS_SOURCE);
        // No-source stripes are marked written.
        for i in 3..6 {
            assert_eq!(metadata.stripe_headers[i], metadata_flags::WRITTEN);
        }
    }

    #[test]
    fn test_prepare_track_written_false_marks_no_source_written() -> Result<()> {
        let stripe_count = 16usize;
        let image_stripe_count = 4usize; // first 4 stripes have a source
        let storage_file = NamedTempFile::new()?;
        let metadata_file = NamedTempFile::new()?;
        storage_file
            .as_file()
            .set_len(stripe_count as u64 * STRIPE_SIZE)?;

        let mut metadata = UbiMetadata::new(
            DEFAULT_STRIPE_SECTOR_COUNT_SHIFT,
            stripe_count,
            image_stripe_count,
        );
        // The source stripes are already fetched (their data is in the overlay).
        for i in 0..image_stripe_count {
            metadata.stripe_headers[i] |= metadata_flags::FETCHED;
        }
        // One no-source stripe carries a real WRITTEN bit; the rest are 0 (an
        // untracked write is indistinguishable from a hole).
        metadata.stripe_headers[5] |= metadata_flags::WRITTEN;

        metadata_file.as_file().set_len(4 * 1024 * 1024)?;
        let mut buf = vec![0u8; metadata.metadata_size()];
        metadata.write_to_buf(&mut buf)?;
        metadata_file.as_file().write_all(&buf)?;

        let config = config(
            storage_file.path().to_str().unwrap().to_string(),
            Some(metadata_file.path().to_str().unwrap().to_string()),
            false, // track_written = false
        );
        let server = prepare_stripe_server(&config)?;
        let served = server.metadata.as_ref();

        for (i, &header) in served.stripe_headers.iter().enumerate() {
            if i < image_stripe_count {
                // Source stripes are served as-is, never marked written.
                assert_eq!(
                    header,
                    metadata_flags::HAS_SOURCE | metadata_flags::FETCHED,
                    "source stripe {i}"
                );
            } else {
                // Every no-source stripe is now served, written or not.
                assert_ne!(
                    header & metadata_flags::WRITTEN,
                    0,
                    "no-source stripe {i} should be served"
                );
            }
        }
        Ok(())
    }

    #[test]
    fn test_prepare_rejects_unfetched_without_source() -> Result<()> {
        let stripe_count = 8usize;
        let storage_file = NamedTempFile::new()?;
        let metadata_file = NamedTempFile::new()?;
        storage_file
            .as_file()
            .set_len(stripe_count as u64 * STRIPE_SIZE)?;

        // One source stripe that has NOT been fetched, and (via the config
        // helper) no stripe_source configured to serve it from.
        let metadata = UbiMetadata::new(DEFAULT_STRIPE_SECTOR_COUNT_SHIFT, stripe_count, 1);
        metadata_file.as_file().set_len(4 * 1024 * 1024)?;
        let mut buf = vec![0u8; metadata.metadata_size()];
        metadata.write_to_buf(&mut buf)?;
        metadata_file.as_file().write_all(&buf)?;

        let config = config(
            storage_file.path().to_str().unwrap().to_string(),
            Some(metadata_file.path().to_str().unwrap().to_string()),
            false,
        );
        let result = prepare_stripe_server(&config);
        assert!(
            result.is_err(),
            "unfetched source stripes with no stripe_source must be rejected"
        );
        let err = result.err().unwrap().to_string();
        assert!(err.contains("no stripe_source is configured"), "{err}");
        Ok(())
    }
}
