pub mod progress;

use std::path::{Path, PathBuf};
use std::time::Duration;

use log::info;

use crate::backends::SECTOR_SIZE;
use crate::block_device::{self, shared_buffer, wait_for_completion, BlockDevice, UbiMetadata};
use crate::config::{DeviceConfig, RekeyState};
use crate::crypt::{KeyEncryptionCipher, XtsBlockCipher};
use crate::Result;

use self::progress::ConfigUpdater;

/// Maximum number of sectors to process in a single I/O chunk.
const MAX_CHUNK_SECTORS: u64 = 1024;

/// Check that the device is not actively in use by looking for an active ublk socket.
fn check_exclusive_access(config: &DeviceConfig) -> Result<()> {
    if let Some(ref socket_path) = config.socket {
        let path = Path::new(socket_path);
        if path.exists() {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: format!(
                    "Device appears to be in use (socket exists: {}). \
                     Stop the ubiblk backend before rekeying.",
                    socket_path
                ),
            }));
        }
    }
    if let Some(ref rpc_path) = config.rpc_socket_path {
        let path = Path::new(rpc_path);
        if path.exists() {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: format!(
                    "Device appears to be in use (RPC socket exists: {}). \
                     Stop the ubiblk backend before rekeying.",
                    rpc_path
                ),
            }));
        }
    }
    Ok(())
}

/// Run the rekey operation on a device.
///
/// This re-encrypts all stripe data from the old key to a new key.
/// Supports crash recovery: if the config indicates an in-progress rekey,
/// resumes from the last completed stripe.
pub fn run(config: &DeviceConfig, config_path: &Path, kek: &KeyEncryptionCipher) -> Result<()> {
    check_exclusive_access(config)?;

    let (old_key, new_key, start_stripe) = match config.rekey_state {
        RekeyState::InProgress => {
            // Crash recovery: resume from where we left off
            let old_keys = config.encryption_key.as_ref().ok_or_else(|| {
                crate::ubiblk_error!(InvalidParameter {
                    description: "Config has rekey_state=in_progress but no encryption_key"
                        .to_string(),
                })
            })?;
            let pending_keys = config.pending_encryption_key.as_ref().ok_or_else(|| {
                crate::ubiblk_error!(InvalidParameter {
                    description: "Config has rekey_state=in_progress but no pending_encryption_key"
                        .to_string(),
                })
            })?;

            let old_cipher = XtsBlockCipher::new(old_keys.0.clone(), old_keys.1.clone())?;
            let new_cipher = XtsBlockCipher::new(pending_keys.0.clone(), pending_keys.1.clone())?;
            let start = config.rekey_progress;

            info!("Resuming rekey from stripe {} (crash recovery)", start);

            (old_cipher, new_cipher, start)
        }
        RekeyState::Complete => {
            info!("Rekey already completed, nothing to do");
            return Ok(());
        }
        RekeyState::NotStarted => {
            // Fresh rekey
            let old_keys = config.encryption_key.as_ref().ok_or_else(|| {
                crate::ubiblk_error!(InvalidParameter {
                    description: "Configuration does not contain encryption keys".to_string(),
                })
            })?;

            let old_cipher = XtsBlockCipher::new(old_keys.0.clone(), old_keys.1.clone())?;
            let new_cipher = XtsBlockCipher::random()?;

            (old_cipher, new_cipher, 0)
        }
    };

    // Open the target device WITHOUT encryption (we handle encryption manually)
    let target_dev = open_raw_device(&config.path, config)?;

    // Load metadata to know stripe layout
    let metadata_path = config.metadata_path.as_ref().ok_or_else(|| {
        crate::ubiblk_error!(InvalidParameter {
            description: "metadata_path is required for rekey".to_string(),
        })
    })?;
    let metadata_dev = open_raw_device(metadata_path, config)?;
    let metadata = UbiMetadata::load_from_bdev(metadata_dev.as_ref())?;

    let stripe_sector_count = metadata.stripe_sector_count();
    let total_stripes = metadata.stripe_count();
    let total_sectors = target_dev.sector_count();

    info!(
        "Rekey: {} stripes, {} sectors/stripe, {} total sectors",
        total_stripes, stripe_sector_count, total_sectors
    );

    // Set up config updater for atomic progress tracking
    let updater = ConfigUpdater::new(config_path.to_path_buf(), kek.clone());

    // If this is a fresh start, persist the initial rekey state
    if config.rekey_state == RekeyState::NotStarted {
        let (old_k1, old_k2) = old_key.keys();
        let (new_k1, new_k2) = new_key.keys();
        updater.start_rekey((old_k1, old_k2), (new_k1, new_k2))?;
        info!("Rekey state initialized in config");
    }

    // Create I/O channel for the target device
    let mut channel = target_dev.create_channel()?;
    let mut old_cipher = old_key.clone();
    let mut new_cipher = new_key.clone();

    for stripe_idx in start_stripe..total_stripes {
        let stripe_start_sector = stripe_idx * stripe_sector_count;
        // Last stripe may be smaller
        let stripe_end_sector =
            std::cmp::min(stripe_start_sector + stripe_sector_count, total_sectors);
        let stripe_sectors = stripe_end_sector - stripe_start_sector;

        if stripe_sectors == 0 {
            break;
        }

        rekey_stripe(
            &mut channel,
            &mut old_cipher,
            &mut new_cipher,
            stripe_start_sector,
            stripe_sectors,
        )?;

        // Flush after each stripe to ensure durability before updating progress
        let flush_id = 1;
        channel.add_flush(flush_id);
        channel.submit()?;
        wait_for_completion(channel.as_mut(), flush_id, Duration::from_secs(30))?;

        // Update progress atomically
        let completed = stripe_idx + 1;
        updater.update_progress(completed)?;

        if completed % 100 == 0 || completed == total_stripes {
            info!("Rekey progress: {}/{} stripes", completed, total_stripes);
        }
    }

    // Finalize: update config with new key, remove rekey fields
    let (new_k1, new_k2) = new_key.keys();
    updater.complete_rekey((new_k1, new_k2))?;

    info!("Rekey completed successfully for {} stripes", total_stripes);
    Ok(())
}

/// Re-encrypt a single stripe's worth of sectors.
fn rekey_stripe(
    channel: &mut Box<dyn block_device::IoChannel>,
    old_cipher: &mut XtsBlockCipher,
    new_cipher: &mut XtsBlockCipher,
    start_sector: u64,
    sector_count: u64,
) -> Result<()> {
    let mut remaining = sector_count;
    let mut current_sector = start_sector;
    let read_id = 0usize;
    let write_id = 0usize;

    while remaining > 0 {
        let chunk_sectors = std::cmp::min(remaining, MAX_CHUNK_SECTORS);
        let chunk_bytes = chunk_sectors as usize * SECTOR_SIZE;
        let buffer = shared_buffer(chunk_bytes);

        // Read raw (encrypted with old key)
        channel.add_read(
            current_sector,
            chunk_sectors as u32,
            buffer.clone(),
            read_id,
        );
        channel.submit()?;
        wait_for_completion(channel.as_mut(), read_id, Duration::from_secs(30))?;

        // Decrypt with old key, re-encrypt with new key (in-place)
        {
            let mut data = buffer.borrow_mut();
            old_cipher.decrypt(
                &mut data.as_mut_slice()[..chunk_bytes],
                current_sector,
                chunk_sectors,
            );
            new_cipher.encrypt(
                &mut data.as_mut_slice()[..chunk_bytes],
                current_sector,
                chunk_sectors,
            );
        }

        // Write back (encrypted with new key)
        channel.add_write(current_sector, chunk_sectors as u32, buffer, write_id);
        channel.submit()?;
        wait_for_completion(channel.as_mut(), write_id, Duration::from_secs(30))?;

        current_sector += chunk_sectors;
        remaining -= chunk_sectors;
    }

    Ok(())
}

/// Open a block device WITHOUT encryption wrapping (raw access).
fn open_raw_device(path: &str, config: &DeviceConfig) -> Result<Box<dyn BlockDevice>> {
    use crate::config::IoEngine;
    let dev: Box<dyn BlockDevice> = match config.io_engine {
        IoEngine::IoUring => block_device::UringBlockDevice::new(
            PathBuf::from(path),
            config.queue_size,
            false,
            true,
            false,
        )?,
        IoEngine::Sync => {
            block_device::SyncBlockDevice::new(PathBuf::from(path), false, true, false)?
        }
    };
    Ok(dev)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block_device::UbiMetadata;
    use crate::crypt::CipherMethod;
    use std::fs;
    use tempfile::TempDir;

    fn setup_test_device(
        dir: &Path,
        stripe_shift: u8,
        num_stripes: usize,
    ) -> (PathBuf, PathBuf, PathBuf) {
        let sectors_per_stripe = 1u64 << stripe_shift;
        let total_sectors = sectors_per_stripe * num_stripes as u64;
        let total_bytes = total_sectors * SECTOR_SIZE as u64;

        // Create target device file
        let target_path = dir.join("target.raw");
        let target_data = vec![0u8; total_bytes as usize];
        fs::write(&target_path, &target_data).unwrap();

        // Create metadata device file
        let metadata_path = dir.join("metadata.raw");
        let metadata = UbiMetadata::new(stripe_shift, num_stripes, 0);
        // Compute metadata size and write
        let meta_size = metadata.metadata_size();
        let meta_data = vec![0u8; meta_size];
        fs::write(&metadata_path, &meta_data).unwrap();
        // Use save_to_bdev to write proper metadata
        let meta_dev =
            block_device::SyncBlockDevice::new(metadata_path.clone(), false, false, false).unwrap();
        metadata.save_to_bdev(meta_dev.as_ref()).unwrap();

        // Create config file
        let config_path = dir.join("config.yaml");
        let config_yaml = format!(
            r#"path: "{}"
metadata_path: "{}"
io_engine: sync
encryption_key:
  - "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA="
  - "AQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQE="
"#,
            target_path.display(),
            metadata_path.display(),
        );
        fs::write(&config_path, &config_yaml).unwrap();

        (target_path, metadata_path, config_path)
    }

    fn default_kek() -> KeyEncryptionCipher {
        KeyEncryptionCipher {
            method: CipherMethod::None,
            key: None,
            auth_data: None,
        }
    }

    #[test]
    fn test_rekey_basic() {
        let dir = TempDir::new().unwrap();
        let (target_path, _metadata_path, config_path) = setup_test_device(dir.path(), 6, 2); // shift=6: 64 sectors/stripe = 32KB

        let kek = default_kek();
        let config = DeviceConfig::load_from_file_with_kek(&config_path, &kek).unwrap();

        // Write some known plaintext, encrypt with old key, write to device
        let old_key1 = [0u8; 32];
        let old_key2 = [1u8; 32];
        let mut old_cipher = XtsBlockCipher::new(old_key1.to_vec(), old_key2.to_vec()).unwrap();

        let sectors_per_stripe = 64u64;
        let total_sectors = sectors_per_stripe * 2;
        let plaintext: Vec<u8> = (0..total_sectors * SECTOR_SIZE as u64)
            .map(|i| (i % 256) as u8)
            .collect();

        // Encrypt plaintext with old key and write to device
        let mut encrypted = plaintext.clone();
        old_cipher.encrypt(&mut encrypted, 0, total_sectors);
        fs::write(&target_path, &encrypted).unwrap();

        // Run rekey
        run(&config, &config_path, &kek).unwrap();

        // Verify: config should have new key, no pending fields
        let new_config = DeviceConfig::load_from_file_with_kek(&config_path, &kek).unwrap();
        assert!(new_config.pending_encryption_key.is_none());
        assert_eq!(new_config.rekey_state, RekeyState::NotStarted); // field removed = default
        assert_eq!(new_config.rekey_progress, 0); // field removed = default

        // Verify: new key can decrypt to original plaintext
        let (new_k1, new_k2) = new_config.encryption_key.unwrap();
        let mut new_cipher = XtsBlockCipher::new(new_k1, new_k2).unwrap();
        let mut device_data = fs::read(&target_path).unwrap();
        new_cipher.decrypt(&mut device_data, 0, total_sectors);
        assert_eq!(device_data, plaintext);
    }

    #[test]
    fn test_rekey_crash_recovery() {
        let dir = TempDir::new().unwrap();
        let (target_path, _metadata_path, config_path) = setup_test_device(dir.path(), 6, 4); // 4 stripes

        let kek = default_kek();
        let _config = DeviceConfig::load_from_file_with_kek(&config_path, &kek).unwrap();

        let old_key1 = [0u8; 32];
        let old_key2 = [1u8; 32];
        let mut old_cipher = XtsBlockCipher::new(old_key1.to_vec(), old_key2.to_vec()).unwrap();

        let sectors_per_stripe = 64u64;
        let total_sectors = sectors_per_stripe * 4;
        let plaintext: Vec<u8> = (0..total_sectors * SECTOR_SIZE as u64)
            .map(|i| (i % 256) as u8)
            .collect();

        // Encrypt and write initial data
        let mut encrypted = plaintext.clone();
        old_cipher.encrypt(&mut encrypted, 0, total_sectors);
        fs::write(&target_path, &encrypted).unwrap();

        // Simulate a partial rekey: rekey first 2 stripes manually
        let new_cipher = XtsBlockCipher::random().unwrap();
        let (new_k1, new_k2) = new_cipher.keys();

        // Re-encrypt first 2 stripes with new key
        let mut data = fs::read(&target_path).unwrap();
        let first_two_sectors = sectors_per_stripe * 2;
        let first_two_bytes = first_two_sectors as usize * SECTOR_SIZE;
        old_cipher.decrypt(&mut data[..first_two_bytes], 0, first_two_sectors);
        let mut new_cipher_clone = new_cipher.clone();
        new_cipher_clone.encrypt(&mut data[..first_two_bytes], 0, first_two_sectors);
        fs::write(&target_path, &data).unwrap();

        // Write config as if we crashed after 2 stripes
        let updater = ConfigUpdater::new(config_path.clone(), kek.clone());
        updater
            .start_rekey((&old_key1, &old_key2), (new_k1, new_k2))
            .unwrap();
        // Manually set progress to 2
        updater.update_progress(2).unwrap();

        // Reload config (simulating restart)
        let resumed_config = DeviceConfig::load_from_file_with_kek(&config_path, &kek).unwrap();
        assert_eq!(resumed_config.rekey_state, RekeyState::InProgress);
        assert_eq!(resumed_config.rekey_progress, 2);

        // Resume rekey
        run(&resumed_config, &config_path, &kek).unwrap();

        // Verify the whole device is now encrypted with new key
        let final_config = DeviceConfig::load_from_file_with_kek(&config_path, &kek).unwrap();
        let (fk1, fk2) = final_config.encryption_key.unwrap();
        let mut final_cipher = XtsBlockCipher::new(fk1, fk2).unwrap();
        let mut device_data = fs::read(&target_path).unwrap();
        final_cipher.decrypt(&mut device_data, 0, total_sectors);
        assert_eq!(device_data, plaintext);
    }

    #[test]
    fn test_rekey_idempotent() {
        let dir = TempDir::new().unwrap();
        let (target_path, _metadata_path, config_path) = setup_test_device(dir.path(), 6, 2);

        let kek = default_kek();
        let config = DeviceConfig::load_from_file_with_kek(&config_path, &kek).unwrap();

        let old_key1 = [0u8; 32];
        let old_key2 = [1u8; 32];
        let mut old_cipher = XtsBlockCipher::new(old_key1.to_vec(), old_key2.to_vec()).unwrap();

        let sectors_per_stripe = 64u64;
        let total_sectors = sectors_per_stripe * 2;
        let plaintext: Vec<u8> = (0..total_sectors * SECTOR_SIZE as u64)
            .map(|i| (i % 256) as u8)
            .collect();

        let mut encrypted = plaintext.clone();
        old_cipher.encrypt(&mut encrypted, 0, total_sectors);
        fs::write(&target_path, &encrypted).unwrap();

        // Run rekey once
        run(&config, &config_path, &kek).unwrap();

        let data_after_first = fs::read(&target_path).unwrap();

        // Read the new config, run rekey again (should be a fresh rekey with yet another key)
        let config2 = DeviceConfig::load_from_file_with_kek(&config_path, &kek).unwrap();
        run(&config2, &config_path, &kek).unwrap();

        // Verify: final data should be different (new random key)
        let data_after_second = fs::read(&target_path).unwrap();
        assert_ne!(data_after_first, data_after_second);

        // But decrypting with the final key should still yield original plaintext
        let final_config = DeviceConfig::load_from_file_with_kek(&config_path, &kek).unwrap();
        let (fk1, fk2) = final_config.encryption_key.unwrap();
        let mut final_cipher = XtsBlockCipher::new(fk1, fk2).unwrap();
        let mut device_data = fs::read(&target_path).unwrap();
        final_cipher.decrypt(&mut device_data, 0, total_sectors);
        assert_eq!(device_data, plaintext);
    }
}
