//! End-to-end integration tests for the snapshot feature.
//!
//! These tests exercise the full snapshot flow: set up a device with metadata,
//! write data, trigger snapshot via RPC, verify data integrity and COW behavior,
//! verify snapshot_status, and test error paths.

#[cfg(test)]
mod tests {
    use std::io::{BufRead, Write};
    use std::os::unix::net::UnixStream;
    use std::path::{Path, PathBuf};
    use std::time::Duration;

    use serde_json::{json, Value};
    use tempfile::TempDir;

    use crate::backends::common::{init_metadata, run_backend_loop, SECTOR_SIZE};
    use crate::block_device::{shared_buffer, IoChannel, DEFAULT_STRIPE_SECTOR_COUNT_SHIFT};
    use crate::config::v2::{self, DeviceSection};
    use crate::utils::umask_guard::UMASK_LOCK;

    const STRIPE_SHIFT: u8 = DEFAULT_STRIPE_SECTOR_COUNT_SHIFT; // 11
    const STRIPE_SECTORS: u64 = 1u64 << STRIPE_SHIFT; // 2048 sectors per stripe
    const STRIPE_SIZE: u64 = STRIPE_SECTORS * SECTOR_SIZE as u64; // 1 MiB
    const DISK_SIZE: u64 = STRIPE_SIZE * 4; // 4 MiB

    fn test_config(
        data_path: &Path,
        metadata_path: Option<&Path>,
        rpc_socket: Option<&Path>,
    ) -> v2::Config {
        v2::Config {
            device: DeviceSection {
                data_path: data_path.to_path_buf(),
                metadata_path: metadata_path.map(|p| p.to_path_buf()),
                vhost_socket: None,
                rpc_socket: rpc_socket.map(|p| p.to_path_buf()),
                device_id: "ubiblk-test".to_string(),
                track_written: false,
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

    fn setup_test_device(dir: &TempDir) -> (PathBuf, PathBuf) {
        let data_path = dir.path().join("data.img");
        let metadata_path = dir.path().join("metadata.bin");

        let data_file = std::fs::OpenOptions::new()
            .create(true)
            .read(true)
            .write(true)
            .open(&data_path)
            .unwrap();
        data_file.set_len(DISK_SIZE).unwrap();
        data_file.sync_all().unwrap();

        let meta_file = std::fs::OpenOptions::new()
            .create(true)
            .read(true)
            .write(true)
            .open(&metadata_path)
            .unwrap();
        meta_file.set_len(8 * 1024 * 1024).unwrap();
        meta_file.sync_all().unwrap();

        let config = test_config(&data_path, Some(&metadata_path), None);
        init_metadata(&config, STRIPE_SHIFT).unwrap();

        (data_path, metadata_path)
    }

    fn rpc_connect(socket_path: &Path) -> UnixStream {
        let mut stream = None;
        for _ in 0..20 {
            if let Ok(s) = UnixStream::connect(socket_path) {
                stream = Some(s);
                break;
            }
            std::thread::sleep(Duration::from_millis(50));
        }
        stream.expect("Failed to connect to RPC socket")
    }

    fn rpc_call_json(socket_path: &Path, request: Value) -> Value {
        let mut stream = rpc_connect(socket_path);
        stream
            .set_read_timeout(Some(Duration::from_secs(60)))
            .unwrap();
        let payload = request.to_string();
        stream.write_all(payload.as_bytes()).unwrap();
        stream.write_all(b"\n").unwrap();
        stream.flush().unwrap();

        let mut reader = std::io::BufReader::new(stream);
        let mut response_line = String::new();
        reader
            .read_line(&mut response_line)
            .expect("Failed to read RPC response");
        serde_json::from_str(&response_line).expect("Failed to parse RPC response JSON")
    }

    fn rpc_call(socket_path: &Path, command: &str) -> Value {
        rpc_call_json(socket_path, json!({ "command": command }))
    }

    /// Trigger a snapshot via RPC while polling the channel to participate in
    /// the drain/resume cycle. The RPC snapshot command blocks until the
    /// snapshot completes, but the channel must poll() to drain and resume.
    fn trigger_snapshot_with_poll(
        rpc_path: &Path,
        channel: &mut Box<dyn IoChannel>,
        new_data_path: &Path,
        new_metadata_path: &Path,
    ) -> Value {
        let rpc_path = rpc_path.to_path_buf();
        let ndp = new_data_path.to_path_buf();
        let nmp = new_metadata_path.to_path_buf();

        // Send the RPC from a background thread (it blocks until snapshot completes).
        let rpc_thread = std::thread::spawn(move || {
            rpc_call_json(
                &rpc_path,
                json!({
                    "command": "snapshot",
                    "new_data_path": ndp.to_str().unwrap(),
                    "new_metadata_path": nmp.to_str().unwrap()
                }),
            )
        });

        // Poll the channel to participate in drain/resume until the RPC thread finishes.
        let deadline = std::time::Instant::now() + Duration::from_secs(60);
        loop {
            channel.poll();
            if rpc_thread.is_finished() {
                break;
            }
            if std::time::Instant::now() > deadline {
                panic!("trigger_snapshot_with_poll timed out");
            }
            std::thread::sleep(Duration::from_millis(1));
        }

        rpc_thread.join().expect("RPC thread panicked")
    }

    fn write_stripe(channel: &mut Box<dyn IoChannel>, stripe_index: u64, pattern_byte: u8) {
        let sector_offset = stripe_index * STRIPE_SECTORS;
        let buf = shared_buffer(STRIPE_SIZE as usize);
        {
            let mut b = buf.borrow_mut();
            b.as_mut_slice()[..STRIPE_SIZE as usize].fill(pattern_byte);
        }
        channel.add_write(sector_offset, STRIPE_SECTORS as u32, buf, 1);
        channel.submit().unwrap();
        let results = poll_until_done(channel);
        assert!(
            results.iter().all(|(_, ok)| *ok),
            "write_stripe failed: {:?}",
            results
        );
    }

    fn read_stripe(channel: &mut Box<dyn IoChannel>, stripe_index: u64) -> u8 {
        let sector_offset = stripe_index * STRIPE_SECTORS;
        let buf = shared_buffer(STRIPE_SIZE as usize);
        channel.add_read(sector_offset, STRIPE_SECTORS as u32, buf.clone(), 2);
        channel.submit().unwrap();
        let results = poll_until_done(channel);
        assert!(
            results.iter().all(|(_, ok)| *ok),
            "read_stripe failed: {:?}",
            results
        );
        let b = buf.borrow();
        let first = b.as_slice()[0];
        assert!(
            b.as_slice()[..STRIPE_SIZE as usize]
                .iter()
                .all(|&x| x == first),
            "stripe data is not uniform: first={first:#x}"
        );
        first
    }

    fn poll_until_done(channel: &mut Box<dyn IoChannel>) -> Vec<(usize, bool)> {
        let mut all_results = Vec::new();
        let deadline = std::time::Instant::now() + Duration::from_secs(10);
        loop {
            let results = channel.poll();
            all_results.extend(results);
            if !channel.busy() {
                break;
            }
            if std::time::Instant::now() > deadline {
                panic!("poll_until_done timed out");
            }
            std::thread::sleep(Duration::from_millis(1));
        }
        all_results
    }

    /// Test 1: Basic snapshot lifecycle
    ///
    /// Write known data, trigger snapshot via RPC, verify data integrity
    /// (COW reads from old disk), write new data, verify new data goes to new file.
    #[test]
    fn test_snapshot_basic_lifecycle() {
        let _umask = UMASK_LOCK.lock().unwrap();
        let dir = TempDir::new().unwrap();
        let (data_path, metadata_path) = setup_test_device(&dir);
        let rpc_path = dir.path().join("rpc.sock");

        let config = test_config(&data_path, Some(&metadata_path), Some(&rpc_path));

        let new_data_path = dir.path().join("snap1_data.img");
        let new_metadata_path = dir.path().join("snap1_metadata.bin");

        run_backend_loop(&config, "test-snapshot", false, |env| {
            let bdev = env.bdev();
            let mut channel = bdev.create_channel().unwrap();

            // Write known data: stripe 0 = 0xAA, stripe 1 = 0xBB
            write_stripe(&mut channel, 0, 0xAA);
            write_stripe(&mut channel, 1, 0xBB);

            // Verify writes
            assert_eq!(read_stripe(&mut channel, 0), 0xAA);
            assert_eq!(read_stripe(&mut channel, 1), 0xBB);

            // Trigger snapshot via RPC (polls channel for drain/resume)
            let response = trigger_snapshot_with_poll(
                &rpc_path,
                &mut channel,
                &new_data_path,
                &new_metadata_path,
            );

            // Verify snapshot success
            assert!(
                response.get("snapshot").is_some(),
                "snapshot failed: {response}"
            );
            assert_eq!(response["snapshot"]["status"], "initiated");
            let snapshot_id = response["snapshot"]["snapshot_id"].as_str().unwrap();
            assert!(
                snapshot_id.starts_with("snap-"),
                "bad snapshot_id: {snapshot_id}"
            );

            // Read back data — should still see original patterns (served from COW source)
            assert_eq!(read_stripe(&mut channel, 0), 0xAA);
            assert_eq!(read_stripe(&mut channel, 1), 0xBB);

            // Write new data to stripe 0
            write_stripe(&mut channel, 0, 0xCC);

            // Read stripe 0 — should see new data (0xCC)
            assert_eq!(read_stripe(&mut channel, 0), 0xCC);
            // Read stripe 1 — should still see old data (0xBB) from COW source
            assert_eq!(read_stripe(&mut channel, 1), 0xBB);

            // Verify new files exist with correct permissions (0o600)
            assert!(new_data_path.exists(), "new data file not created");
            assert!(new_metadata_path.exists(), "new metadata file not created");

            use std::os::unix::fs::PermissionsExt;
            let data_mode = std::fs::metadata(&new_data_path)
                .unwrap()
                .permissions()
                .mode()
                & 0o777;
            let meta_mode = std::fs::metadata(&new_metadata_path)
                .unwrap()
                .permissions()
                .mode()
                & 0o777;
            assert_eq!(data_mode, 0o600, "new data file has wrong permissions");
            assert_eq!(meta_mode, 0o600, "new metadata file has wrong permissions");

            Ok(())
        })
        .unwrap();
    }

    /// Test 2: snapshot_status RPC
    ///
    /// Check status before and after snapshot.
    #[test]
    fn test_snapshot_status_rpc() {
        let _umask = UMASK_LOCK.lock().unwrap();
        let dir = TempDir::new().unwrap();
        let (data_path, metadata_path) = setup_test_device(&dir);
        let rpc_path = dir.path().join("rpc.sock");

        let config = test_config(&data_path, Some(&metadata_path), Some(&rpc_path));

        let new_data_path = dir.path().join("snap1_data.img");
        let new_metadata_path = dir.path().join("snap1_metadata.bin");

        run_backend_loop(&config, "test-status", false, |env| {
            let bdev = env.bdev();
            let mut channel = bdev.create_channel().unwrap();

            // Check initial status: idle, no last_snapshot
            let response = rpc_call(&rpc_path, "snapshot_status");
            let status = &response["snapshot_status"];
            assert_eq!(status["state"], "idle");
            assert!(status["last_snapshot"].is_null());

            // Trigger snapshot (polls channel for drain/resume)
            let snap_response = trigger_snapshot_with_poll(
                &rpc_path,
                &mut channel,
                &new_data_path,
                &new_metadata_path,
            );
            assert!(
                snap_response.get("snapshot").is_some(),
                "snapshot failed: {snap_response}"
            );

            // Check status after snapshot: idle with last_snapshot showing success
            let response = rpc_call(&rpc_path, "snapshot_status");
            let status = &response["snapshot_status"];
            assert_eq!(status["state"], "idle");

            let last = &status["last_snapshot"];
            assert!(!last.is_null(), "last_snapshot should not be null");
            assert_eq!(last["result"], "success");
            assert_eq!(last["new_data_path"], new_data_path.to_str().unwrap());
            assert_eq!(
                last["new_metadata_path"],
                new_metadata_path.to_str().unwrap()
            );
            assert!(last["completed_at_unix"].as_u64().unwrap() > 0);

            Ok(())
        })
        .unwrap();
    }

    /// Test 3: Second snapshot rejected (single-level enforcement)
    ///
    /// After a successful snapshot, a second snapshot should be rejected.
    #[test]
    fn test_snapshot_second_rejected() {
        let _umask = UMASK_LOCK.lock().unwrap();
        let dir = TempDir::new().unwrap();
        let (data_path, metadata_path) = setup_test_device(&dir);
        let rpc_path = dir.path().join("rpc.sock");

        let config = test_config(&data_path, Some(&metadata_path), Some(&rpc_path));

        run_backend_loop(&config, "test-reject", false, |env| {
            let bdev = env.bdev();
            let mut channel = bdev.create_channel().unwrap();

            // First snapshot: should succeed
            let snap1_data = dir.path().join("snap1_data.img");
            let snap1_meta = dir.path().join("snap1_meta.bin");
            let response = trigger_snapshot_with_poll(
                &rpc_path,
                &mut channel,
                &snap1_data,
                &snap1_meta,
            );
            assert!(
                response.get("snapshot").is_some(),
                "first snapshot failed: {response}"
            );

            // Second snapshot: should be rejected (single-level enforcement).
            // This goes through the coordinator which checks snapshot_active flag,
            // so no drain is needed — the RPC call returns immediately with error.
            let snap2_data = dir.path().join("snap2_data.img");
            let snap2_meta = dir.path().join("snap2_meta.bin");
            let response = trigger_snapshot_with_poll(
                &rpc_path,
                &mut channel,
                &snap2_data,
                &snap2_meta,
            );
            assert!(
                response.get("error").is_some(),
                "second snapshot should fail: {response}"
            );
            let error = response["error"].as_str().unwrap();
            assert!(
                error.contains("already active"),
                "unexpected error: {error}"
            );

            // The second data file should NOT have been created
            assert!(!snap2_data.exists(), "second data file should not exist");

            Ok(())
        })
        .unwrap();
    }

    /// Test 4: Snapshot with no metadata layer
    ///
    /// A device without metadata_path cannot snapshot.
    #[test]
    fn test_snapshot_no_metadata() {
        let _umask = UMASK_LOCK.lock().unwrap();
        let dir = TempDir::new().unwrap();
        let data_path = dir.path().join("data.img");
        let rpc_path = dir.path().join("rpc.sock");

        let data_file = std::fs::OpenOptions::new()
            .create(true)
            .read(true)
            .write(true)
            .open(&data_path)
            .unwrap();
        data_file.set_len(DISK_SIZE).unwrap();
        data_file.sync_all().unwrap();

        let config = test_config(&data_path, None, Some(&rpc_path));

        run_backend_loop(&config, "test-no-meta", false, |env| {
            // snapshot_cmd_sender is None without metadata — RPC returns error immediately
            let response = rpc_call_json(
                &rpc_path,
                json!({
                    "command": "snapshot",
                    "new_data_path": "/tmp/data",
                    "new_metadata_path": "/tmp/meta"
                }),
            );
            assert!(
                response.get("error").is_some(),
                "should fail without metadata: {response}"
            );
            let error = response["error"].as_str().unwrap();
            assert!(
                error.contains("metadata layer"),
                "unexpected error: {error}"
            );

            // Device should still be operational
            let bdev = env.bdev();
            let mut channel = bdev.create_channel().unwrap();
            let buf = shared_buffer(SECTOR_SIZE);
            channel.add_read(0, 1, buf.clone(), 1);
            channel.submit().unwrap();
            let results = poll_until_done(&mut channel);
            assert!(
                results.iter().all(|(_, ok)| *ok),
                "read after failed snapshot should work"
            );

            Ok(())
        })
        .unwrap();
    }

    /// Test 5: Snapshot with invalid paths
    ///
    /// Non-existent directory should fail, device should continue working.
    #[test]
    fn test_snapshot_invalid_paths() {
        let _umask = UMASK_LOCK.lock().unwrap();
        let dir = TempDir::new().unwrap();
        let (data_path, metadata_path) = setup_test_device(&dir);
        let rpc_path = dir.path().join("rpc.sock");

        let config = test_config(&data_path, Some(&metadata_path), Some(&rpc_path));

        run_backend_loop(&config, "test-bad-path", false, |env| {
            let bdev = env.bdev();
            let mut channel = bdev.create_channel().unwrap();

            // Write some data first
            write_stripe(&mut channel, 0, 0xDD);

            // Attempt snapshot with non-existent directory
            let response = trigger_snapshot_with_poll(
                &rpc_path,
                &mut channel,
                Path::new("/nonexistent/dir/data.img"),
                Path::new("/nonexistent/dir/meta.bin"),
            );
            assert!(
                response.get("error").is_some(),
                "snapshot to bad path should fail: {response}"
            );

            // Verify snapshot_status shows failure
            let status_response = rpc_call(&rpc_path, "snapshot_status");
            let last = &status_response["snapshot_status"]["last_snapshot"];
            assert_eq!(last["result"], "failed");

            // Device should still be operational after failed snapshot
            assert_eq!(
                read_stripe(&mut channel, 0),
                0xDD,
                "read after failed snapshot should return original data"
            );

            // Write new data should also work
            write_stripe(&mut channel, 0, 0xEE);
            assert_eq!(read_stripe(&mut channel, 0), 0xEE);

            Ok(())
        })
        .unwrap();
    }
}
