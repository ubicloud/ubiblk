use std::{
    fs,
    io::{self, BufRead, BufReader, Write},
    os::unix::{
        fs::PermissionsExt,
        net::{UnixListener, UnixStream},
    },
    path::{Path, PathBuf},
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
    thread::JoinHandle,
};

use crate::{
    backends::common::io_tracking::{IoKind, IoTracker},
    utils::{s3::UpdatableS3Client, umask_guard::UmaskGuard},
    Result,
};
use log::{error, info, warn};
use serde::Deserialize;
use serde_json::{json, Value};
use ubiblk_macros::error_context;

use crate::block_device::StatusReporter;

const VERSION: &str = env!("CARGO_PKG_VERSION");

#[derive(Clone)]
struct RpcState {
    status_reporter: Option<StatusReporter>,
    io_trackers: Vec<IoTracker>,
    shared_s3_client: Option<Arc<UpdatableS3Client>>,
}

#[derive(Deserialize)]
struct RpcRequest {
    command: String,
    #[serde(default)]
    params: Option<Value>,
}

#[allow(dead_code)]
pub struct RpcServerHandle {
    join_handle: JoinHandle<()>,
    stop_requested: Arc<AtomicBool>,
    path: PathBuf,
}

#[allow(dead_code)]
impl RpcServerHandle {
    pub fn stop(self) -> Result<()> {
        self.stop_requested.store(true, Ordering::Release);

        // connect to the socket to unblock the listener
        UnixStream::connect(&self.path)?;

        self.join_handle.join().map_err(|_| {
            crate::ubiblk_error!(RpcError {
                description: "failed to join RPC server thread".to_string(),
            })
        })?;

        Ok(())
    }
}

#[error_context("Failed to start RPC server on path: {path:?}")]
pub fn start_rpc_server<P: AsRef<Path>>(
    path: P,
    status_reporter: Option<StatusReporter>,
    io_trackers: Vec<IoTracker>,
    shared_s3_client: Option<Arc<UpdatableS3Client>>,
) -> Result<RpcServerHandle> {
    let path = path.as_ref().to_path_buf();
    if let Err(e) = fs::remove_file(&path) {
        if e.kind() != io::ErrorKind::NotFound {
            return Err(crate::ubiblk_error!(RpcError {
                description: format!("failed to remove existing RPC socket {:?}: {e}", path),
            }));
        }
    }

    let listener = {
        let _um = UmaskGuard::set(0o117); // ensures 0660 max on creation
        UnixListener::bind(&path).map_err(|e| {
            crate::ubiblk_error!(RpcError {
                description: format!("failed to bind RPC socket {:?}: {e}", path),
            })
        })?
    };

    // Allow only owner and group to read/write the socket
    fs::set_permissions(&path, fs::Permissions::from_mode(0o660))?;

    let state = Arc::new(RpcState {
        status_reporter,
        io_trackers,
        shared_s3_client,
    });

    info!("RPC server listening on {:?}", path);

    let path_clone = path.clone();
    let stop_requested = Arc::new(AtomicBool::new(false));
    let stop_requested_clone = stop_requested.clone();
    let join_handle = std::thread::Builder::new()
        .name("ubiblk-rpc-listener".to_string())
        .spawn(move || run_listener(listener, state, path_clone, stop_requested_clone))
        .map_err(|e| crate::ubiblk_error!(ThreadCreation { source: e }))?;

    Ok(RpcServerHandle {
        join_handle,
        stop_requested,
        path,
    })
}

fn run_listener(
    listener: UnixListener,
    state: Arc<RpcState>,
    path: PathBuf,
    stop_requested: Arc<AtomicBool>,
) {
    for stream in listener.incoming() {
        if stop_requested.load(Ordering::Acquire) {
            info!("RPC shutdown signal received.");
            break;
        }

        match stream {
            Ok(stream) => {
                let state = state.clone();
                if let Err(e) = std::thread::Builder::new()
                    .name("ubiblk-rpc-client".to_string())
                    .spawn(move || handle_client(stream, state))
                {
                    error!("Failed to spawn RPC handler thread: {e}");
                }
            }
            Err(e) => {
                if e.kind() == io::ErrorKind::Interrupted {
                    continue;
                }
                error!("RPC listener error on {:?}: {e}", path);
                break;
            }
        }
    }

    if let Err(e) = fs::remove_file(&path) {
        if e.kind() != io::ErrorKind::NotFound {
            warn!("Failed to remove RPC socket {:?}: {e}", path);
        }
    }
}

fn handle_client(stream: UnixStream, state: Arc<RpcState>) {
    let mut reader = BufReader::new(stream);
    let mut line = String::new();

    loop {
        line.clear();
        match reader.read_line(&mut line) {
            Ok(0) => break,
            Ok(_) => {
                let trimmed = line.trim();
                if trimmed.is_empty() {
                    continue;
                }

                let response = match serde_json::from_str::<RpcRequest>(trimmed) {
                    Ok(request) => process_request(request, &state),
                    Err(e) => json!({
                        "error": format!("invalid request: {e}"),
                    }),
                };

                if let Err(e) = send_response(reader.get_mut(), &response) {
                    error!("Failed to send RPC response: {e}");
                    break;
                }
            }
            Err(e) => {
                error!("Failed to read RPC request: {e}");
                break;
            }
        }
    }
}

fn queue_snapshots(state: &RpcState) -> Vec<Value> {
    state
        .io_trackers
        .iter()
        .map(|tracker| {
            let ios: Vec<Value> = tracker
                .snapshot()
                .into_iter()
                .map(|(kind, offset, length)| match kind {
                    IoKind::Read => json!(["read", offset, length]),
                    IoKind::Write => json!(["write", offset, length]),
                    IoKind::Flush => json!(["flush"]),
                })
                .collect();
            json!(ios)
        })
        .collect()
}

fn process_request(request: RpcRequest, state: &RpcState) -> Value {
    match request.command.as_str() {
        "version" => json!({ "version": VERSION }),
        "status" => {
            let status = state.status_reporter.as_ref().map(StatusReporter::report);
            json!({ "status": status })
        }
        "queues" => {
            let queue_snapshots = queue_snapshots(state);
            json!({ "queues": queue_snapshots })
        }
        "stats" => {
            let queue_stats: Vec<Value> = state
                .io_trackers
                .iter()
                .map(|tracker| {
                    let (bytes_read, bytes_written, read_ops, write_ops, flush_ops) =
                        tracker.cumulative_stats();
                    json!({
                        "bytes_read": bytes_read,
                        "bytes_written": bytes_written,
                        "read_ops": read_ops,
                        "write_ops": write_ops,
                        "flush_ops": flush_ops,
                    })
                })
                .collect();
            json!({ "stats": { "queues": queue_stats } })
        }
        "update-credentials" => handle_update_credentials(request.params, state),
        other => json!({
            "error": format!("unknown command: {other}"),
        }),
    }
}

fn handle_update_credentials(params: Option<Value>, state: &RpcState) -> Value {
    let Some(shared_client) = &state.shared_s3_client else {
        return json!({ "error": "no S3 client configured for this device" });
    };

    let Some(params) = params else {
        return json!({ "error": "missing params for update-credentials" });
    };

    let key_id = match params.get("key_id").and_then(Value::as_str) {
        Some(v) => v.to_string(),
        None => return json!({ "error": "missing or invalid 'key_id' in params" }),
    };

    let secret_key = match params.get("secret_key").and_then(Value::as_str) {
        Some(v) => v.to_string(),
        None => return json!({ "error": "missing or invalid 'secret_key' in params" }),
    };

    let session_token = params
        .get("session_token")
        .and_then(Value::as_str)
        .map(String::from);

    match shared_client.update_credentials(key_id, secret_key, session_token) {
        Ok(()) => json!({ "result": "credentials updated" }),
        Err(e) => json!({ "error": format!("failed to update credentials: {e}") }),
    }
}

fn send_response(stream: &mut UnixStream, response: &Value) -> io::Result<()> {
    let mut payload = serde_json::to_vec(response).map_err(io::Error::other)?;
    payload.push(b'\n');
    stream.write_all(&payload)?;
    stream.flush()
}

#[cfg(test)]
mod tests {
    use crate::block_device::{
        metadata_flags, SharedMetadataState, UbiMetadata, DEFAULT_STRIPE_SECTOR_COUNT_SHIFT,
    };
    use crate::utils::umask_guard::UMASK_LOCK;

    use super::*;
    use serde_json::Value;
    use std::io::Write;
    use std::os::unix::net::UnixStream;
    use std::time::Duration;

    fn test_socket_path(test_name: &str) -> PathBuf {
        let mut path = std::env::temp_dir();
        path.push(format!("ubiblk_rpc_test_{}.sock", test_name));
        path
    }

    fn connect(socket_path: &Path) -> UnixStream {
        // Retry connection a few times to allow the server thread to spin up
        let mut stream = None;
        for _ in 0..10 {
            if let Ok(s) = UnixStream::connect(socket_path) {
                stream = Some(s);
                break;
            }
            std::thread::sleep(Duration::from_millis(50));
        }
        stream.expect("Failed to connect to RPC socket")
    }

    fn read_response(stream: &mut UnixStream) -> Value {
        let mut reader = std::io::BufReader::new(stream);
        let mut response_line = String::new();
        reader
            .read_line(&mut response_line)
            .expect("Failed to read response");

        serde_json::from_str(&response_line).expect("Failed to parse response JSON")
    }

    fn rpc_call(socket_path: &Path, command: &str) -> Value {
        rpc_call_with_params(socket_path, command, None)
    }

    fn rpc_call_with_params(socket_path: &Path, command: &str, params: Option<Value>) -> Value {
        let mut stream = connect(socket_path);

        // Send request
        let mut request = json!({ "command": command });
        if let Some(params) = params {
            request["params"] = params;
        }
        let request_str = request.to_string();
        stream
            .write_all(request_str.as_bytes())
            .expect("Failed to write to socket");
        stream.write_all(b"\n").expect("Failed to write newline");

        read_response(&mut stream)
    }

    fn wrapped_start_rpc_server(
        path: &Path,
        status_reporter: Option<StatusReporter>,
        io_trackers: Vec<IoTracker>,
    ) -> Result<RpcServerHandle> {
        let _l = UMASK_LOCK.lock().unwrap();
        start_rpc_server(path, status_reporter, io_trackers, None)
    }

    #[test]
    fn test_nonexistent_directory_socket_path() {
        let bad_path = PathBuf::from("/nonexistent_directory/ubiblk_rpc.sock");
        let result = wrapped_start_rpc_server(&bad_path, None, vec![]);
        assert!(result.is_err());
    }

    #[test]
    fn test_non_removable_socket_path() {
        // Make the would-be socket path an existing directory: current dir.
        // This is reliably not removable via `remove_file()`.
        let bad_path = std::env::current_dir().unwrap();

        let result = wrapped_start_rpc_server(&bad_path, None, vec![]);
        assert!(result.is_err());
        assert!(result
            .err()
            .unwrap()
            .to_string()
            .contains("failed to remove existing RPC socket"));
    }

    #[test]
    fn test_rpc_version() {
        let path = test_socket_path("version");

        // Start server with no trackers and no reporter
        let handle =
            wrapped_start_rpc_server(&path, None, vec![]).expect("Failed to start RPC server");

        let response = rpc_call(&path, "version");

        handle.stop().expect("Failed to stop RPC server");

        // Assert the version matches the const
        assert_eq!(response["version"], VERSION);
    }

    #[test]
    fn test_rpc_status() {
        let path = test_socket_path("status");
        let mut metadata = UbiMetadata::new(DEFAULT_STRIPE_SECTOR_COUNT_SHIFT, 64, 16);

        metadata.stripe_headers[0] |= metadata_flags::FETCHED;
        metadata.stripe_headers[2] |= metadata_flags::FETCHED;

        let shared_state = SharedMetadataState::new(&metadata);
        let reporter = StatusReporter::new(shared_state, 64 * 2048);

        let handle = wrapped_start_rpc_server(&path, Some(reporter), vec![])
            .expect("Failed to start RPC server");

        let response = rpc_call(&path, "status");
        handle.stop().expect("Failed to stop RPC server");

        assert!(response.get("status").is_some());
        let status = &response["status"];
        assert!(status.get("stripes").is_some());
        let stripes = &status["stripes"];
        assert_eq!(stripes["fetched"], 2);
        assert_eq!(stripes["source"], 16);
        assert_eq!(stripes["total"], 64);
    }

    #[test]
    fn test_rpc_status_empty() {
        let path = test_socket_path("status_empty");

        // Start server with None for status_reporter
        let handle =
            wrapped_start_rpc_server(&path, None, vec![]).expect("Failed to start RPC server");

        let response = rpc_call(&path, "status");

        handle.stop().expect("Failed to stop RPC server");

        // Should return null for status
        assert!(response.get("status").is_some());
        assert!(response["status"].is_null());
    }

    #[test]
    fn test_rpc_queues() {
        let path = test_socket_path("queues");

        let io_tracker_1 = IoTracker::new(4);
        io_tracker_1.add_flush(0);
        io_tracker_1.add_read(1, 2, 3);
        io_tracker_1.add_write(2, 4, 5);
        io_tracker_1.add_flush(3);

        let io_tracker_2 = IoTracker::new(4);
        io_tracker_2.add_write(2, 10, 20);

        let io_tracker_3 = IoTracker::new(4);
        // No IOs added to tracker 3

        let io_trackers = vec![io_tracker_1, io_tracker_2, io_tracker_3];

        // Start server with multiple trackers and no reporter
        let handle =
            wrapped_start_rpc_server(&path, None, io_trackers).expect("Failed to start RPC server");

        let response = rpc_call(&path, "queues");

        handle.stop().expect("Failed to stop RPC server");

        // Should return array with 3 queues (one per tracker)
        assert!(response["queues"].is_array());
        let queues = response["queues"].as_array().unwrap();
        assert_eq!(queues.len(), 3);
        assert_eq!(
            queues[0],
            json!([["flush"], ["read", 2, 3], ["write", 4, 5], ["flush"]])
        );
        assert_eq!(queues[1], json!([["write", 10, 20]]));
        assert_eq!(queues[2], json!([]));
    }

    #[test]
    fn test_rpc_queues_empty() {
        let path = test_socket_path("queues_empty");

        // Start server with empty trackers vector
        let handle =
            wrapped_start_rpc_server(&path, None, vec![]).expect("Failed to start RPC server");

        let response = rpc_call(&path, "queues");

        handle.stop().expect("Failed to stop RPC server");

        // Should return empty array
        assert!(response["queues"].is_array());
        assert_eq!(response["queues"].as_array().unwrap().len(), 0);
    }

    #[test]
    fn test_rpc_unknown_command() {
        let path = test_socket_path("unknown");
        let handle =
            wrapped_start_rpc_server(&path, None, vec![]).expect("Failed to start RPC server");

        let response = rpc_call(&path, "destroy_world");

        handle.stop().expect("Failed to stop RPC server");

        // Should return an error field
        assert!(response.get("error").is_some());
        let error_msg = response["error"].as_str().unwrap();
        assert!(error_msg.contains("unknown command"));
    }

    #[test]
    fn test_ignore_empty_lines() {
        let path = test_socket_path("empty_lines");
        let handle =
            wrapped_start_rpc_server(&path, None, vec![]).expect("Failed to start RPC server");

        let mut stream = connect(&path);

        // Send empty lines and then a valid command
        stream.write_all(b"\n\n\n").unwrap();
        let request = json!({ "command": "version" }).to_string();
        stream.write_all(request.as_bytes()).unwrap();
        stream.write_all(b"\n").unwrap();

        let response = read_response(&mut stream);

        handle.stop().expect("Failed to stop RPC server");

        assert_eq!(response["version"], VERSION);
    }

    #[test]
    fn test_rpc_malformed_json() {
        let path = test_socket_path("malformed");
        let handle =
            wrapped_start_rpc_server(&path, None, vec![]).expect("Failed to start RPC server");

        let mut stream = connect(&path);

        // Manually writing garbage to stream instead of using helper
        stream.write_all(b"{ not valid json }\n").unwrap();

        let mut reader = std::io::BufReader::new(stream);
        let mut response_line = String::new();
        reader.read_line(&mut response_line).unwrap();

        let response: Value = serde_json::from_str(&response_line).unwrap();

        handle.stop().expect("Failed to stop RPC server");

        assert!(response.get("error").is_some());
        assert!(response["error"]
            .as_str()
            .unwrap()
            .contains("invalid request"));
    }

    #[test]
    fn test_rpc_stats() {
        let path = test_socket_path("stats");

        let io_tracker_1 = IoTracker::new(4);
        io_tracker_1.add_read(0, 100, 8); // 8 sectors = 4096 bytes
        io_tracker_1.add_write(1, 200, 16); // 16 sectors = 8192 bytes
        io_tracker_1.add_flush(2);

        let io_tracker_2 = IoTracker::new(4);
        io_tracker_2.add_write(0, 50, 10); // 10 sectors = 5120 bytes
        io_tracker_2.add_read(1, 75, 20); // 20 sectors = 10240 bytes
        io_tracker_2.add_read(2, 100, 5); // 5 sectors = 2560 bytes

        let io_tracker_3 = IoTracker::new(4);
        // No IOs added to tracker 3

        let io_trackers = vec![io_tracker_1, io_tracker_2, io_tracker_3];

        let handle =
            wrapped_start_rpc_server(&path, None, io_trackers).expect("Failed to start RPC server");

        let response = rpc_call(&path, "stats");

        handle.stop().expect("Failed to stop RPC server");

        // Verify response structure
        assert!(response.get("stats").is_some());
        let stats = &response["stats"];
        assert!(stats.get("queues").is_some());
        let queues = stats["queues"].as_array().unwrap();
        assert_eq!(queues.len(), 3);

        // Verify tracker 1 stats
        assert_eq!(queues[0]["bytes_read"], 4096);
        assert_eq!(queues[0]["bytes_written"], 8192);
        assert_eq!(queues[0]["read_ops"], 1);
        assert_eq!(queues[0]["write_ops"], 1);
        assert_eq!(queues[0]["flush_ops"], 1);

        // Verify tracker 2 stats
        assert_eq!(queues[1]["bytes_read"], 12800); // 10240 + 2560
        assert_eq!(queues[1]["bytes_written"], 5120);
        assert_eq!(queues[1]["read_ops"], 2);
        assert_eq!(queues[1]["write_ops"], 1);
        assert_eq!(queues[1]["flush_ops"], 0);

        // Verify tracker 3 stats (all zeros)
        assert_eq!(queues[2]["bytes_read"], 0);
        assert_eq!(queues[2]["bytes_written"], 0);
        assert_eq!(queues[2]["read_ops"], 0);
        assert_eq!(queues[2]["write_ops"], 0);
        assert_eq!(queues[2]["flush_ops"], 0);
    }

    #[test]
    fn test_rpc_stats_empty() {
        let path = test_socket_path("stats_empty");

        // Start server with empty trackers vector
        let handle =
            wrapped_start_rpc_server(&path, None, vec![]).expect("Failed to start RPC server");

        let response = rpc_call(&path, "stats");

        handle.stop().expect("Failed to stop RPC server");

        // Should return empty array
        assert!(response.get("stats").is_some());
        let stats = &response["stats"];
        assert!(stats.get("queues").is_some());
        assert_eq!(stats["queues"].as_array().unwrap().len(), 0);
    }

    fn start_rpc_server_with_s3(
        path: &Path,
        shared_s3_client: Option<Arc<crate::utils::s3::UpdatableS3Client>>,
    ) -> Result<RpcServerHandle> {
        let _l = UMASK_LOCK.lock().unwrap();
        start_rpc_server(path, None, vec![], shared_s3_client)
    }

    #[test]
    fn test_rpc_update_credentials_no_s3_client() {
        let path = test_socket_path("update_creds_no_client");
        let handle =
            start_rpc_server_with_s3(&path, None).expect("Failed to start RPC server");

        let response = rpc_call_with_params(
            &path,
            "update-credentials",
            Some(json!({
                "key_id": "AKIA123",
                "secret_key": "secret123"
            })),
        );

        handle.stop().expect("Failed to stop RPC server");
        assert!(response["error"]
            .as_str()
            .unwrap()
            .contains("no S3 client"));
    }

    #[test]
    fn test_rpc_update_credentials_missing_params() {
        let path = test_socket_path("update_creds_no_params");
        let client = crate::utils::s3::UpdatableS3Client::new(
            crate::utils::s3::build_s3_client(
                &crate::utils::s3::create_runtime().unwrap(),
                None,
                None,
                None,
                None,
            )
            .unwrap(),
            None,
            None,
        );
        let shared = Arc::new(client);
        let handle =
            start_rpc_server_with_s3(&path, Some(shared)).expect("Failed to start RPC server");

        let response = rpc_call(&path, "update-credentials");

        handle.stop().expect("Failed to stop RPC server");
        assert!(response["error"]
            .as_str()
            .unwrap()
            .contains("missing params"));
    }

    #[test]
    fn test_rpc_update_credentials_missing_key_id() {
        let path = test_socket_path("update_creds_no_key");
        let client = crate::utils::s3::UpdatableS3Client::new(
            crate::utils::s3::build_s3_client(
                &crate::utils::s3::create_runtime().unwrap(),
                None,
                None,
                None,
                None,
            )
            .unwrap(),
            None,
            None,
        );
        let shared = Arc::new(client);
        let handle =
            start_rpc_server_with_s3(&path, Some(shared)).expect("Failed to start RPC server");

        let response = rpc_call_with_params(
            &path,
            "update-credentials",
            Some(json!({ "secret_key": "secret" })),
        );

        handle.stop().expect("Failed to stop RPC server");
        assert!(response["error"]
            .as_str()
            .unwrap()
            .contains("key_id"));
    }

    #[test]
    fn test_rpc_update_credentials_success() {
        let path = test_socket_path("update_creds_ok");
        let client = crate::utils::s3::UpdatableS3Client::new(
            crate::utils::s3::build_s3_client(
                &crate::utils::s3::create_runtime().unwrap(),
                None,
                Some("http://localhost:9999"),
                Some("auto"),
                None,
            )
            .unwrap(),
            Some("http://localhost:9999".to_string()),
            Some("auto".to_string()),
        );
        let shared = Arc::new(client);
        let handle =
            start_rpc_server_with_s3(&path, Some(shared)).expect("Failed to start RPC server");

        let response = rpc_call_with_params(
            &path,
            "update-credentials",
            Some(json!({
                "key_id": "AKIA_NEW_KEY",
                "secret_key": "new_secret_key",
                "session_token": "new_session_token"
            })),
        );

        handle.stop().expect("Failed to stop RPC server");
        assert_eq!(response["result"], "credentials updated");
    }
}
