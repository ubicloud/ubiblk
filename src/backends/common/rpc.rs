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
    block_device::{
        bdev_ops::{shared_state::NORMAL, uploader::SnapshotCoordinator},
        BgWorkerRequest, DualKeyState, OpsSharedState, RekeyOperation, SnapshotOperation,
    },
    crypt::XtsBlockCipher,
    utils::umask_guard::UmaskGuard,
    Result,
};
use log::{error, info, warn};
use serde::Deserialize;
use serde_json::{json, Value};
use ubiblk_macros::error_context;

use crate::block_device::StatusReporter;

use std::sync::atomic::AtomicUsize;
use std::sync::{mpsc::Sender, RwLock};

const VERSION: &str = env!("CARGO_PKG_VERSION");

/// Handles snapshot-related RPC commands.
///
/// Shared across RPC handler threads via `Arc`. The `RwLock<Option<SnapshotCoordinator>>`
/// holds the active snapshot coordinator (if any).
pub struct SnapshotRpcHandler {
    ops_shared: OpsSharedState,
    bgworker_tx: Sender<BgWorkerRequest>,
    staging_device_factory:
        Box<dyn Fn() -> crate::Result<Box<dyn crate::block_device::BlockDevice>> + Send + Sync>,
    stripe_count: usize,
    stripe_size_bytes: u64,
    active_snapshot: RwLock<Option<SnapshotCoordinator>>,
    next_snapshot_id: AtomicUsize,
}

impl SnapshotRpcHandler {
    pub fn new(
        ops_shared: OpsSharedState,
        bgworker_tx: Sender<BgWorkerRequest>,
        staging_device_factory: Box<
            dyn Fn() -> crate::Result<Box<dyn crate::block_device::BlockDevice>> + Send + Sync,
        >,
        stripe_count: usize,
        stripe_size_bytes: u64,
    ) -> Self {
        SnapshotRpcHandler {
            ops_shared,
            bgworker_tx,
            staging_device_factory,
            stripe_count,
            stripe_size_bytes,
            active_snapshot: RwLock::new(None),
            next_snapshot_id: AtomicUsize::new(1),
        }
    }

    /// Handle the `create_snapshot` RPC command.
    pub fn create_snapshot(&self) -> Value {
        // Atomic claim — only one operation can run at a time
        if !self.ops_shared.try_begin_stalling() {
            return json!({ "error": "operation already in progress" });
        }

        let id = self.next_snapshot_id.fetch_add(1, Ordering::Relaxed) as u64;

        // Create staging device
        let staging_device = match (self.staging_device_factory)() {
            Ok(dev) => dev,
            Err(e) => {
                // Reset phase since we failed before starting
                self.ops_shared
                    .set_phase(crate::block_device::bdev_ops::shared_state::NORMAL);
                return json!({ "error": format!("failed to create staging device: {}", e) });
            }
        };

        // Create the snapshot operation
        let operation = SnapshotOperation::new(staging_device, id);
        let stripes_copied = operation.stripes_copied();
        let upload_error = operation.upload_error();

        // Create coordinator for status tracking
        let stripes_uploaded = Arc::new(AtomicUsize::new(0));
        let ops_shared = self.ops_shared.clone();
        let coordinator = SnapshotCoordinator {
            id,
            destination: crate::block_device::bdev_ops::uploader::ArchiveDestination::LocalFs {
                path: std::path::PathBuf::from("/tmp/snapshot"), // placeholder
            },
            stripe_count: self.stripe_count,
            stripe_size: self.stripe_size_bytes,
            stripes_copied: stripes_copied.clone(),
            stripes_uploaded: stripes_uploaded.clone(),
            upload_error: upload_error.clone(),
            upload_handle: Some(
                crate::block_device::bdev_ops::uploader::spawn_local_fs_mirror(
                    stripes_copied,
                    stripes_uploaded,
                    self.stripe_count,
                ),
            ),
            phase_fn: Box::new(move || ops_shared.phase()),
        };

        // Store coordinator
        if let Ok(mut guard) = self.active_snapshot.write() {
            *guard = Some(coordinator);
        }

        // Send to bgworker
        if let Err(e) = self.bgworker_tx.send(BgWorkerRequest::StartOperation {
            operation: Box::new(operation),
        }) {
            error!("Failed to send StartOperation to bgworker: {}", e);
            self.ops_shared
                .set_phase(crate::block_device::bdev_ops::shared_state::NORMAL);
            return json!({ "error": format!("failed to send operation to bgworker: {}", e) });
        }

        info!("Snapshot {} created", id);
        json!({
            "id": id,
            "stripe_count": self.stripe_count,
            "stripe_size_bytes": self.stripe_size_bytes,
            "total_bytes": self.stripe_count as u64 * self.stripe_size_bytes,
        })
    }

    /// Handle the `snapshot_status` RPC command.
    pub fn snapshot_status(&self) -> Value {
        let guard = match self.active_snapshot.read() {
            Ok(g) => g,
            Err(_) => return json!({ "error": "lock poisoned" }),
        };

        match &*guard {
            Some(coord) => {
                let status = coord.status();
                json!({
                    "id": status.id,
                    "state": format!("{:?}", status.state),
                    "stripes_copied": status.stripes_copied,
                    "stripes_uploaded": status.stripes_uploaded,
                    "stripe_count": status.stripe_count,
                    "error": status.error,
                })
            }
            None => json!({ "error": "no snapshot in progress" }),
        }
    }

    /// Handle the `cancel_snapshot` RPC command.
    pub fn cancel_snapshot(&self) -> Value {
        let phase = self.ops_shared.phase();
        if phase == crate::block_device::bdev_ops::shared_state::NORMAL {
            return json!({ "error": "no operation active" });
        }
        if let Err(e) = self.bgworker_tx.send(BgWorkerRequest::CancelOperation) {
            return json!({ "error": format!("failed to send cancel: {}", e) });
        }
        json!({ "result": "cancel requested" })
    }
}

/// Rekey status for RPC reporting.
#[derive(Debug)]
pub enum RekeyStatus {
    /// No rekey in progress.
    Idle,
    /// Rekey is stalling (draining in-flight IO).
    Stalling,
    /// Rekey is actively processing stripes.
    Operating {
        stripes_processed: usize,
        stripe_count: usize,
    },
}

/// Handles rekey-related RPC commands.
///
/// Shared across RPC handler threads via `Arc`.
pub struct RekeyRpcHandler {
    ops_shared: OpsSharedState,
    bgworker_tx: Sender<BgWorkerRequest>,
    stripe_count: usize,
    /// Tracks whether a rekey is in progress (for status reporting).
    rekey_active: Arc<AtomicBool>,
}

impl RekeyRpcHandler {
    pub fn new(
        ops_shared: OpsSharedState,
        bgworker_tx: Sender<BgWorkerRequest>,
        stripe_count: usize,
    ) -> Self {
        RekeyRpcHandler {
            ops_shared,
            bgworker_tx,
            stripe_count,
            rekey_active: Arc::new(AtomicBool::new(false)),
        }
    }

    /// Handle the `start_rekey` RPC command.
    ///
    /// Expects old and new XTS key pairs to be provided externally
    /// (from config with pending_encryption_key).
    pub fn start_rekey(&self, old_xts: XtsBlockCipher, new_xts: XtsBlockCipher) -> Value {
        // Atomic claim — only one operation can run at a time
        if !self.ops_shared.try_begin_stalling() {
            return json!({ "error": "operation already in progress" });
        }

        // Create DualKeyState and RekeyOperation
        let dual_key_state = Arc::new(DualKeyState::new(self.stripe_count));
        let operation = RekeyOperation::new(old_xts, new_xts, dual_key_state);

        // Mark rekey as active
        self.rekey_active.store(true, Ordering::Release);

        // Send to bgworker
        if let Err(e) = self.bgworker_tx.send(BgWorkerRequest::StartOperation {
            operation: Box::new(operation),
        }) {
            error!("Failed to send StartOperation to bgworker: {}", e);
            self.ops_shared.set_phase(NORMAL);
            self.rekey_active.store(false, Ordering::Release);
            return json!({ "error": format!("failed to send operation to bgworker: {}", e) });
        }

        info!("Rekey operation started for {} stripes", self.stripe_count);
        json!({
            "result": "rekey started",
            "stripe_count": self.stripe_count,
        })
    }

    /// Handle the `rekey_status` RPC command.
    pub fn rekey_status(&self) -> Value {
        if !self.rekey_active.load(Ordering::Acquire) {
            return json!({ "state": "idle" });
        }

        let phase = self.ops_shared.phase();
        match phase {
            crate::block_device::bdev_ops::shared_state::STALLING => {
                json!({
                    "state": "stalling",
                    "stripe_count": self.stripe_count,
                })
            }
            crate::block_device::bdev_ops::shared_state::OPERATING => {
                let processed = self.ops_shared.stripes_processed();
                json!({
                    "state": "operating",
                    "stripes_processed": processed,
                    "stripe_count": self.stripe_count,
                })
            }
            _ => {
                // Phase returned to normal — rekey completed (or failed)
                self.rekey_active.store(false, Ordering::Release);
                json!({ "state": "idle" })
            }
        }
    }
}

#[derive(Clone)]
struct RpcState {
    status_reporter: Option<StatusReporter>,
    io_trackers: Vec<IoTracker>,
    snapshot_handler: Option<Arc<SnapshotRpcHandler>>,
    rekey_handler: Option<Arc<RekeyRpcHandler>>,
}

#[derive(Deserialize)]
struct RpcRequest {
    command: String,
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
) -> Result<RpcServerHandle> {
    start_rpc_server_with_ops(path, status_reporter, io_trackers, None, None)
}

#[error_context("Failed to start RPC server on path: {path:?}")]
pub fn start_rpc_server_with_snapshot<P: AsRef<Path>>(
    path: P,
    status_reporter: Option<StatusReporter>,
    io_trackers: Vec<IoTracker>,
    snapshot_handler: Option<Arc<SnapshotRpcHandler>>,
) -> Result<RpcServerHandle> {
    start_rpc_server_with_ops(path, status_reporter, io_trackers, snapshot_handler, None)
}

#[error_context("Failed to start RPC server on path: {path:?}")]
pub fn start_rpc_server_with_ops<P: AsRef<Path>>(
    path: P,
    status_reporter: Option<StatusReporter>,
    io_trackers: Vec<IoTracker>,
    snapshot_handler: Option<Arc<SnapshotRpcHandler>>,
    rekey_handler: Option<Arc<RekeyRpcHandler>>,
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
        snapshot_handler,
        rekey_handler,
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
        "create_snapshot" => match &state.snapshot_handler {
            Some(handler) => handler.create_snapshot(),
            None => json!({ "error": "snapshot not supported" }),
        },
        "snapshot_status" => match &state.snapshot_handler {
            Some(handler) => handler.snapshot_status(),
            None => json!({ "error": "snapshot not supported" }),
        },
        "cancel_snapshot" => match &state.snapshot_handler {
            Some(handler) => handler.cancel_snapshot(),
            None => json!({ "error": "snapshot not supported" }),
        },
        "rekey_status" => match &state.rekey_handler {
            Some(handler) => handler.rekey_status(),
            None => json!({ "error": "rekey not supported" }),
        },
        other => json!({
            "error": format!("unknown command: {other}"),
        }),
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
        let mut stream = connect(socket_path);

        // Send request
        let request = json!({ "command": command }).to_string();
        stream
            .write_all(request.as_bytes())
            .expect("Failed to write to socket");
        stream.write_all(b"\n").expect("Failed to write newline"); // Important: logic expects read_line

        read_response(&mut stream)
    }

    fn wrapped_start_rpc_server(
        path: &Path,
        status_reporter: Option<StatusReporter>,
        io_trackers: Vec<IoTracker>,
    ) -> Result<RpcServerHandle> {
        let _l = UMASK_LOCK.lock().unwrap();
        start_rpc_server(path, status_reporter, io_trackers)
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
}
