use std::{
    fs,
    io::{self, BufRead, BufReader, Write},
    os::unix::net::{UnixListener, UnixStream},
    path::{Path, PathBuf},
    sync::{mpsc, Arc},
    thread::JoinHandle,
    time::Duration,
};

use crate::{
    vhost_backend::io_tracking::{IoKind, IoTracker},
    Result, VhostUserBlockError,
};
use log::{error, info, warn};
use serde::Deserialize;
use serde_json::{json, Value};

use crate::block_device::{
    BgWorkerDebugInfo, BgWorkerRequest, SharedMetadataState, StatusReporter,
};

const VERSION: &str = env!("CARGO_PKG_VERSION");

#[derive(Clone)]
struct RpcState {
    status_reporter: Option<StatusReporter>,
    io_trackers: Vec<IoTracker>,
    bgworker_sender: Option<mpsc::Sender<BgWorkerRequest>>,
    shared_metadata_state: Option<SharedMetadataState>,
}

#[derive(Deserialize)]
struct RpcRequest {
    command: String,
    #[serde(default)]
    args: Value,
}

#[derive(Deserialize)]
struct DebugHeadersArgs {
    start: usize,
    end: usize,
}

pub fn start_rpc_server<P: AsRef<Path>>(
    path: P,
    status_reporter: Option<StatusReporter>,
    io_trackers: Vec<IoTracker>,
    bgworker_sender: Option<mpsc::Sender<BgWorkerRequest>>,
    shared_metadata_state: Option<SharedMetadataState>,
) -> Result<JoinHandle<()>> {
    let path = path.as_ref().to_path_buf();
    if let Err(e) = fs::remove_file(&path) {
        if e.kind() != io::ErrorKind::NotFound {
            return Err(VhostUserBlockError::Other {
                description: format!("failed to remove existing RPC socket {:?}: {e}", path),
            });
        }
    }

    let listener = UnixListener::bind(&path).map_err(|e| VhostUserBlockError::Other {
        description: format!("failed to bind RPC socket {:?}: {e}", path),
    })?;
    let state = Arc::new(RpcState {
        status_reporter,
        io_trackers,
        bgworker_sender,
        shared_metadata_state,
    });

    info!("RPC server listening on {:?}", path);

    std::thread::Builder::new()
        .name("ubiblk-rpc-listener".to_string())
        .spawn(move || run_listener(listener, state, path))
        .map_err(|e| VhostUserBlockError::Other {
            description: e.to_string(),
        })
}

fn run_listener(listener: UnixListener, state: Arc<RpcState>, path: PathBuf) {
    for stream in listener.incoming() {
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
    let command = request.command;
    let args = request.args;

    match command.as_str() {
        "version" => json!({ "version": VERSION }),
        "status" => {
            let status = state.status_reporter.as_ref().map(StatusReporter::report);
            json!({ "status": status })
        }
        "queues" => {
            let queue_snapshots = queue_snapshots(state);
            json!({ "queues": queue_snapshots })
        }
        "debug_bgworker" => debug_bgworker(state),
        "debug_headers" => debug_headers(state, args),
        other => json!({
            "error": format!("unknown command: {other}"),
        }),
    }
}

fn debug_bgworker(state: &RpcState) -> Value {
    let Some(sender) = state.bgworker_sender.as_ref() else {
        return json!({ "error": "bgworker debug not available" });
    };

    let (tx, rx) = mpsc::channel::<BgWorkerDebugInfo>();
    if let Err(e) = sender.send(BgWorkerRequest::Debug { responder: tx }) {
        return json!({
            "error": format!("failed to send bgworker debug request: {e}"),
        });
    }

    match rx.recv_timeout(Duration::from_secs(1)) {
        Ok(info) => match serde_json::to_value(info) {
            Ok(value) => json!({ "bgworker": value }),
            Err(e) => json!({
                "error": format!("failed to serialize bgworker debug info: {e}"),
            }),
        },
        Err(mpsc::RecvTimeoutError::Timeout) => {
            json!({ "error": "timed out waiting for bgworker debug response" })
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            json!({ "error": "bgworker debug response channel disconnected" })
        }
    }
}

fn debug_headers(state: &RpcState, args: Value) -> Value {
    let Some(metadata) = state.shared_metadata_state.as_ref() else {
        return json!({ "error": "metadata state not available" });
    };

    let parsed = match serde_json::from_value::<DebugHeadersArgs>(args) {
        Ok(args) => args,
        Err(e) => {
            return json!({
                "error": format!("invalid arguments for debug_headers: {e}"),
            });
        }
    };

    match metadata.stripe_headers_range(parsed.start, parsed.end) {
        Some(headers) => json!({
            "start": parsed.start,
            "end": parsed.end,
            "headers": headers,
        }),
        None => {
            let max_index = metadata.stripe_count().saturating_sub(1);
            json!({
                "error": format!(
                    "stripe range {}-{} out of bounds (valid stripes 0-{})",
                    parsed.start, parsed.end, max_index
                ),
            })
        }
    }
}

fn send_response(stream: &mut UnixStream, response: &Value) -> io::Result<()> {
    let mut payload = serde_json::to_vec(response).map_err(io::Error::other)?;
    payload.push(b'\n');
    stream.write_all(&payload)?;
    stream.flush()
}
