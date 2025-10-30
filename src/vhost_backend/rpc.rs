use std::{
    fs,
    io::{self, BufRead, BufReader, Write},
    os::unix::net::{UnixListener, UnixStream},
    path::{Path, PathBuf},
    sync::Arc,
    thread::JoinHandle,
};

use crate::{Result, VhostUserBlockError};
use log::{error, info, warn};
use serde::Deserialize;
use serde_json::{json, Value};

use crate::block_device::StatusReporter;

const VERSION: &str = env!("CARGO_PKG_VERSION");

#[derive(Clone)]
struct RpcState {
    status_reporter: Option<StatusReporter>,
}

#[derive(Deserialize)]
struct RpcRequest {
    command: String,
}

pub fn start_rpc_server<P: AsRef<Path>>(
    path: P,
    status_reporter: Option<StatusReporter>,
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
    let state = Arc::new(RpcState { status_reporter });

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

fn process_request(request: RpcRequest, state: &RpcState) -> Value {
    match request.command.as_str() {
        "version" => json!({ "version": VERSION }),
        "status" => {
            let status = state.status_reporter.as_ref().map(StatusReporter::report);
            json!({ "status": status })
        }
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
