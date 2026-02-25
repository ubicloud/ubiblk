use std::path::PathBuf;
use std::sync::atomic::{AtomicU8, Ordering};
use std::sync::{mpsc, Arc, Mutex};

use serde::Serialize;

/// Represents the snapshot FSM states.
/// Stored as AtomicU8 for lock-free reading from the RPC thread.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum SnapshotState {
    Idle = 0,
    Draining = 1,
    Snapshotting = 2,
    Resuming = 3,
}

impl SnapshotState {
    pub fn from_u8(v: u8) -> Self {
        match v {
            0 => Self::Idle,
            1 => Self::Draining,
            2 => Self::Snapshotting,
            3 => Self::Resuming,
            _ => Self::Idle,
        }
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Idle => "idle",
            Self::Draining => "draining",
            Self::Snapshotting => "snapshotting",
            Self::Resuming => "resuming",
        }
    }
}

/// Command sent from RPC thread to the snapshot layer via mpsc channel.
pub struct SnapshotCommand {
    /// Path for the new active data file.
    pub new_data_path: PathBuf,
    /// Path for the new metadata file.
    pub new_metadata_path: PathBuf,
    /// Channel to send back the result (snapshot_id on success, error string on failure).
    pub result_tx: mpsc::Sender<Result<String, String>>,
}

/// Information about the last completed snapshot, readable by RPC.
#[derive(Debug, Clone, Serialize)]
pub struct SnapshotInfo {
    pub snapshot_id: String,
    #[serde(flatten)]
    pub result: SnapshotResult,
    pub completed_at_unix: u64,
}

#[derive(Debug, Clone, Serialize)]
#[serde(tag = "result")]
pub enum SnapshotResult {
    #[serde(rename = "success")]
    Success {
        old_data_path: PathBuf,
        new_data_path: PathBuf,
        new_metadata_path: PathBuf,
    },
    #[serde(rename = "failed")]
    Failed { error: String },
}

/// Shared handle for reading/writing snapshot status.
/// Clone-friendly (all fields are Arc), matches the pattern of StatusReporter.
#[derive(Debug, Clone)]
pub struct SnapshotStatusHandle {
    state: Arc<AtomicU8>,
    last_snapshot: Arc<Mutex<Option<SnapshotInfo>>>,
}

impl SnapshotStatusHandle {
    /// Returns (writer, reader) pair — both are identical clones sharing the same Arc state.
    pub fn new() -> (Self, Self) {
        let state = Arc::new(AtomicU8::new(SnapshotState::Idle as u8));
        let last_snapshot = Arc::new(Mutex::new(None));
        let handle = SnapshotStatusHandle {
            state,
            last_snapshot,
        };
        (handle.clone(), handle)
    }

    pub fn current_state(&self) -> SnapshotState {
        SnapshotState::from_u8(self.state.load(Ordering::Acquire))
    }

    pub fn set_state(&self, state: SnapshotState) {
        self.state.store(state as u8, Ordering::Release);
    }

    pub fn last_snapshot(&self) -> Option<SnapshotInfo> {
        self.last_snapshot.lock().unwrap().clone()
    }

    pub fn set_last_snapshot(&self, info: SnapshotInfo) {
        *self.last_snapshot.lock().unwrap() = Some(info);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn snapshot_state_round_trip() {
        for v in 0..=3u8 {
            let state = SnapshotState::from_u8(v);
            assert_eq!(state as u8, v);
        }
        // Unknown values default to Idle
        assert_eq!(SnapshotState::from_u8(255), SnapshotState::Idle);
    }

    #[test]
    fn snapshot_state_as_str() {
        assert_eq!(SnapshotState::Idle.as_str(), "idle");
        assert_eq!(SnapshotState::Draining.as_str(), "draining");
        assert_eq!(SnapshotState::Snapshotting.as_str(), "snapshotting");
        assert_eq!(SnapshotState::Resuming.as_str(), "resuming");
    }

    #[test]
    fn snapshot_status_handle_is_clone_send_sync() {
        fn assert_clone_send_sync<T: Clone + Send + Sync>() {}
        assert_clone_send_sync::<SnapshotStatusHandle>();
    }

    #[test]
    fn snapshot_command_is_send() {
        fn assert_send<T: Send>() {}
        assert_send::<SnapshotCommand>();
    }

    #[test]
    fn snapshot_status_handle_state_transitions() {
        let (writer, reader) = SnapshotStatusHandle::new();
        assert_eq!(reader.current_state(), SnapshotState::Idle);

        writer.set_state(SnapshotState::Draining);
        assert_eq!(reader.current_state(), SnapshotState::Draining);

        writer.set_state(SnapshotState::Snapshotting);
        assert_eq!(reader.current_state(), SnapshotState::Snapshotting);

        writer.set_state(SnapshotState::Resuming);
        assert_eq!(reader.current_state(), SnapshotState::Resuming);

        writer.set_state(SnapshotState::Idle);
        assert_eq!(reader.current_state(), SnapshotState::Idle);
    }

    #[test]
    fn snapshot_status_handle_last_snapshot() {
        let (writer, reader) = SnapshotStatusHandle::new();
        assert!(reader.last_snapshot().is_none());

        let info = SnapshotInfo {
            snapshot_id: "snap-123".to_string(),
            result: SnapshotResult::Success {
                old_data_path: PathBuf::from("/old/data"),
                new_data_path: PathBuf::from("/new/data"),
                new_metadata_path: PathBuf::from("/new/meta"),
            },
            completed_at_unix: 1234567890,
        };
        writer.set_last_snapshot(info);

        let last = reader.last_snapshot().unwrap();
        assert_eq!(last.snapshot_id, "snap-123");
        assert_eq!(last.completed_at_unix, 1234567890);
    }

    #[test]
    fn snapshot_info_serializes_success() {
        let info = SnapshotInfo {
            snapshot_id: "snap-1".to_string(),
            result: SnapshotResult::Success {
                old_data_path: PathBuf::from("/old"),
                new_data_path: PathBuf::from("/new"),
                new_metadata_path: PathBuf::from("/meta"),
            },
            completed_at_unix: 100,
        };
        let json = serde_json::to_value(&info).unwrap();
        assert_eq!(json["result"], "success");
        assert_eq!(json["old_data_path"], "/old");
    }

    #[test]
    fn snapshot_info_serializes_failed() {
        let info = SnapshotInfo {
            snapshot_id: "snap-2".to_string(),
            result: SnapshotResult::Failed {
                error: "disk full".to_string(),
            },
            completed_at_unix: 200,
        };
        let json = serde_json::to_value(&info).unwrap();
        assert_eq!(json["result"], "failed");
        assert_eq!(json["error"], "disk full");
    }
}
