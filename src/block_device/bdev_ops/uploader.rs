use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::thread::{self, JoinHandle};
use std::time::Duration;

/// Snapshot archive destination.
#[derive(Clone, Debug)]
pub enum ArchiveDestination {
    /// Write directly to a local/mounted filesystem path.
    /// No separate upload phase — the staging file IS the final artifact.
    LocalFs { path: PathBuf },
}

/// Status of a snapshot operation (for RPC reporting).
#[derive(Clone, Debug)]
pub struct SnapshotStatus {
    pub id: u64,
    pub state: SnapshotState,
    pub stripes_copied: usize,
    pub stripes_uploaded: usize,
    pub stripe_count: usize,
    pub error: Option<String>,
}

/// Possible states of a snapshot as seen by the RPC interface.
#[derive(Clone, Debug, PartialEq)]
pub enum SnapshotState {
    /// Draining in-flight IO from all channels + bgworker.
    Stalling,
    /// Bgworker copying stripes to staging, per-stripe write gating.
    Copying,
    /// Uploader archiving staged data (not applicable for LocalFs).
    Uploading,
    /// Snapshot fully archived.
    Complete,
    /// Snapshot failed.
    Failed,
}

/// Coordinator for a snapshot lifecycle, including the uploader thread.
///
/// This is held by the RPC/coordinator layer and provides status reporting.
/// The `SnapshotOperation` handles the copy phase; this manages the upload phase.
pub struct SnapshotCoordinator {
    pub id: u64,
    pub destination: ArchiveDestination,
    pub stripe_count: usize,
    pub stripe_size: u64,

    /// Stripes locally copied (shared with SnapshotOperation via bgworker).
    pub stripes_copied: Arc<AtomicUsize>,

    /// Stripes uploaded to destination. For LocalFs: mirrors stripes_copied.
    pub stripes_uploaded: Arc<AtomicUsize>,

    /// Upload error. Set by uploader thread, read by RPC status.
    pub upload_error: Arc<Mutex<Option<String>>>,

    /// Handle to the uploader thread. None for LocalFs.
    pub upload_handle: Option<JoinHandle<()>>,

    /// The OpsSharedState phase reference (for deriving Stalling/Copying).
    pub phase_fn: Box<dyn Fn() -> u8 + Send + Sync>,
}

impl SnapshotCoordinator {
    /// Derive the current snapshot state for RPC reporting.
    pub fn derive_state(&self) -> SnapshotState {
        let phase = (self.phase_fn)();
        if phase == super::shared_state::STALLING {
            return SnapshotState::Stalling;
        }
        if phase == super::shared_state::OPERATING {
            return SnapshotState::Copying;
        }
        // phase == NORMAL: check upload status
        if let Ok(guard) = self.upload_error.lock() {
            if guard.is_some() {
                return SnapshotState::Failed;
            }
        }
        if self.stripes_uploaded.load(Ordering::Acquire) < self.stripe_count {
            return SnapshotState::Uploading;
        }
        SnapshotState::Complete
    }

    /// Get full status for RPC.
    pub fn status(&self) -> SnapshotStatus {
        SnapshotStatus {
            id: self.id,
            state: self.derive_state(),
            stripes_copied: self.stripes_copied.load(Ordering::Acquire),
            stripes_uploaded: self.stripes_uploaded.load(Ordering::Acquire),
            stripe_count: self.stripe_count,
            error: self.upload_error.lock().ok().and_then(|g| g.clone()),
        }
    }
}

/// For LocalFs destinations, stripes_uploaded tracks stripes_copied since the
/// staging file IS the final artifact. This function spawns a lightweight
/// polling thread that mirrors the counter.
pub fn spawn_local_fs_mirror(
    stripes_copied: Arc<AtomicUsize>,
    stripes_uploaded: Arc<AtomicUsize>,
    stripe_count: usize,
) -> JoinHandle<()> {
    thread::Builder::new()
        .name("snapshot-localfs-mirror".to_string())
        .spawn(move || loop {
            let copied = stripes_copied.load(Ordering::Acquire);
            stripes_uploaded.store(copied, Ordering::Release);
            if copied >= stripe_count {
                break;
            }
            thread::sleep(Duration::from_millis(10));
        })
        .expect("failed to spawn LocalFs mirror thread")
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::AtomicUsize;

    #[test]
    fn local_fs_mirror_tracks_progress() {
        let stripes_copied = Arc::new(AtomicUsize::new(0));
        let stripes_uploaded = Arc::new(AtomicUsize::new(0));
        let stripe_count = 4;

        let copied = stripes_copied.clone();
        let handle = spawn_local_fs_mirror(
            stripes_copied.clone(),
            stripes_uploaded.clone(),
            stripe_count,
        );

        // Simulate copy progress
        for i in 1..=stripe_count {
            copied.store(i, Ordering::Release);
            thread::sleep(Duration::from_millis(20));
        }

        handle.join().unwrap();
        assert_eq!(stripes_uploaded.load(Ordering::Acquire), stripe_count);
    }

    #[test]
    fn snapshot_state_derivation() {
        use std::sync::atomic::AtomicU8;

        let phase = Arc::new(AtomicU8::new(super::super::shared_state::NORMAL));
        let phase_clone = phase.clone();
        let stripes_copied = Arc::new(AtomicUsize::new(0));
        let stripes_uploaded = Arc::new(AtomicUsize::new(0));
        let upload_error = Arc::new(Mutex::new(None));

        let coord = SnapshotCoordinator {
            id: 1,
            destination: ArchiveDestination::LocalFs {
                path: PathBuf::from("/tmp/test"),
            },
            stripe_count: 4,
            stripe_size: 4096,
            stripes_copied: stripes_copied.clone(),
            stripes_uploaded: stripes_uploaded.clone(),
            upload_error: upload_error.clone(),
            upload_handle: None,
            phase_fn: Box::new(move || phase_clone.load(Ordering::Acquire)),
        };

        // Test Stalling
        phase.store(super::super::shared_state::STALLING, Ordering::Release);
        assert_eq!(coord.derive_state(), SnapshotState::Stalling);

        // Test Copying (Operating)
        phase.store(super::super::shared_state::OPERATING, Ordering::Release);
        assert_eq!(coord.derive_state(), SnapshotState::Copying);

        // Test Uploading (Normal, not all uploaded)
        phase.store(super::super::shared_state::NORMAL, Ordering::Release);
        stripes_uploaded.store(2, Ordering::Release);
        assert_eq!(coord.derive_state(), SnapshotState::Uploading);

        // Test Complete
        stripes_uploaded.store(4, Ordering::Release);
        assert_eq!(coord.derive_state(), SnapshotState::Complete);

        // Test Failed
        *upload_error.lock().unwrap() = Some("disk full".to_string());
        assert_eq!(coord.derive_state(), SnapshotState::Failed);
    }
}
