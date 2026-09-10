use nix::sys::stat::{umask, Mode};

/// RAII guard that temporarily sets the process umask.
///
/// Restores the previous umask when dropped.
/// **Note:** `umask` is process-global; avoid using in concurrent threads.
pub struct UmaskGuard {
    previous: Mode,
}

impl UmaskGuard {
    /// Set the process umask to `mask` and restore it on drop.
    pub fn set(mask: libc::mode_t) -> Self {
        // Tests run beside unrelated filesystem operations that cannot all
        // participate in a lock. Keep the real umask syscall, but detach this
        // thread's filesystem context before changing it.
        #[cfg(test)]
        isolate_test_umask();

        let previous = umask(Mode::from_bits_retain(mask));
        Self { previous }
    }
}

impl Drop for UmaskGuard {
    fn drop(&mut self) {
        umask(self.previous);
    }
}

#[cfg(test)]
fn isolate_test_umask() {
    nix::sched::unshare(nix::sched::CloneFlags::CLONE_FS).expect("isolate the test thread's umask");
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt};

    fn get_umask() -> libc::mode_t {
        isolate_test_umask();
        let cur = umask(Mode::from_bits_retain(0));
        umask(cur);
        cur.bits()
    }

    #[test]
    fn restores_on_drop() {
        let orig = get_umask();

        {
            let _g = UmaskGuard::set(0o006);
            assert_eq!(get_umask(), 0o006);
        }
        assert_eq!(get_umask(), orig);
    }

    #[test]
    fn masks_file_creation() {
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("f");

        {
            let _g = UmaskGuard::set(0o006);
            fs::OpenOptions::new()
                .create(true)
                .truncate(true)
                .write(true)
                .mode(0o666)
                .open(&file)
                .unwrap();
        }

        let mode = fs::metadata(&file).unwrap().mode() & 0o777;
        assert_eq!(mode, 0o666 & !0o006);
    }

    #[test]
    fn restrictive_umask_does_not_affect_other_test_threads() {
        let dir = tempfile::tempdir().unwrap();
        let child = dir.path().join("child");
        let (ready_tx, ready_rx) = std::sync::mpsc::channel();
        let (release_tx, release_rx) = std::sync::mpsc::channel();
        let worker = std::thread::spawn(move || {
            let _guard = UmaskGuard::set(0o777);
            ready_tx.send(()).unwrap();
            release_rx.recv().unwrap();
        });
        ready_rx.recv().unwrap();

        // Hold the restrictive mask until both operations finish. A mutex
        // around UmaskGuard alone cannot protect these unrelated operations.
        let result = fs::DirBuilder::new()
            .mode(0o700)
            .create(&child)
            .and_then(|()| fs::write(child.join("file"), b"parallel test"));
        release_tx.send(()).unwrap();
        worker.join().unwrap();

        // Also allow cleanup when running this regression against the old code.
        let mode = fs::metadata(&child).unwrap().mode() & 0o777;
        fs::set_permissions(&child, fs::Permissions::from_mode(0o700)).unwrap();
        // Check the mode as well, so this catches the regression even as root.
        assert_eq!(mode, 0o700);
        result.expect("another test thread's umask must not prevent file creation");
    }
}
