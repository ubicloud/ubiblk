#[cfg(test)]
use std::sync::Mutex;

/// RAII guard that temporarily sets the process umask.
///
/// Restores the previous umask when dropped.
/// **Note:** `umask` is process-global; avoid using in concurrent threads.
pub struct UmaskGuard {
    previous: libc::mode_t,
}

impl UmaskGuard {
    /// Set the process umask to `mask` and restore it on drop.
    pub fn set(mask: libc::mode_t) -> Self {
        let previous = unsafe { libc::umask(mask) };
        Self { previous }
    }
}

impl Drop for UmaskGuard {
    fn drop(&mut self) {
        unsafe {
            libc::umask(self.previous);
        }
    }
}

#[cfg(test)]
pub(crate) static UMASK_LOCK: Mutex<()> = Mutex::new(());

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::os::unix::fs::{MetadataExt, OpenOptionsExt};

    fn get_umask() -> libc::mode_t {
        unsafe {
            let cur = libc::umask(0);
            libc::umask(cur);
            cur
        }
    }

    #[test]
    fn restores_on_drop() {
        let _l = UMASK_LOCK.lock().unwrap();
        let orig = get_umask();

        {
            let _g = UmaskGuard::set(0o006);
            assert_eq!(get_umask(), 0o006);
        }
        assert_eq!(get_umask(), orig);
    }

    #[test]
    fn masks_file_creation() {
        let _l = UMASK_LOCK.lock().unwrap();

        let dir = std::env::temp_dir().join("umaskguard-test");
        let file = dir.join("f");
        fs::remove_file(&file).ok();
        fs::remove_dir(&dir).ok();
        fs::create_dir_all(&dir).unwrap();

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

        fs::remove_file(&file).ok();
        fs::remove_dir(&dir).ok();
    }
}
