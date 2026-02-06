use log::warn;

/// Disable core dumps to prevent key material from being written to disk.
///
/// Calls `prctl(PR_SET_DUMPABLE, 0)` and sets `RLIMIT_CORE` to zero.
/// Logs a warning if either call fails but does not abort (defense in depth).
#[cfg(target_os = "linux")]
pub fn disable_core_dumps() {
    // Mark the process as non-dumpable. This prevents core dumps and also
    // restricts /proc/self/mem access from other processes.

    log::debug!("Disabling core dumps with prctl(PR_SET_DUMPABLE=0) and RLIMIT_CORE=0");

    let ret = unsafe { libc::prctl(libc::PR_SET_DUMPABLE, 0, 0, 0, 0) };
    if ret != 0 {
        warn!(
            "failed to set PR_SET_DUMPABLE=0: {}",
            std::io::Error::last_os_error()
        );
    }

    // Set RLIMIT_CORE to zero to prevent core dumps even if dumpable gets
    // re-enabled (e.g. by setuid or ptrace).
    let rlim = libc::rlimit {
        rlim_cur: 0,
        rlim_max: 0,
    };
    let ret = unsafe { libc::setrlimit(libc::RLIMIT_CORE, &rlim) };
    if ret != 0 {
        warn!(
            "failed to set RLIMIT_CORE=0: {}",
            std::io::Error::last_os_error()
        );
    }
}

#[cfg(not(target_os = "linux"))]
pub fn disable_core_dumps() {
    // No-op on non-Linux platforms.
    warn!("Not disabling core dumps: only supported on Linux");
}

#[cfg(all(test, target_os = "linux"))]
mod tests {
    use super::*;

    #[test]
    fn test_disable_core_dumps() {
        disable_core_dumps();

        // Verify PR_SET_DUMPABLE is 0
        let dumpable = unsafe { libc::prctl(libc::PR_GET_DUMPABLE, 0, 0, 0, 0) };
        assert_ne!(dumpable, -1, "PR_GET_DUMPABLE should succeed");
        assert!(
            dumpable <= 0,
            "process should be non-dumpable after disable_core_dumps()"
        );

        // Verify RLIMIT_CORE is 0
        let mut rlim = libc::rlimit {
            rlim_cur: libc::RLIM_INFINITY,
            rlim_max: libc::RLIM_INFINITY,
        };
        let ret = unsafe { libc::getrlimit(libc::RLIMIT_CORE, &mut rlim) };
        assert_eq!(ret, 0, "getrlimit should succeed");
        assert_eq!(rlim.rlim_cur, 0, "RLIMIT_CORE soft limit should be 0");
        assert_eq!(rlim.rlim_max, 0, "RLIMIT_CORE hard limit should be 0");
    }
}
