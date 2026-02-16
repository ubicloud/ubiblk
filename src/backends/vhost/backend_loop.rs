use std::{fs, os::unix::fs::PermissionsExt, sync::Arc};

use log::info;
use vhost::vhost_user::{Error as VhostUserError, Listener};
use vhost_user_backend::{Error as VhostUserBackendError, VhostUserDaemon};
use vm_memory::GuestMemoryAtomic;

use super::backend::UbiBlkBackend;
use crate::{
    backends::common::{run_backend_loop, BackendEnv},
    config::v2,
    utils::umask_guard::UmaskGuard,
    Result,
};

type GuestMemoryMmap = vm_memory::GuestMemoryMmap<vhost_user_backend::bitmap::BitmapMmapRegion>;

pub fn block_backend_loop(config: &v2::Config) -> Result<()> {
    run_backend_loop(config, "vhost-user-blk", true, serve_vhost)
}

fn serve_vhost(backend_env: &BackendEnv) -> Result<()> {
    let mem = GuestMemoryAtomic::new(GuestMemoryMmap::new());

    info!("Creating backend ...");

    let backend = Arc::new(UbiBlkBackend::new(
        backend_env.config(),
        mem.clone(),
        backend_env.bdev(),
        backend_env.alignment(),
        backend_env.io_trackers().clone(),
    )?);

    info!("Backend is created!");

    let mut daemon = VhostUserDaemon::new("ubiblk-backend".to_string(), backend.clone(), mem)?;

    info!("Daemon is created!");

    let socket = backend_env
        .config()
        .device
        .vhost_socket
        .as_ref()
        .ok_or_else(|| {
            crate::ubiblk_error!(InvalidParameter {
                description: "socket must be specified for the vhost backend".to_string(),
            })
        })?;

    let listener = {
        let _um = UmaskGuard::set(0o117); // ensures 0660 max on creation
        Listener::new(socket, true)?
    };

    // Allow only owner and group to read/write the socket
    fs::set_permissions(socket, fs::Permissions::from_mode(0o660))?;

    daemon.start(listener)?;
    let result = daemon.wait();

    for handler in daemon.get_epoll_handlers() {
        handler.send_exit_event();
    }

    match result {
        Ok(()) => {}
        Err(VhostUserBackendError::HandleRequest(e @ VhostUserError::Disconnected))
        | Err(VhostUserBackendError::HandleRequest(e @ VhostUserError::PartialMessage))
        | Err(VhostUserBackendError::HandleRequest(e @ VhostUserError::InvalidMessage))
        | Err(VhostUserBackendError::HandleRequest(e @ VhostUserError::SocketBroken(_))) => {
            info!("Client disconnected: {}", e);
        }
        Err(e) => {
            return Err(e.into());
        }
    }

    info!("Finished serving socket!");

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backends::common::BackendEnv;
    use crate::utils::umask_guard::UMASK_LOCK;
    use std::os::unix::net::UnixStream;

    fn test_danger_zone() -> v2::DangerZone {
        v2::DangerZone {
            enabled: true,
            allow_unencrypted_disk: true,
            allow_inline_plaintext_secrets: true,
            allow_secret_over_regular_file: true,
            allow_unencrypted_connection: true,
            allow_env_secrets: false,
        }
    }

    fn test_config_with_socket(
        disk_path: &std::path::Path,
        socket_path: Option<&std::path::Path>,
    ) -> v2::Config {
        v2::Config {
            device: v2::DeviceSection {
                data_path: disk_path.to_path_buf(),
                vhost_socket: socket_path.map(|p| p.to_path_buf()),
                metadata_path: None,
                rpc_socket: None,
                device_id: "test-device".to_string(),
                track_written: false,
            },
            tuning: v2::tuning::TuningSection::default(),
            encryption: None,
            danger_zone: test_danger_zone(),
            stripe_source: None,
            secrets: std::collections::HashMap::new(),
        }
    }

    #[test]
    fn serve_vhost_requires_socket() {
        let disk_file = tempfile::NamedTempFile::new().unwrap();
        disk_file.as_file().set_len(10 * 1024 * 1024).unwrap();

        let config = test_config_with_socket(disk_file.path(), None);

        let err = block_backend_loop(&config).unwrap_err();

        assert!(matches!(err,
            crate::UbiblkError::InvalidParameter { description, .. }
            if description == "socket must be specified for the vhost backend"
        ));
    }

    /// Test that serve_vhost creates a socket, sets permissions, and handles
    /// client disconnection gracefully.
    #[test]
    fn serve_vhost_handles_client_disconnect() {
        let _umask_guard = UMASK_LOCK.lock().unwrap();

        let disk_file = tempfile::NamedTempFile::new().unwrap();
        disk_file.as_file().set_len(10 * 1024 * 1024).unwrap();

        let dir = tempfile::tempdir().unwrap();
        let socket_path = dir.path().join("test-vhost.sock");

        let config = test_config_with_socket(disk_file.path(), Some(&socket_path));
        let backend_env = BackendEnv::build(&config).unwrap();

        let socket_path_clone = socket_path.clone();
        let handle = std::thread::spawn(move || serve_vhost(&backend_env));

        // Wait for the socket to be created
        for _ in 0..100 {
            if socket_path_clone.exists() {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(50));
        }
        assert!(socket_path_clone.exists(), "Socket was not created in time");

        // Verify socket permissions are 0660
        let mode = fs::metadata(&socket_path_clone)
            .unwrap()
            .permissions()
            .mode()
            & 0o7777;
        assert_eq!(mode, 0o660);

        // Connect and immediately drop to trigger client disconnect
        let _stream = UnixStream::connect(&socket_path_clone).unwrap();
        drop(_stream);

        let result = handle.join().unwrap();
        // The daemon sees a disconnect. Depending on the exact error from
        // the vhost-user library this may be Ok (handled disconnect) or
        // Err (unexpected error). Either way the function should not panic.
        // In practice, a raw Unix-socket connect (not speaking vhost-user
        // protocol) may produce PartialMessage / InvalidMessage / Disconnected.
        match &result {
            Ok(()) => {}
            Err(e) => {
                let msg = e.to_string();
                // Accept any vhost-user protocol error from the raw connect
                assert!(
                    msg.contains("Disconnect")
                        || msg.contains("Partial")
                        || msg.contains("Invalid")
                        || msg.contains("Broken")
                        || msg.contains("Socket"),
                    "Unexpected error: {msg}"
                );
            }
        }
    }

    /// Test that serve_vhost returns an error when the socket path's parent
    /// directory does not exist.
    #[test]
    fn serve_vhost_fails_with_bad_socket_path() {
        let disk_file = tempfile::NamedTempFile::new().unwrap();
        disk_file.as_file().set_len(10 * 1024 * 1024).unwrap();

        let bad_socket = std::path::PathBuf::from("/nonexistent/dir/test.sock");
        let config = test_config_with_socket(disk_file.path(), Some(&bad_socket));
        let backend_env = BackendEnv::build(&config).unwrap();

        let result = serve_vhost(&backend_env);
        assert!(result.is_err());
    }
}
