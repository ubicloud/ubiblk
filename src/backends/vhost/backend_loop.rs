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

    #[test]
    fn serve_vhost_requires_socket() {
        let disk_file = tempfile::NamedTempFile::new().unwrap();
        disk_file.as_file().set_len(10 * 1024 * 1024).unwrap();

        let danger_zone = v2::DangerZone {
            enabled: true,
            allow_unencrypted_disk: true,
            allow_inline_plaintext_secrets: true,
            allow_secret_over_regular_file: true,
            allow_unencrypted_connection: true,
            allow_env_secrets: false,
        };

        let config = v2::Config {
            device: v2::DeviceSection {
                data_path: disk_file.path().to_path_buf(),
                vhost_socket: None,
                metadata_path: None,
                rpc_socket: None,
                device_id: "test-device".to_string(),
                track_written: false,
            },
            tuning: v2::tuning::TuningSection::default(),
            encryption: None,
            danger_zone,
            stripe_source: None,
            secrets: std::collections::HashMap::new(),
        };

        let err = block_backend_loop(&config).unwrap_err();

        assert!(matches!(err,
            crate::UbiblkError::InvalidParameter { description, .. }
            if description == "socket must be specified for the vhost backend"
        ));
    }
}
