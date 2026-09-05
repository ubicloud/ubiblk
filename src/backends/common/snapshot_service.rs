//! The two threads that make forking work in a real deployment.
//!
//! On the prod side, `spawn_snapshot_server` listens for forks: a fork
//! subscribes to the current snapshot on one session and pulls cold stripes on
//! another. On the fork side, `spawn_snapshot_subscriber` keeps a subscription
//! open and hands every pushed stripe to the bgworker, which writes it to the
//! fork's disk the same way a fetched stripe is written.

use std::{
    net::{TcpListener, TcpStream},
    sync::{mpsc::Sender, Arc},
    thread,
    time::Duration,
};

use log::{error, info, warn};

use crate::{
    block_device::BlockDevice,
    block_device::{
        BgWorkerRequest, PushGate, SharedMetadataState, SharedSnapshotState, SnapshotRequest,
        UbiMetadata, MAX_QUEUED_PUSHES,
    },
    stripe_server::{PushedFrame, SnapshotSubscriber, StripeServer, WireCompression},
    Result,
};

/// How long to wait before reconnecting a dropped subscription.
const RECONNECT_DELAY: Duration = Duration::from_secs(1);

/// How long a push may take to reach a fork before that fork is considered gone.
///
/// Without this a fork whose VM disappears leaves a half-open socket: writes to
/// it block until TCP gives up, minutes later, and the snapshot worker is stuck
/// in that write. Everything else then waits on the worker — the copy-out never
/// finishes, so prod's write stays blocked, and a new fork's subscription is not
/// even processed. A fork must never be able to do that to prod.
/// Generous, because it is the wrong tool for spotting a fork that has gone
/// away: a fork that is merely busy must not be dropped, and a fork whose VM
/// was destroyed is caught by keepalive below instead.
const PUSH_WRITE_TIMEOUT: Duration = Duration::from_secs(30);

/// Keepalive settings for a push connection: a peer that stops answering is
/// noticed in about ten seconds, so prod stops pushing to a fork whose VM was
/// destroyed without having to guess from how long a write is taking.
const KEEPALIVE_IDLE_SECS: libc::c_int = 5;
const KEEPALIVE_INTERVAL_SECS: libc::c_int = 2;
const KEEPALIVE_PROBES: libc::c_int = 3;

fn set_keepalive(stream: &TcpStream) -> std::io::Result<()> {
    use std::os::fd::AsRawFd;

    let fd = stream.as_raw_fd();
    let options: [(libc::c_int, libc::c_int, libc::c_int); 4] = [
        (libc::SOL_SOCKET, libc::SO_KEEPALIVE, 1),
        (libc::IPPROTO_TCP, libc::TCP_KEEPIDLE, KEEPALIVE_IDLE_SECS),
        (
            libc::IPPROTO_TCP,
            libc::TCP_KEEPINTVL,
            KEEPALIVE_INTERVAL_SECS,
        ),
        (libc::IPPROTO_TCP, libc::TCP_KEEPCNT, KEEPALIVE_PROBES),
    ];

    for (level, name, value) in options {
        // SAFETY: fd is owned by `stream` and outlives this call, and value is a
        // c_int as every one of these options expects.
        let result = unsafe {
            libc::setsockopt(
                fd,
                level,
                name,
                &value as *const libc::c_int as *const libc::c_void,
                std::mem::size_of::<libc::c_int>() as libc::socklen_t,
            )
        };
        if result != 0 {
            return Err(std::io::Error::last_os_error());
        }
    }

    Ok(())
}

/// Serve snapshots of this device to forks.
pub fn spawn_snapshot_server(
    address: &str,
    stripe_device: Box<dyn BlockDevice>,
    metadata: Arc<UbiMetadata>,
    live_state: SharedMetadataState,
    snapshot_ch: Sender<SnapshotRequest>,
    snapshot_state: SharedSnapshotState,
) -> Result<()> {
    let listener = TcpListener::bind(address).map_err(|e| {
        crate::ubiblk_error!(InvalidParameter {
            description: format!("Failed to listen for snapshot clients on {address}: {e}"),
        })
    })?;

    info!("Serving snapshots on {address}");

    let server = Arc::new(
        StripeServer::new(Arc::from(stripe_device), metadata, None)
            .with_live_state(live_state)
            .with_snapshot(snapshot_ch, snapshot_state),
    );

    thread::Builder::new()
        .name("snapshot-server".to_string())
        .spawn(move || {
            for stream in listener.incoming() {
                let stream = match stream {
                    Ok(stream) => stream,
                    Err(e) => {
                        error!("Failed to accept a snapshot client: {e}");
                        continue;
                    }
                };

                if let Err(e) = stream.set_write_timeout(Some(PUSH_WRITE_TIMEOUT)) {
                    error!("Failed to set the push write timeout: {e}");
                    continue;
                }

                if let Err(e) = set_keepalive(&stream) {
                    error!("Failed to set keepalive on a snapshot connection: {e}");
                    continue;
                }

                // Keepalive only marks the socket dead; something has to look.
                // The worker looks at this handle, so a fork that dies while
                // prod is not writing is dropped rather than kept until a push
                // to it happens to fail.
                let socket = match stream.try_clone() {
                    Ok(socket) => socket,
                    Err(e) => {
                        error!("Failed to duplicate a snapshot connection: {e}");
                        continue;
                    }
                };

                let server = server.clone();
                // One thread per fork. A session that subscribes hands its
                // stream to the snapshot worker and this thread ends.
                let spawned = thread::Builder::new()
                    .name("snapshot-session".to_string())
                    .spawn(move || match server.start_session(Box::new(stream)) {
                        Ok(session) => session.with_socket(Box::new(socket)).handle_requests(),
                        Err(e) => error!("Failed to start a snapshot session: {e}"),
                    });

                if let Err(e) = spawned {
                    error!("Failed to spawn a snapshot session thread: {e}");
                }
            }
        })
        .map_err(|e| {
            crate::ubiblk_error!(InvalidParameter {
                description: format!("Failed to spawn the snapshot server thread: {e}"),
            })
        })?;

    Ok(())
}

/// Subscribe to the prod device's snapshot and feed what it pushes into the
/// bgworker.
pub fn spawn_snapshot_subscriber(
    address: &str,
    compression: WireCompression,
    bgworker_ch: Sender<BgWorkerRequest>,
) -> Result<()> {
    let address = address.to_string();
    let gate = PushGate::new(MAX_QUEUED_PUSHES);

    thread::Builder::new()
        .name("snapshot-subscriber".to_string())
        .spawn(move || loop {
            match subscribe_once(&address, compression, &gate, &bgworker_ch) {
                Ok(()) => info!("Snapshot ended; not resubscribing"),
                Err(e) => {
                    warn!("Snapshot subscription to {address} ended: {e}");
                    thread::sleep(RECONNECT_DELAY);
                    continue;
                }
            }
            return;
        })
        .map_err(|e| {
            crate::ubiblk_error!(InvalidParameter {
                description: format!("Failed to spawn the snapshot subscriber thread: {e}"),
            })
        })?;

    Ok(())
}

fn subscribe_once(
    address: &str,
    compression: WireCompression,
    gate: &Arc<PushGate>,
    bgworker_ch: &Sender<BgWorkerRequest>,
) -> Result<()> {
    let stream = TcpStream::connect(address).map_err(|e| {
        crate::ubiblk_error!(InvalidParameter {
            description: format!("Failed to connect to the snapshot server {address}: {e}"),
        })
    })?;

    let mut subscriber = SnapshotSubscriber::subscribe(Box::new(stream), compression)?;
    info!(
        "Subscribed to snapshot generation {} on {address}",
        subscriber.generation()
    );

    loop {
        match subscriber.next_frame()? {
            Some(PushedFrame::Stripe { stripe_id, data }) => {
                // Waits while the worker is behind, so a fork that cannot keep
                // up stops reading rather than holding prod's writes in memory.
                let permit = gate.acquire();
                if bgworker_ch
                    .send(BgWorkerRequest::PushedStripe {
                        stripe_id: stripe_id as usize,
                        data,
                        permit,
                    })
                    .is_err()
                {
                    // The bgworker is gone, so this device is shutting down.
                    return Ok(());
                }
            }
            // Prod released the snapshot. Anything not pushed by now is
            // still available to pull, so there is nothing to wait for.
            Some(PushedFrame::End) => return Ok(()),
            None => {
                return Err(crate::ubiblk_error!(InvalidParameter {
                    description: "snapshot server closed the connection".to_string(),
                }))
            }
        }
    }
}
