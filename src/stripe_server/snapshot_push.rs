//! The push half of snapshot serving.
//!
//! A fork opens a second session and sends `SUBSCRIBE_SNAPSHOT_CMD`. That
//! session stops being request/response and becomes a one-way stream of stripes
//! the prod side is about to overwrite: prod hands over the pre-write content
//! before the write is allowed through. Cold stripes the fork has not been
//! pushed are still pulled with `READ_STRIPE_CMD` on its other session, so an
//! idle fork cannot stall prod writes and a busy fork does not wait for prod to
//! overwrite something before it can read it.

use std::{
    os::fd::{AsRawFd, RawFd},
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
};

use log::{info, warn};

use crate::{
    block_device::{DestinationId, SnapshotDestination},
    Result,
};

use super::{DynStream, WireCompression, PUSH_STRIPE_FRAME, SNAPSHOT_END_FRAME};

/// Server side: a fork that subscribed, seen as a snapshot destination.
pub struct RemoteDestination {
    id: DestinationId,
    stream: DynStream,
    /// A second handle on the socket under `stream`, when there is one, so the
    /// fork can be found dead without writing to it.
    socket: Option<Box<dyn AsRawFd + Send>>,
    alive: Arc<AtomicBool>,
    compression: WireCompression,
}

impl RemoteDestination {
    pub fn new(id: DestinationId, stream: DynStream, compression: WireCompression) -> Self {
        Self {
            id,
            stream,
            socket: None,
            alive: Arc::new(AtomicBool::new(true)),
            compression,
        }
    }

    /// Check liveness against the socket itself, not only against failed
    /// pushes. Without this a fork is found dead only when a push to it fails,
    /// and a fork that dies while prod is not writing is never found at all:
    /// the kernel has given up on the connection, but nothing asks it.
    pub fn with_socket(mut self, socket: Box<dyn AsRawFd + Send>) -> Self {
        self.socket = Some(socket);
        self
    }

    /// Shared with whoever wants to hang up on this destination from another
    /// thread, e.g. when the snapshot ends.
    pub fn alive_flag(&self) -> Arc<AtomicBool> {
        self.alive.clone()
    }

    fn mark_dead(&mut self) {
        self.alive.store(false, Ordering::SeqCst);
    }

    /// Tell the fork the snapshot is over. Best effort: the fork may already be
    /// gone, which is not an error worth reporting.
    pub fn send_end(&mut self) {
        use std::io::Write;
        if self.stream.write_all(&[SNAPSHOT_END_FRAME]).is_err() || self.stream.flush().is_err() {
            info!(
                "Snapshot destination {} closed before the end frame",
                self.id
            );
        }
        self.mark_dead();
    }
}

impl SnapshotDestination for RemoteDestination {
    fn id(&self) -> DestinationId {
        self.id
    }

    fn offer(&mut self, stripe_id: usize, data: &[u8]) -> Result<()> {
        use std::io::Write;

        let payload = self.compression.compress(data).inspect_err(|_| {
            // Nothing else can send this stripe, so a destination that cannot
            // be encoded for is a destination that is over.
            self.mark_dead();
        })?;

        let result = (|| -> std::io::Result<()> {
            self.stream.write_all(&[PUSH_STRIPE_FRAME])?;
            self.stream.write_all(&(stripe_id as u64).to_le_bytes())?;
            self.stream
                .write_all(&(payload.len() as u64).to_le_bytes())?;
            self.stream.write_all(&payload)?;
            self.stream.flush()
        })();

        if let Err(source) = result {
            // A write error means the fork is gone or wedged. Prod writes are
            // waiting on this offer, so the destination dies rather than the
            // write retrying.
            warn!("Snapshot destination {} failed: {source}", self.id);
            self.mark_dead();
            return Err(crate::ubiblk_error!(IoError { source: source }));
        }

        Ok(())
    }

    fn is_alive(&self) -> bool {
        if !self.alive.load(Ordering::SeqCst) {
            return false;
        }
        if self
            .socket
            .as_ref()
            .is_some_and(|socket| peer_hung_up(socket.as_raw_fd()))
        {
            info!("Snapshot destination {} hung up", self.id);
            self.alive.store(false, Ordering::SeqCst);
            return false;
        }
        true
    }

    fn finish(&mut self) {
        self.send_end();
    }
}

/// Whether the peer on a socket has hung up, or the connection has failed.
///
/// The kernel knows as soon as a FIN, a reset or a keepalive timeout lands, but
/// only tells a process that asks. A push socket is only ever written to, so
/// nothing asks between pushes; this does, without reading or writing a byte.
fn peer_hung_up(fd: RawFd) -> bool {
    let mut poll_fd = libc::pollfd {
        fd,
        events: libc::POLLRDHUP,
        revents: 0,
    };
    // SAFETY: poll_fd is a valid pollfd that outlives the call, and 1 is the
    // number of entries it points at.
    let ready = unsafe { libc::poll(&mut poll_fd, 1, 0) };
    if ready <= 0 {
        // Nothing to report, or poll itself failed. Neither says the peer is
        // gone; a push that fails will still catch it.
        return false;
    }
    poll_fd.revents & (libc::POLLERR | libc::POLLHUP | libc::POLLRDHUP) != 0
}

/// What a subscribed fork reads off its push session.
#[derive(Debug, PartialEq, Eq)]
pub enum PushedFrame {
    /// Pre-write content of a stripe as of the snapshot.
    Stripe { stripe_id: u64, data: Vec<u8> },
    /// The snapshot ended: prod released it, or the last destination went away.
    End,
}

/// Client side: the fork's end of a push session.
pub struct SnapshotSubscriber {
    stream: DynStream,
    generation: u64,
    compression: WireCompression,
}

impl SnapshotSubscriber {
    /// Send the subscribe command and read the acknowledgement. The caller
    /// supplies a stream that has already been connected (and PSK-wrapped, if
    /// the deployment uses one), exactly like the pull client.
    pub fn subscribe(stream: DynStream, compression: WireCompression) -> Result<Self> {
        Self::subscribe_inner(stream, compression)
    }

    fn subscribe_inner(mut stream: DynStream, wanted: WireCompression) -> Result<Self> {
        use std::io::{Read, Write};

        stream.write_all(&[super::SUBSCRIBE_SNAPSHOT_CMD])?;
        stream.flush()?;

        let mut status = [0u8; 1];
        stream.read_exact(&mut status)?;
        if status[0] != super::STATUS_OK {
            return Err(crate::ubiblk_error!(IoError {
                source: std::io::Error::other(format!(
                    "snapshot subscribe rejected with status {}",
                    status[0]
                )),
            }));
        }

        let mut generation_bytes = [0u8; 8];
        stream.read_exact(&mut generation_bytes)?;
        let generation = u64::from_le_bytes(generation_bytes);

        // Prod encodes the pushes; this fork decodes them. Same negotiation as
        // the pull session, since the same two sides have to agree.
        let mut server_mask = [0u8; 1];
        stream.read_exact(&mut server_mask)?;
        let compression = wanted.best_of(server_mask[0]);
        stream.write_all(&[compression.code()])?;
        stream.flush()?;

        Ok(Self {
            stream,
            generation,
            compression,
        })
    }

    /// The snapshot generation this subscription is attached to. A fork that
    /// reconnects onto a different generation is looking at a different
    /// snapshot and has to start over.
    pub fn generation(&self) -> u64 {
        self.generation
    }

    /// Block until the next frame arrives. Returns `None` when the peer closes
    /// the connection.
    pub fn next_frame(&mut self) -> Result<Option<PushedFrame>> {
        use std::io::{ErrorKind, Read};

        let mut frame = [0u8; 1];
        match self.stream.read_exact(&mut frame) {
            Ok(()) => {}
            Err(e) if e.kind() == ErrorKind::UnexpectedEof => return Ok(None),
            Err(source) => return Err(crate::ubiblk_error!(IoError { source: source })),
        }

        match frame[0] {
            PUSH_STRIPE_FRAME => {
                let mut stripe_id_bytes = [0u8; 8];
                self.stream.read_exact(&mut stripe_id_bytes)?;
                let mut len_bytes = [0u8; 8];
                self.stream.read_exact(&mut len_bytes)?;

                let len = u64::from_le_bytes(len_bytes) as usize;
                let mut payload = vec![0u8; len];
                self.stream.read_exact(&mut payload)?;

                Ok(Some(PushedFrame::Stripe {
                    stripe_id: u64::from_le_bytes(stripe_id_bytes),
                    data: self.compression.decompress(payload)?,
                }))
            }
            SNAPSHOT_END_FRAME => Ok(Some(PushedFrame::End)),
            other => Err(crate::ubiblk_error!(IoError {
                source: std::io::Error::other(format!("unexpected snapshot frame {other}")),
            })),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::net::UnixStream;

    fn pair() -> (DynStream, DynStream) {
        let (a, b) = UnixStream::pair().unwrap();
        (Box::new(a), Box::new(b))
    }

    #[test]
    fn pushed_stripes_arrive_in_order() {
        for compression in [WireCompression::None, WireCompression::Zstd] {
            pushed_stripes_arrive_in_order_with(compression);
        }
    }

    fn pushed_stripes_arrive_in_order_with(compression: WireCompression) {
        let (server, client) = pair();
        let mut destination = RemoteDestination::new(1, server, compression);

        destination.offer(7, &[0xAA; 16]).unwrap();
        destination.offer(9, &[0xBB; 16]).unwrap();
        destination.send_end();

        let mut subscriber = SnapshotSubscriber {
            stream: client,
            generation: 1,
            compression,
        };

        assert_eq!(
            subscriber.next_frame().unwrap(),
            Some(PushedFrame::Stripe {
                stripe_id: 7,
                data: vec![0xAA; 16]
            })
        );
        assert_eq!(
            subscriber.next_frame().unwrap(),
            Some(PushedFrame::Stripe {
                stripe_id: 9,
                data: vec![0xBB; 16]
            })
        );
        assert_eq!(subscriber.next_frame().unwrap(), Some(PushedFrame::End));
    }

    #[test]
    fn a_hung_up_fork_kills_the_destination_instead_of_blocking() {
        let (server, client) = pair();
        let mut destination = RemoteDestination::new(2, server, WireCompression::None);
        drop(client);

        // The first offer may or may not fail depending on socket buffering,
        // but the destination must end up dead rather than looping.
        let mut died = false;
        for stripe_id in 0..64 {
            if destination.offer(stripe_id, &[0xCC; 4096]).is_err() {
                died = true;
                break;
            }
        }

        assert!(died, "writing to a closed peer must fail");
        assert!(!destination.is_alive());
    }

    /// The case a failed push cannot cover: the fork is gone, and prod has no
    /// write that would make the worker push anything to find that out.
    #[test]
    fn a_fork_that_hangs_up_is_found_dead_without_a_push() {
        let (server, client) = UnixStream::pair().unwrap();
        let socket = server.try_clone().unwrap();
        let destination = RemoteDestination::new(4, Box::new(server), WireCompression::None)
            .with_socket(Box::new(socket));

        assert!(destination.is_alive(), "a quiet fork is not a dead one");

        drop(client);
        assert!(
            !destination.is_alive(),
            "the hang-up is seen without anything being written"
        );
        assert!(!destination.is_alive(), "and it stays dead");
    }

    #[test]
    fn the_end_of_the_stream_reads_as_no_frame() {
        let (server, client) = pair();
        drop(server);

        let mut subscriber = SnapshotSubscriber {
            stream: client,
            generation: 3,
            compression: WireCompression::None,
        };
        assert_eq!(subscriber.next_frame().unwrap(), None);
    }

    #[test]
    fn an_unknown_frame_is_an_error_not_a_silent_skip() {
        let (mut server, client) = pair();
        {
            use std::io::Write;
            server.write_all(&[0x7F]).unwrap();
            server.flush().unwrap();
        }

        let mut subscriber = SnapshotSubscriber {
            stream: client,
            generation: 1,
            compression: WireCompression::None,
        };
        assert!(subscriber.next_frame().is_err());
    }
}
