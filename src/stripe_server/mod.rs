use std::{
    io::{Read, Write},
    os::fd::AsRawFd,
    sync::{atomic::AtomicU64, mpsc::Sender, Arc},
};

use crate::{
    block_device::SharedBuffer,
    block_device::{
        BlockDevice, IoChannel, SharedMetadataState, SharedSnapshotState, SnapshotRequest,
        UbiMetadata,
    },
    stripe_source::{StripeSource, StripeSourceBuilder},
    Result,
};

pub trait ReadWrite: Read + Write {}
impl<T: Read + Write> ReadWrite for T {}

pub type DynStream = Box<dyn ReadWrite + Send>;

pub const METADATA_CMD: u8 = 0x00;
pub const READ_STRIPE_CMD: u8 = 0x01;
pub const HELLO_CMD: u8 = 0x02;
/// Turns this session into a one-way stream of snapshot pushes. Cold reads keep
/// using `READ_STRIPE_CMD` on another session.
pub const SUBSCRIBE_SNAPSHOT_CMD: u8 = 0x03;

/// Frames the server sends on a subscribed session.
pub const PUSH_STRIPE_FRAME: u8 = 0x10;
pub const SNAPSHOT_END_FRAME: u8 = 0x11;

/// Remote stripe protocol version, reported by the hello command so a client can
/// detect a server it is not compatible with. Bump on incompatible wire changes.
///
/// 2: hello and subscribe negotiate stripe compression, and stripe payloads on
/// the wire are whatever that negotiation chose.
pub const PROTOCOL_VERSION: u32 = 2;

pub const STATUS_OK: u8 = 0x00;
pub const STATUS_INVALID_STRIPE: u8 = 0x01;
pub const STATUS_NO_DATA: u8 = 0x02;
pub const STATUS_NOT_FETCHED: u8 = 0x03;
pub const STATUS_NO_SNAPSHOT: u8 = 0x04;
/// The snapshot's copy of this stripe was already pushed to the subscribers:
/// prod has moved on, so the local copy is the only correct one.
pub const STATUS_ALREADY_PUSHED: u8 = 0x05;
pub const STATUS_INVALID_COMMAND: u8 = 0xFE;
pub const STATUS_SERVER_ERROR: u8 = 0xFF;

pub struct StripeServer {
    metadata: Arc<UbiMetadata>,
    stripe_device: Arc<dyn BlockDevice>,
    /// Set when this server fronts a device that can snapshot itself. Sessions
    /// use it to hand their stream over as a snapshot destination.
    snapshot_ch: Option<Sender<SnapshotRequest>>,
    snapshot_state: Option<SharedSnapshotState>,
    /// The device's live written/fetched bits. The metadata this server was
    /// built with is a snapshot of the file at startup, so a device that is
    /// being written to needs this to answer "does this stripe hold data?".
    live_state: Option<SharedMetadataState>,
    /// Ids handed to destinations, so the worker can be told to drop one.
    next_destination_id: Arc<AtomicU64>,
    // A stripe source builder, so each session can build its own source (the
    // source is not Send, so it cannot be shared across connection threads).
    // Used to serve stripes that have a source but have not been fetched yet.
    source_builder: Option<StripeSourceBuilder>,
}

pub struct StripeServerSession {
    stream: Option<DynStream>,
    /// A second handle on the socket under `stream`, if the caller has one.
    /// Handed to the snapshot worker along with the stream when the session
    /// subscribes, so a fork that dies is noticed without a push to it.
    socket: Option<Box<dyn AsRawFd + Send>>,
    /// One buffer, reused for every stripe this session serves. Allocating a
    /// megabyte per request means faulting in and zeroing a megabyte per
    /// request, which the serving side pays on every stripe a fork pulls.
    stripe_buffer: Option<SharedBuffer>,
    /// How stripe payloads are encoded on this session, agreed at hello or
    /// subscribe time. Uncompressed until then.
    compression: WireCompression,
    metadata: Arc<UbiMetadata>,
    stripe_channel: Box<dyn IoChannel>,
    source: Option<Box<dyn StripeSource>>,
    snapshot_ch: Option<Sender<SnapshotRequest>>,
    snapshot_state: Option<SharedSnapshotState>,
    live_state: Option<SharedMetadataState>,
    next_destination_id: Arc<AtomicU64>,
}

pub struct StripeServerClient {
    stream: DynStream,
    pub metadata: Option<UbiMetadata>,
    /// What this client asks the server to encode stripes with, and what it
    /// decodes them as once the server has agreed.
    compression: WireCompression,
}

pub trait RemoteStripeProvider {
    fn fetch_stripe(&mut self, stripe_idx: u64) -> Result<Vec<u8>>;
    fn get_metadata(&self) -> Option<&UbiMetadata>;
}

impl StripeServer {
    pub fn new(
        stripe_device: Arc<dyn BlockDevice>,
        metadata: Arc<UbiMetadata>,
        source_builder: Option<StripeSourceBuilder>,
    ) -> Self {
        Self {
            stripe_device,
            metadata,
            source_builder,
            snapshot_ch: None,
            snapshot_state: None,
            live_state: None,
            next_destination_id: Arc::new(AtomicU64::new(1)),
        }
    }

    /// Let sessions subscribe to snapshots taken on the device this server
    /// serves.
    /// Serve what the device actually holds right now, rather than what its
    /// metadata said when this server started.
    pub fn with_live_state(mut self, live_state: SharedMetadataState) -> Self {
        self.live_state = Some(live_state);
        self
    }

    pub fn with_snapshot(
        mut self,
        snapshot_ch: Sender<SnapshotRequest>,
        snapshot_state: SharedSnapshotState,
    ) -> Self {
        self.snapshot_ch = Some(snapshot_ch);
        self.snapshot_state = Some(snapshot_state);
        self
    }

    pub fn start_session(&self, stream: DynStream) -> Result<StripeServerSession> {
        let stripe_channel = self.stripe_device.create_channel()?;
        let source = self
            .source_builder
            .as_ref()
            .map(StripeSourceBuilder::build)
            .transpose()?;
        Ok(StripeServerSession {
            stream: Some(stream),
            socket: None,
            stripe_buffer: None,
            compression: WireCompression::default(),
            metadata: self.metadata.clone(),
            stripe_channel,
            source,
            snapshot_ch: self.snapshot_ch.clone(),
            snapshot_state: self.snapshot_state.clone(),
            live_state: self.live_state.clone(),
            next_destination_id: self.next_destination_id.clone(),
        })
    }
}

impl StripeServerSession {
    /// Let a subscription made on this session be checked for liveness against
    /// the socket itself. `socket` must be another handle on the connection
    /// `stream` was built from.
    pub fn with_socket(mut self, socket: Box<dyn AsRawFd + Send>) -> Self {
        self.socket = Some(socket);
        self
    }
}

mod client;
mod compression;
mod legacy;
mod prepare;
mod psk;
mod session;
mod snapshot_push;

#[cfg(test)]
mod snapshot_e2e_tests;

pub use client::connect_to_stripe_server;
pub use compression::WireCompression;
pub use legacy::load_legacy_config;
pub use prepare::prepare_stripe_server;
pub use psk::{
    parse_psk_credentials, wrap_psk_client_stream, wrap_psk_server_stream, PskCredentials,
};
pub use snapshot_push::{PushedFrame, RemoteDestination, SnapshotSubscriber};
