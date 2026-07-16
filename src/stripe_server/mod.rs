use std::{
    io::{Read, Write},
    sync::Arc,
};

use crate::{
    block_device::{BlockDevice, IoChannel, UbiMetadata},
    stripe_source::{StripeSource, StripeSourceBuilder},
    Result,
};

pub trait ReadWrite: Read + Write {}
impl<T: Read + Write> ReadWrite for T {}

pub type DynStream = Box<dyn ReadWrite + Send>;

pub const METADATA_CMD: u8 = 0x00;
pub const READ_STRIPE_CMD: u8 = 0x01;
pub const HELLO_CMD: u8 = 0x02;

/// Remote stripe protocol version, reported by the hello command so a client can
/// detect a server it is not compatible with. Bump on incompatible wire changes.
pub const PROTOCOL_VERSION: u32 = 1;

pub const STATUS_OK: u8 = 0x00;
pub const STATUS_INVALID_STRIPE: u8 = 0x01;
pub const STATUS_NO_DATA: u8 = 0x02;
pub const STATUS_NOT_FETCHED: u8 = 0x03;
pub const STATUS_INVALID_COMMAND: u8 = 0xFE;
pub const STATUS_SERVER_ERROR: u8 = 0xFF;

pub struct StripeServer {
    metadata: Arc<UbiMetadata>,
    stripe_device: Arc<dyn BlockDevice>,
    // A stripe source builder, so each session can build its own source (the
    // source is not Send, so it cannot be shared across connection threads).
    // Used to serve stripes that have a source but have not been fetched yet.
    source_builder: Option<StripeSourceBuilder>,
}

pub struct StripeServerSession {
    stream: DynStream,
    metadata: Arc<UbiMetadata>,
    stripe_channel: Box<dyn IoChannel>,
    source: Option<Box<dyn StripeSource>>,
}

pub struct StripeServerClient {
    stream: DynStream,
    pub metadata: Option<UbiMetadata>,
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
        }
    }

    pub fn start_session(&self, stream: DynStream) -> Result<StripeServerSession> {
        let stripe_channel = self.stripe_device.create_channel()?;
        let source = self
            .source_builder
            .as_ref()
            .map(StripeSourceBuilder::build)
            .transpose()?;
        Ok(StripeServerSession {
            stream,
            metadata: self.metadata.clone(),
            stripe_channel,
            source,
        })
    }
}

mod client;
mod legacy;
mod prepare;
mod psk;
mod reconnect;
mod session;

pub use client::connect_to_stripe_server;
pub use legacy::load_legacy_config;
pub use prepare::prepare_stripe_server;
pub use psk::{
    parse_psk_credentials, wrap_psk_client_stream, wrap_psk_server_stream, PskCredentials,
};
pub use reconnect::{connect_reconnecting_stripe_client, ReconnectingStripeClient};
