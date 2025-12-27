use std::{
    io::{Read, Write},
    sync::Arc,
};

use crate::{
    block_device::{BlockDevice, IoChannel, UbiMetadata},
    Result,
};

pub trait ReadWrite: Read + Write {}
impl<T: Read + Write> ReadWrite for T {}

pub type DynStream = Box<dyn ReadWrite + Send>;

pub const METADATA_CMD: u8 = 0x00;
pub const READ_STRIPE_CMD: u8 = 0x01;

pub const STATUS_OK: u8 = 0x00;
pub const STATUS_INVALID_STRIPE: u8 = 0x01;
pub const STATUS_UNWRITTEN: u8 = 0x02;
pub const STATUS_SERVER_ERROR: u8 = 0xFF;

pub struct StripeServer {
    metadata: Arc<UbiMetadata>,
    stripe_device: Arc<dyn BlockDevice>,
}

pub struct StripeServerSession {
    stream: DynStream,
    metadata: Arc<UbiMetadata>,
    stripe_channel: Box<dyn IoChannel>,
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
    pub fn new(stripe_device: Arc<dyn BlockDevice>, metadata: Arc<UbiMetadata>) -> Self {
        Self {
            stripe_device,
            metadata,
        }
    }

    pub fn start_session(&self, stream: DynStream) -> Result<StripeServerSession> {
        let stripe_channel = self.stripe_device.create_channel()?;
        Ok(StripeServerSession {
            stream,
            metadata: self.metadata.clone(),
            stripe_channel,
        })
    }
}

mod client;
mod prepare;
mod psk;
mod session;

pub use client::connect_to_stripe_server;
pub use prepare::prepare_stripe_server;
pub use psk::{wrap_psk_client_stream, wrap_psk_server_stream, PskCredentials};
