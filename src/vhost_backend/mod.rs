mod backend;
mod backend_loop;
mod io_tracking;
mod options;
mod request;
mod rpc;
pub use backend_loop::{
    block_backend_loop, build_block_device, build_source_device, init_metadata,
};
pub use options::{
    ArchiveStripeSourceConfig, AwsCredentials, IoEngine, Options, StripeSourceConfig,
};
mod backend_thread;

pub const SECTOR_SIZE: usize = 512;

#[cfg(test)]
mod backend_tests;

#[cfg(test)]
pub use backend::UbiBlkBackend;
