mod init;
mod load;
mod types;

pub use init::init_metadata;
pub use load::load_metadata;
pub use types::UbiMetadata;
pub use types::{UBI_MAGIC, UBI_MAX_STRIPES};

#[cfg(test)]
pub use types::UBI_MAGIC_SIZE;
