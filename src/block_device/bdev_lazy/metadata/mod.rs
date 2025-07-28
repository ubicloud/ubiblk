mod init;
mod load;
mod metadata;

pub use init::init_metadata;
pub use load::load_metadata;
pub use metadata::UbiMetadata;
pub use metadata::{UBI_MAGIC, UBI_MAX_STRIPES};

#[cfg(test)]
pub use metadata::UBI_MAGIC_SIZE;
