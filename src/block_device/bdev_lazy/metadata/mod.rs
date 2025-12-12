mod init;
mod load;
mod shared_state;
mod types;

pub use init::init_metadata;
pub use load::load_metadata;
pub use shared_state::{Failed, Fetched, NoSource, NotFetched, SharedMetadataState};
pub use types::UbiMetadata;
pub use types::UBI_MAGIC;
