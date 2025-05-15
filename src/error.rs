use thiserror::Error;

#[derive(Error, Debug)]
pub enum VhostUserBlockError {
    #[error("Thread creation error")]
    ThreadCreation,
    #[error("I/O channel creation error")]
    IoChannelCreation {
        #[source]
        source: std::io::Error,
    },
    #[error("Guest memory access error")]
    GuestMemoryAccess {
        #[source]
        source: vm_memory::GuestMemoryError,
    },
    #[error("I/O error")]
    IoError {
        #[source]
        source: std::io::Error,
    },
    #[error("Channel error")]
    ChannelError,
    #[error("Invalid parameter error")]
    InvalidParameter { description: String },
}

pub type Result<T> = std::result::Result<T, VhostUserBlockError>;
