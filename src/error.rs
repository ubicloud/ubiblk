use thiserror::Error;

#[derive(Error, Debug)]
pub enum UbiblkError {
    #[error("Thread creation error: {source}")]
    ThreadCreation {
        #[source]
        source: std::io::Error,
    },
    #[error("I/O channel creation error: {source}")]
    IoChannelCreation {
        #[source]
        source: std::io::Error,
    },
    #[error("Guest memory access error: {source}")]
    GuestMemoryAccess {
        #[source]
        source: vm_memory::GuestMemoryError,
    },
    #[error("I/O error: {source}")]
    IoError {
        #[from]
        source: std::io::Error,
    },
    #[error("Channel error: {reason}")]
    ChannelError { reason: String },
    #[error("Invalid parameter error: {description}")]
    InvalidParameter { description: String },
    #[error("Metadata error: {description}")]
    MetadataError { description: String },
    #[error("Protocol error: {description}")]
    ProtocolError { description: String },
    #[error("Missing stripe metadata on client")]
    MissingStripeMetadata,
    #[error("Stripe {stripe} is unwritten")]
    UnwrittenStripe { stripe: u64 },
    #[error("Stripe {stripe} size mismatch: expected {expected} bytes, got {actual} bytes")]
    StripeSizeMismatch {
        stripe: u64,
        expected: usize,
        actual: usize,
    },
    #[error("Stripe fetch failed for stripe {stripe}")]
    StripeFetchFailed { stripe: usize },
    #[error("Stripe fetch timeout for stripe {stripe}")]
    StripeFetchTimeout { stripe: usize },
    #[error("Remote server returned error status: {status}")]
    RemoteStatus { status: u8 },
    #[error("TLS setup failed: {description}")]
    TlsError { description: String },
    #[error("Background worker error: {description}")]
    BackgroundWorkerError { description: String },
    #[error("RPC error: {description}")]
    RpcError { description: String },
    #[error("Vhost user backend error: {reason}")]
    VhostUserBackendError { reason: vhost_user_backend::Error },
    #[error("Archive error: {description}")]
    ArchiveError { description: String },
    #[error("Cryptography error: {description}")]
    CryptoError { description: String },
    #[error("CPU pinning error: {source}")]
    CpuPinning {
        #[source]
        source: nix::Error,
    },
}

pub type Error = UbiblkError;
pub type Result<T> = std::result::Result<T, Error>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_invalid_parameter_format() {
        let error = UbiblkError::InvalidParameter {
            description: "Test error".to_string(),
        };
        assert_eq!(format!("{error}"), "Invalid parameter error: Test error");
    }

    #[test]
    fn test_io_error_format() {
        let io_error = std::io::Error::other("Test IO error");
        let error = UbiblkError::IoError { source: io_error };
        assert_eq!(format!("{error}"), "I/O error: Test IO error");
    }

    #[test]
    fn test_guest_memory_access_format() {
        let guest_memory_error = vm_memory::GuestMemoryError::InvalidBackendAddress;
        let error = UbiblkError::GuestMemoryAccess {
            source: guest_memory_error,
        };
        assert_eq!(
            format!("{error}"),
            "Guest memory access error: Guest memory error: invalid backend address"
        );
    }

    #[test]
    fn test_thread_creation_format() {
        let error = UbiblkError::ThreadCreation {
            source: std::io::Error::other("spawn error"),
        };
        assert_eq!(format!("{error}"), "Thread creation error: spawn error");
    }

    #[test]
    fn test_io_channel_creation_format() {
        let io_error = std::io::Error::other("Test IO error");
        let error = UbiblkError::IoChannelCreation { source: io_error };
        assert_eq!(
            format!("{error}"),
            "I/O channel creation error: Test IO error"
        );
    }

    #[test]
    fn test_channel_error_format() {
        let error = UbiblkError::ChannelError {
            reason: "Disconnected".to_string(),
        };
        assert_eq!(format!("{error}"), "Channel error: Disconnected");
    }

    #[test]
    fn test_metadata_error_format() {
        let error = UbiblkError::MetadataError {
            description: "Test metadata error".to_string(),
        };
        assert_eq!(format!("{error}"), "Metadata error: Test metadata error");
    }

    #[test]
    fn test_unwritten_stripe_format() {
        let error = UbiblkError::UnwrittenStripe { stripe: 42 };
        assert_eq!(format!("{error}"), "Stripe 42 is unwritten");
    }

    #[test]
    fn test_protocol_error_format() {
        let error = UbiblkError::ProtocolError {
            description: "Invalid status byte".to_string(),
        };
        assert_eq!(format!("{error}"), "Protocol error: Invalid status byte");
    }
}
