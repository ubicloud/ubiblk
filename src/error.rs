use thiserror::Error;

#[macro_export]
macro_rules! ubiblk_error {
    ($variant:ident { $($field:ident : $value:expr),* $(,)? }) => {{
        $crate::UbiblkError::$variant {
            $($field: $value,)*
            file: file!(),
            line: line!(),
        }
    }};
    ($variant:ident) => {{
        $crate::UbiblkError::$variant {
            file: file!(),
            line: line!(),
        }
    }};
}

#[derive(Error, Debug)]
pub enum UbiblkError {
    #[error("Thread creation error: {source} (at {file}:{line})")]
    ThreadCreation {
        #[source]
        source: std::io::Error,
        file: &'static str,
        line: u32,
    },
    #[error("I/O channel creation error: {source} (at {file}:{line})")]
    IoChannelCreation {
        #[source]
        source: std::io::Error,
        file: &'static str,
        line: u32,
    },
    #[error("Guest memory access error: {source} (at {file}:{line})")]
    GuestMemoryAccess {
        #[source]
        source: vm_memory::GuestMemoryError,
        file: &'static str,
        line: u32,
    },
    #[error("I/O error: {source} (at {file}:{line})")]
    IoError {
        source: std::io::Error,
        file: &'static str,
        line: u32,
    },
    #[error("Channel error: {reason} (at {file}:{line})")]
    ChannelError {
        reason: String,
        file: &'static str,
        line: u32,
    },
    #[error("Invalid parameter error: {description} (at {file}:{line})")]
    InvalidParameter {
        description: String,
        file: &'static str,
        line: u32,
    },
    #[error("Metadata error: {description} (at {file}:{line})")]
    MetadataError {
        description: String,
        file: &'static str,
        line: u32,
    },
    #[error("Protocol error: {description} (at {file}:{line})")]
    ProtocolError {
        description: String,
        file: &'static str,
        line: u32,
    },
    #[error("Missing stripe metadata on client (at {file}:{line})")]
    MissingStripeMetadata { file: &'static str, line: u32 },
    #[error("Stripe {stripe} is unwritten (at {file}:{line})")]
    UnwrittenStripe {
        stripe: u64,
        file: &'static str,
        line: u32,
    },
    #[error("Stripe {stripe} size mismatch: expected {expected} bytes, got {actual} bytes (at {file}:{line})")]
    StripeSizeMismatch {
        stripe: u64,
        expected: usize,
        actual: usize,
        file: &'static str,
        line: u32,
    },
    #[error("Stripe fetch failed for stripe {stripe} (at {file}:{line})")]
    StripeFetchFailed {
        stripe: usize,
        file: &'static str,
        line: u32,
    },
    #[error("Stripe fetch timeout for stripe {stripe} (at {file}:{line})")]
    StripeFetchTimeout {
        stripe: usize,
        file: &'static str,
        line: u32,
    },
    #[error("Remote server returned error status: {status} (at {file}:{line})")]
    RemoteStatus {
        status: u8,
        file: &'static str,
        line: u32,
    },
    #[error("TLS setup failed: {description} (at {file}:{line})")]
    TlsError {
        description: String,
        file: &'static str,
        line: u32,
    },
    #[error("Background worker error: {description} (at {file}:{line})")]
    BackgroundWorkerError {
        description: String,
        file: &'static str,
        line: u32,
    },
    #[error("RPC error: {description} (at {file}:{line})")]
    RpcError {
        description: String,
        file: &'static str,
        line: u32,
    },
    #[error("Vhost user backend error: {reason} (at {file}:{line})")]
    VhostUserBackendError {
        reason: vhost_user_backend::Error,
        file: &'static str,
        line: u32,
    },
    #[error("Archive error: {description} (at {file}:{line})")]
    ArchiveError {
        description: String,
        file: &'static str,
        line: u32,
    },
    #[error("Cryptography error: {description} (at {file}:{line})")]
    CryptoError {
        description: String,
        file: &'static str,
        line: u32,
    },
    #[error("CPU pinning error: {source} (at {file}:{line})")]
    CpuPinning {
        #[source]
        source: nix::Error,
        file: &'static str,
        line: u32,
    },
}

pub type Error = UbiblkError;
pub type Result<T> = std::result::Result<T, Error>;

impl From<std::io::Error> for UbiblkError {
    #[track_caller]
    fn from(source: std::io::Error) -> Self {
        let location = std::panic::Location::caller();
        UbiblkError::IoError {
            source,
            file: location.file(),
            line: location.line(),
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_invalid_parameter_format() {
        let error = crate::ubiblk_error!(InvalidParameter {
            description: "Test error".to_string(),
        });
        let rendered = format!("{error}");
        assert!(
            rendered.starts_with("Invalid parameter error: Test error (at "),
            "unexpected error display: {rendered}"
        );
        assert!(
            rendered.contains("src/error.rs:"),
            "missing file location: {rendered}"
        );
    }

    #[test]
    fn test_io_error_format() {
        let io_error = std::io::Error::other("Test IO error");
        let error = crate::ubiblk_error!(IoError { source: io_error });
        let rendered = format!("{error}");
        assert!(
            rendered.starts_with("I/O error: Test IO error (at "),
            "unexpected error display: {rendered}"
        );
        assert!(
            rendered.contains("src/error.rs:"),
            "missing file location: {rendered}"
        );
    }

    #[test]
    fn test_guest_memory_access_format() {
        let guest_memory_error = vm_memory::GuestMemoryError::InvalidBackendAddress;
        let error = crate::ubiblk_error!(GuestMemoryAccess {
            source: guest_memory_error,
        });
        let rendered = format!("{error}");
        assert!(
            rendered.starts_with(
                "Guest memory access error: Guest memory error: invalid backend address (at "
            ),
            "unexpected error display: {rendered}"
        );
        assert!(
            rendered.contains("src/error.rs:"),
            "missing file location: {rendered}"
        );
    }

    #[test]
    fn test_thread_creation_format() {
        let error = crate::ubiblk_error!(ThreadCreation {
            source: std::io::Error::other("spawn error"),
        });
        let rendered = format!("{error}");
        assert!(
            rendered.starts_with("Thread creation error: spawn error (at "),
            "unexpected error display: {rendered}"
        );
        assert!(
            rendered.contains("src/error.rs:"),
            "missing file location: {rendered}"
        );
    }

    #[test]
    fn test_io_channel_creation_format() {
        let io_error = std::io::Error::other("Test IO error");
        let error = crate::ubiblk_error!(IoChannelCreation { source: io_error });
        let rendered = format!("{error}");
        assert!(
            rendered.starts_with("I/O channel creation error: Test IO error (at "),
            "unexpected error display: {rendered}"
        );
        assert!(
            rendered.contains("src/error.rs:"),
            "missing file location: {rendered}"
        );
    }

    #[test]
    fn test_channel_error_format() {
        let error = crate::ubiblk_error!(ChannelError {
            reason: "Disconnected".to_string(),
        });
        let rendered = format!("{error}");
        assert!(
            rendered.starts_with("Channel error: Disconnected (at "),
            "unexpected error display: {rendered}"
        );
        assert!(
            rendered.contains("src/error.rs:"),
            "missing file location: {rendered}"
        );
    }

    #[test]
    fn test_metadata_error_format() {
        let error = crate::ubiblk_error!(MetadataError {
            description: "Test metadata error".to_string(),
        });
        let rendered = format!("{error}");
        assert!(
            rendered.starts_with("Metadata error: Test metadata error (at "),
            "unexpected error display: {rendered}"
        );
        assert!(
            rendered.contains("src/error.rs:"),
            "missing file location: {rendered}"
        );
    }

    #[test]
    fn test_unwritten_stripe_format() {
        let error = crate::ubiblk_error!(UnwrittenStripe { stripe: 42 });
        let rendered = format!("{error}");
        assert!(
            rendered.starts_with("Stripe 42 is unwritten (at "),
            "unexpected error display: {rendered}"
        );
        assert!(
            rendered.contains("src/error.rs:"),
            "missing file location: {rendered}"
        );
    }

    #[test]
    fn test_protocol_error_format() {
        let error = crate::ubiblk_error!(ProtocolError {
            description: "Invalid status byte".to_string(),
        });
        let rendered = format!("{error}");
        assert!(
            rendered.starts_with("Protocol error: Invalid status byte (at "),
            "unexpected error display: {rendered}"
        );
        assert!(
            rendered.contains("src/error.rs:"),
            "missing file location: {rendered}"
        );
    }
}
