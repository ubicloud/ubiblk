use thiserror::Error;

#[macro_export]
macro_rules! ubiblk_error {
    ($variant:ident { $($field:ident : $value:expr),* $(,)? }) => {{
        $crate::UbiblkError::$variant {
            $($field: $value,)*
            context: $crate::ErrorLocation::new(file!(), line!()),
        }
    }};
    ($variant:ident) => {{
        $crate::UbiblkError::$variant {
            context: $crate::ErrorLocation::new(file!(), line!()),
        }
    }};
}

#[derive(Debug, Clone, Copy)]
pub struct ErrorLocation {
    file: &'static str,
    line: u32,
}

impl ErrorLocation {
    pub const fn new(file: &'static str, line: u32) -> Self {
        Self { file, line }
    }
}

impl std::fmt::Display for ErrorLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.file, self.line)
    }
}

#[derive(Error, Debug)]
pub enum UbiblkError {
    #[error("Thread creation error: {source} (at {context})")]
    ThreadCreation {
        #[source]
        source: std::io::Error,
        context: ErrorLocation,
    },
    #[error("I/O channel creation error: {source} (at {context})")]
    IoChannelCreation {
        #[source]
        source: std::io::Error,
        context: ErrorLocation,
    },
    #[error("Guest memory access error: {source} (at {context})")]
    GuestMemoryAccess {
        #[source]
        source: vm_memory::GuestMemoryError,
        context: ErrorLocation,
    },
    #[error("I/O error: {source} (at {context})")]
    IoError {
        source: std::io::Error,
        context: ErrorLocation,
    },
    #[error("Channel error: {reason} (at {context})")]
    ChannelError {
        reason: String,
        context: ErrorLocation,
    },
    #[error("Invalid parameter error: {description} (at {context})")]
    InvalidParameter {
        description: String,
        context: ErrorLocation,
    },
    #[error("Metadata error: {description} (at {context})")]
    MetadataError {
        description: String,
        context: ErrorLocation,
    },
    #[error("Protocol error: {description} (at {context})")]
    ProtocolError {
        description: String,
        context: ErrorLocation,
    },
    #[error("Missing stripe metadata on client (at {context})")]
    MissingStripeMetadata { context: ErrorLocation },
    #[error("Stripe {stripe} is unavailable (at {context})")]
    StripeUnavailableData { stripe: u64, context: ErrorLocation },
    #[error("Stripe {stripe} size mismatch: expected {expected} bytes, got {actual} bytes (at {context})")]
    StripeSizeMismatch {
        stripe: u64,
        expected: usize,
        actual: usize,
        context: ErrorLocation,
    },
    #[error("Stripe fetch failed for stripe {stripe} (at {context})")]
    StripeFetchFailed {
        stripe: usize,
        context: ErrorLocation,
    },
    #[error("Stripe fetch timeout for stripe {stripe} (at {context})")]
    StripeFetchTimeout {
        stripe: usize,
        context: ErrorLocation,
    },
    #[error("Remote server returned error status: {status} (at {context})")]
    RemoteStatus { status: u8, context: ErrorLocation },
    #[error("TLS setup failed: {description} (at {context})")]
    TlsError {
        description: String,
        context: ErrorLocation,
    },
    #[error("Background worker error: {description} (at {context})")]
    BackgroundWorkerError {
        description: String,
        context: ErrorLocation,
    },
    #[error("RPC error: {description} (at {context})")]
    RpcError {
        description: String,
        context: ErrorLocation,
    },
    #[error("Vhost user backend error: {reason} (at {context})")]
    VhostUserBackendError {
        reason: vhost_user_backend::Error,
        context: ErrorLocation,
    },
    #[error("Archive error: {description} (at {context})")]
    ArchiveError {
        description: String,
        context: ErrorLocation,
    },
    #[error("Cryptography error: {description} (at {context})")]
    CryptoError {
        description: String,
        context: ErrorLocation,
    },
    #[error("CPU pinning error: {source} (at {context})")]
    CpuPinning {
        #[source]
        source: nix::Error,
        context: ErrorLocation,
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
            context: ErrorLocation::new(location.file(), location.line()),
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
    fn test_stripe_unavailable_data_format() {
        let error = crate::ubiblk_error!(StripeUnavailableData { stripe: 42 });
        let rendered = format!("{error}");
        assert!(
            rendered.starts_with("Stripe 42 is unavailable (at "),
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
