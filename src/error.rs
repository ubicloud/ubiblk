use thiserror::Error;

#[derive(Error, Debug)]
pub enum VhostUserBlockError {
    #[error("Thread creation error")]
    ThreadCreation,
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
        #[source]
        source: std::io::Error,
    },
    #[error("Channel error")]
    ChannelError,
    #[error("Invalid parameter error: {description}")]
    InvalidParameter { description: String },
    #[error("Metadata error: {description}")]
    MetadataError { description: String },
}

pub type Result<T> = std::result::Result<T, VhostUserBlockError>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_invalid_parameter_format() {
        let error = VhostUserBlockError::InvalidParameter {
            description: "Test error".to_string(),
        };
        assert_eq!(format!("{error}"), "Invalid parameter error: Test error");
    }

    #[test]
    fn test_io_error_format() {
        let io_error = std::io::Error::other("Test IO error");
        let error = VhostUserBlockError::IoError { source: io_error };
        assert_eq!(format!("{error}"), "I/O error: Test IO error");
    }

    #[test]
    fn test_guest_memory_access_format() {
        let guest_memory_error = vm_memory::GuestMemoryError::InvalidBackendAddress;
        let error = VhostUserBlockError::GuestMemoryAccess {
            source: guest_memory_error,
        };
        assert_eq!(
            format!("{error}"),
            "Guest memory access error: Guest memory error: invalid backend address"
        );
    }

    #[test]
    fn test_thread_creation_format() {
        let error = VhostUserBlockError::ThreadCreation;
        assert_eq!(format!("{error}"), "Thread creation error");
    }

    #[test]
    fn test_io_channel_creation_format() {
        let io_error = std::io::Error::other("Test IO error");
        let error = VhostUserBlockError::IoChannelCreation { source: io_error };
        assert_eq!(
            format!("{error}"),
            "I/O channel creation error: Test IO error"
        );
    }

    #[test]
    fn test_channel_error_format() {
        let error = VhostUserBlockError::ChannelError;
        assert_eq!(format!("{error}"), "Channel error");
    }

    #[test]
    fn test_metadata_error_format() {
        let error = VhostUserBlockError::MetadataError {
            description: "Test metadata error".to_string(),
        };
        assert_eq!(format!("{error}"), "Metadata error: Test metadata error");
    }
}
