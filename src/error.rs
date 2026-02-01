use std::sync::mpsc::SendError;

use thiserror::Error;

#[macro_export]
macro_rules! ubiblk_error {
    ($variant:ident { $($field:ident : $value:expr),* $(,)? }) => {{
        $crate::UbiblkError::$variant {
            $($field: $value,)*
            meta: $crate::ErrorMeta::new($crate::ErrorLocation::new(file!(), line!())),
        }
    }};
    ($variant:ident) => {{
        $crate::UbiblkError::$variant {
            meta: $crate::ErrorMeta::new($crate::ErrorLocation::new(file!(), line!())),
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

impl Default for ErrorLocation {
    fn default() -> Self {
        Self {
            file: "<unknown>",
            line: 0,
        }
    }
}

impl std::fmt::Display for ErrorLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.file, self.line)
    }
}

#[derive(Debug, Clone)]
pub struct ErrorContext {
    message: String,
    location: ErrorLocation,
}

impl ErrorContext {
    pub fn new(message: impl Into<String>, location: ErrorLocation) -> Self {
        Self {
            message: message.into(),
            location,
        }
    }
}

impl std::fmt::Display for ErrorContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} (at {})", self.message, self.location)
    }
}

#[derive(Debug, Clone, Default)]
pub struct ErrorContexts(Vec<ErrorContext>);

impl ErrorContexts {
    pub fn push(&mut self, context: ErrorContext) {
        self.0.push(context);
    }
}

impl std::fmt::Display for ErrorContexts {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for context in self.0.iter() {
            write!(f, "\nContext: {context}")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct ErrorMeta {
    pub location: ErrorLocation,
    pub contexts: ErrorContexts,
}

impl ErrorMeta {
    pub fn new(location: ErrorLocation) -> Self {
        Self {
            location,
            contexts: ErrorContexts::default(),
        }
    }
}

impl Default for ErrorMeta {
    #[track_caller]
    fn default() -> Self {
        let location = std::panic::Location::caller();
        Self::new(ErrorLocation::new(location.file(), location.line()))
    }
}

impl std::fmt::Display for ErrorMeta {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            return write!(f, "(at {})", self.location);
        }
        if self.contexts.0.is_empty() {
            return Ok(());
        }
        let mut iter = self.contexts.0.iter().rev();
        if let Some(context) = iter.next() {
            write!(f, "{context}")?;
        }
        for context in iter {
            write!(f, "\n  - caused by: {context}")?;
        }
        write!(f, "\n  - caused by: ")?;
        Ok(())
    }
}

macro_rules! ubiblk_error_variants {
    ($( $variant:ident { $( $(#[$field_attr:meta])* $field:ident : $ty:ty ),* $(,)? } => $message:expr ),* $(,)?) => {
        #[derive(Error, Debug)]
        pub enum UbiblkError {
            $(
                #[error($message)]
                $variant {
                    $( $(#[$field_attr])* $field: $ty, )*
                },
            )*
        }

        impl UbiblkError {
            fn contexts_mut(&mut self) -> &mut ErrorContexts {
                match self {
                    $( UbiblkError::$variant { meta, .. } => &mut meta.contexts, )*
                }
            }
        }
    };
}

macro_rules! ubiblk_error_from_value {
    ($field:ident) => {
        $field
    };
    ($field:ident, $into:ty) => {
        $field.into()
    };
}

macro_rules! ubiblk_error_from {
    ($( #[from] $variant:ident ( $field:ident : $ty:ty $(=> $into:ty)? ) ),* $(,)?) => {
        $(
            impl From<$ty> for UbiblkError {
                #[track_caller]
                fn from($field: $ty) -> Self {
                    let location = std::panic::Location::caller();
                    UbiblkError::$variant {
                        $field: ubiblk_error_from_value!($field $(, $into)?),
                        meta: ErrorMeta::new(ErrorLocation::new(location.file(), location.line())),
                    }
                }
            }
        )*
    };
}

#[derive(Debug, Error)]
pub enum TlsErrorSource {
    #[error(transparent)]
    Ssl(#[from] openssl::ssl::Error),
    #[error(transparent)]
    Stack(#[from] openssl::error::ErrorStack),
}

ubiblk_error_variants! {
    ThreadCreation {
        #[source]
        source: std::io::Error,
        meta: ErrorMeta,
    } => "{meta}Thread creation error: {source} {meta:#}",
    IoChannelCreation {
        #[source]
        source: std::io::Error,
        meta: ErrorMeta,
    } => "{meta}I/O channel creation error: {source} {meta:#}",
    GuestMemoryAccess {
        #[source]
        source: vm_memory::GuestMemoryError,
        meta: ErrorMeta,
    } => "{meta}Guest memory access error: {source} {meta:#}",
    IoError {
        #[source]
        source: std::io::Error,
        meta: ErrorMeta,
    } => "{meta}I/O error: {source} {meta:#}",
    ChannelError {
        reason: String,
        meta: ErrorMeta,
    } => "{meta}Channel error: {reason} {meta:#}",
    InvalidParameter {
        description: String,
        meta: ErrorMeta,
    } => "{meta}Invalid parameter error: {description} {meta:#}",
    MetadataError {
        description: String,
        meta: ErrorMeta,
    } => "{meta}Metadata error: {description} {meta:#}",
    ProtocolError {
        description: String,
        meta: ErrorMeta,
    } => "{meta}Protocol error: {description} {meta:#}",
    MissingStripeMetadata {
        meta: ErrorMeta,
    } => "{meta}Missing stripe metadata on client {meta:#}",
    StripeUnavailableData {
        stripe: u64,
        meta: ErrorMeta,
    } => "{meta}Stripe {stripe} is unavailable {meta:#}",
    StripeSizeMismatch {
        stripe: u64,
        expected: usize,
        actual: usize,
        meta: ErrorMeta,
    } => "{meta}Stripe {stripe} size mismatch: expected {expected} bytes, got {actual} bytes {meta:#}",
    StripeFetchFailed {
        stripe: usize,
        meta: ErrorMeta,
    } => "{meta}Stripe fetch failed for stripe {stripe} {meta:#}",
    StripeFetchTimeout {
        stripe: usize,
        meta: ErrorMeta,
    } => "{meta}Stripe fetch timeout for stripe {stripe} {meta:#}",
    RemoteStatus {
        status: u8,
        meta: ErrorMeta,
    } => "{meta}Remote server returned error status: {status} {meta:#}",
    TlsError {
        #[source]
        source: TlsErrorSource,
        meta: ErrorMeta,
    } => "{meta}TLS setup failed: {source} {meta:#}",
    BackgroundWorkerError {
        description: String,
        meta: ErrorMeta,
    } => "{meta}Background worker error: {description} {meta:#}",
    RpcError {
        description: String,
        meta: ErrorMeta,
    } => "{meta}RPC error: {description} {meta:#}",
    VhostUserError {
        #[source]
        source: vhost::vhost_user::Error,
        meta: ErrorMeta,
    } => "{meta}Vhost user error: {source} {meta:#}",
    VhostUserBackendError {
        reason: vhost_user_backend::Error,
        meta: ErrorMeta,
    } => "{meta}Vhost user backend error: {reason} {meta:#}",
    ArchiveError {
        description: String,
        meta: ErrorMeta,
    } => "{meta}Archive error: {description} {meta:#}",
    CryptoError {
        description: String,
        meta: ErrorMeta,
    } => "{meta}Cryptography error: {description} {meta:#}",
    CpuPinning {
        #[source]
        source: nix::Error,
        meta: ErrorMeta,
    } => "{meta}CPU pinning error: {source} {meta:#}",
    UblkError {
        #[source]
        source: libublk::UblkError,
        meta: ErrorMeta,
    } => "{meta}Ublk error: {source} {meta:#}",
}

ubiblk_error_from! {
    #[from] IoError(source: std::io::Error),
    #[from] VhostUserError(source: vhost::vhost_user::Error),
    #[from] VhostUserBackendError(reason: vhost_user_backend::Error),
    #[from] TlsError(source: openssl::ssl::Error => TlsErrorSource),
    #[from] TlsError(source: openssl::error::ErrorStack => TlsErrorSource),
    #[from] UblkError(source: libublk::UblkError),
}

pub type Error = UbiblkError;
pub type Result<T> = std::result::Result<T, Error>;

impl UbiblkError {
    #[track_caller]
    pub fn context(self, message: impl Into<String>) -> Self {
        let location = std::panic::Location::caller();
        self.context_at(message, location)
    }

    pub fn context_at(
        mut self,
        message: impl Into<String>,
        location: &'static std::panic::Location<'static>,
    ) -> Self {
        let context = ErrorContext::new(
            message,
            ErrorLocation::new(location.file(), location.line()),
        );
        self.contexts_mut().push(context);
        self
    }
}

pub trait ResultExt<T> {
    fn context(self, message: impl Into<String>) -> Result<T>;
}

impl<T, E> ResultExt<T> for std::result::Result<T, E>
where
    E: Into<UbiblkError>,
{
    #[track_caller]
    fn context(self, message: impl Into<String>) -> Result<T> {
        let location = std::panic::Location::caller();
        self.map_err(|e| e.into().context_at(message, location))
    }
}

impl<T> From<SendError<T>> for UbiblkError {
    #[track_caller]
    fn from(source: SendError<T>) -> Self {
        let location = std::panic::Location::caller();
        UbiblkError::ChannelError {
            reason: source.to_string(),
            meta: ErrorMeta::new(ErrorLocation::new(location.file(), location.line())),
        }
    }
}

#[cfg(test)]
mod tests {
    use libublk::UblkError;
    use ubiblk_macros::error_context;

    use super::*;

    fn assert_starts_with(haystack: &str, needle: &str) {
        assert!(
            haystack.starts_with(needle),
            "expected '{}' to start with '{}'",
            haystack,
            needle
        );
    }

    fn assert_contains(haystack: &str, needle: &str) {
        assert!(
            haystack.contains(needle),
            "expected '{}' to contain '{}'",
            haystack,
            needle
        );
    }

    #[test]
    fn test_invalid_parameter_format() {
        let error = crate::ubiblk_error!(InvalidParameter {
            description: "Test error".to_string(),
        });
        let rendered = format!("{error}");
        assert_starts_with(&rendered, "Invalid parameter error: Test error (at ");
        assert_contains(&rendered, "src/error.rs:");
    }

    #[test]
    fn test_io_error_format() {
        let io_error = std::io::Error::other("Test IO error");
        let error = crate::ubiblk_error!(IoError { source: io_error });
        let rendered = format!("{error}");
        assert_starts_with(&rendered, "I/O error: Test IO error (at ");
        assert_contains(&rendered, "src/error.rs:");
    }

    #[test]
    fn test_guest_memory_access_format() {
        let guest_memory_error = vm_memory::GuestMemoryError::InvalidBackendAddress;
        let error = crate::ubiblk_error!(GuestMemoryAccess {
            source: guest_memory_error,
        });
        let rendered = format!("{error}");
        assert_starts_with(
            &rendered,
            "Guest memory access error: Guest memory error: invalid backend address (at ",
        );
        assert_contains(&rendered, "src/error.rs:");
    }

    #[test]
    fn test_thread_creation_format() {
        let error = crate::ubiblk_error!(ThreadCreation {
            source: std::io::Error::other("spawn error"),
        });
        let rendered = format!("{error}");
        assert_starts_with(&rendered, "Thread creation error: spawn error (at ");
        assert_contains(&rendered, "src/error.rs:");
    }

    #[test]
    fn test_io_channel_creation_format() {
        let io_error = std::io::Error::other("Test IO error");
        let error = crate::ubiblk_error!(IoChannelCreation { source: io_error });
        let rendered = format!("{error}");
        assert_starts_with(&rendered, "I/O channel creation error: Test IO error (at ");
        assert_contains(&rendered, "src/error.rs:");
    }

    #[test]
    fn test_channel_error_format() {
        let error = crate::ubiblk_error!(ChannelError {
            reason: "Disconnected".to_string(),
        });
        let rendered = format!("{error}");
        assert_starts_with(&rendered, "Channel error: Disconnected (at ");
        assert_contains(&rendered, "src/error.rs:");
    }

    #[test]
    fn test_metadata_error_format() {
        let error = crate::ubiblk_error!(MetadataError {
            description: "Test metadata error".to_string(),
        });
        let rendered = format!("{error}");
        assert_starts_with(&rendered, "Metadata error: Test metadata error (at ");
        assert_contains(&rendered, "src/error.rs:");
    }

    #[test]
    fn test_stripe_unavailable_data_format() {
        let error = crate::ubiblk_error!(StripeUnavailableData { stripe: 42 });
        let rendered = format!("{error}");
        assert_starts_with(&rendered, "Stripe 42 is unavailable (at ");
        assert_contains(&rendered, "src/error.rs:");
    }

    #[test]
    fn test_protocol_error_format() {
        let error = crate::ubiblk_error!(ProtocolError {
            description: "Invalid status byte".to_string(),
        });
        let rendered = format!("{error}");
        assert_starts_with(&rendered, "Protocol error: Invalid status byte (at ");
        assert_contains(&rendered, "src/error.rs:");
    }

    #[test]
    fn test_conversion_from_vhost_user_backend_error() {
        let some_io_error = std::io::Error::other("IO failure");
        let vhub_error = vhost_user_backend::Error::StartDaemon(some_io_error);
        let ubiblk_error: UbiblkError = vhub_error.into();
        let rendered = format!("{ubiblk_error}");
        assert_starts_with(
            &rendered,
            "Vhost user backend error: failed to start daemon: IO failure (at ",
        );
        assert_contains(&rendered, "src/error.rs:");
    }

    #[test]
    fn test_conversion_from_vhost_user_error() {
        let vhu_error = vhost::vhost_user::Error::InvalidMessage;
        let ubiblk_error: UbiblkError = vhu_error.into();
        let rendered = format!("{ubiblk_error}");
        assert_starts_with(&rendered, "Vhost user error: invalid message (at ");
        assert_contains(&rendered, "src/error.rs:");
    }

    #[test]
    fn test_conversion_from_ublk_error() {
        let ublk_error = UblkError::InvalidVal;
        let ubiblk_error: UbiblkError = ublk_error.into();
        let rendered = format!("{ubiblk_error}");
        assert_starts_with(&rendered, "Ublk error: Invalid input (at ");
        assert_contains(&rendered, "src/error.rs:");
    }

    #[test]
    fn test_conversion_from_send_error() {
        let (tx, rx) = std::sync::mpsc::channel::<i32>();
        drop(rx); // Close the receiver to cause a SendError
        let send_error = tx.send(42).unwrap_err();
        let line = line!();
        let ubiblk_error: UbiblkError = send_error.into();
        let rendered = format!("{ubiblk_error}");
        let expected = format!(
            "Channel error: sending on a closed channel (at {}:{})",
            file!(),
            line + 1
        );
        assert_eq!(rendered, expected);
    }

    #[test]
    fn test_conversion_from_openssl_error_stack() {
        let line = line!();
        let openssl_error = openssl::error::ErrorStack::get();
        let ubiblk_error: UbiblkError = openssl_error.into();
        let rendered = format!("{ubiblk_error}");
        let expected = format!(
            "TLS setup failed: OpenSSL error (at {}:{})",
            file!(),
            line + 2
        );
        assert_eq!(rendered, expected);
    }

    #[test]
    fn test_conversion_from_openssl_ssl_error() {
        let line = line!();
        let openssl_error: openssl::ssl::Error = openssl::error::ErrorStack::get().into();
        let ubiblk_error: UbiblkError = openssl_error.into();
        let rendered = format!("{ubiblk_error}");
        let expected = format!(
            "TLS setup failed: OpenSSL error (at {}:{})",
            file!(),
            line + 2
        );
        assert_eq!(rendered, expected);
    }

    #[test]
    fn test_context_stack_format() {
        let line = line!();
        let error = crate::ubiblk_error!(InvalidParameter {
            description: "Test error".to_string(),
        })
        .context("inner context")
        .context("outer context");
        let rendered = format!("{error}");
        let expected = format!(
            "outer context (at {}:{})\n  - caused by: inner context (at {}:{})\n  - caused by: Invalid parameter error: Test error (at {}:{})",
            file!(),
            line + 5,
            file!(),
            line + 4,
            file!(),
            line + 1
        );
        assert_eq!(rendered, expected);
    }

    #[test]
    fn test_result_ext_context_with_question_operator() {
        fn inner_operation(lines: &mut Vec<u32>) -> Result<()> {
            lines.push(line!() + 1);
            Err(std::io::Error::other("inner error"))?;
            Ok(())
        }
        fn middle_operation(lines: &mut Vec<u32>) -> Result<()> {
            lines.push(line!() + 1);
            inner_operation(lines).context("failed during middle operation")?;
            Ok(())
        }
        fn outer_operation(lines: &mut Vec<u32>) -> Result<()> {
            lines.push(line!() + 1);
            middle_operation(lines).context("failed in outer_operation")?;
            Ok(())
        }
        let mut lines = Vec::new();
        let result = outer_operation(&mut lines);
        assert!(result.is_err());
        let error = result.unwrap_err();
        let rendered = format!("{error}");
        let expected = format!(
            "failed in outer_operation (at {}:{})\n  - caused by: failed during middle operation (at {}:{})\n  - caused by: I/O error: inner error (at {}:{})",
            file!(),
            lines[0],
            file!(),
            lines[1],
            file!(),
            lines[2]
        );
        assert_eq!(rendered, expected);
    }

    #[test]
    fn test_error_context_proc_macro() {
        let line = line!();
        #[error_context("top level context")]
        fn level_one() -> Result<()> {
            #[error_context("second level context")]
            fn level_two() -> Result<()> {
                Err(crate::ubiblk_error!(InvalidParameter {
                    description: "original error".to_string(),
                }))
            }
            level_two()
        }
        let result = level_one();
        assert!(result.is_err());
        let error = result.unwrap_err();
        let rendered = format!("{error}");
        let expected = format!(
            "top level context (at {}:{})\n  - caused by: second level context (at {}:{})\n  - caused by: Invalid parameter error: original error (at {}:{})",
            file!(),
            line + 11,
            file!(),
            line + 9,
            file!(),
            line + 5
        );
        assert_eq!(rendered, expected);
    }
}
