use base64::{engine::general_purpose::STANDARD, Engine};
use openssl::{
    error::ErrorStack,
    ssl::{Ssl, SslContext, SslContextBuilder, SslMethod, SslOptions, SslStream, SslVerifyMode},
};

use crate::{KeyEncryptionCipher, Result, UbiblkError};

use super::DynStream;

const PSK_CIPHER_SUITE: &str = "PSK-AES256-GCM-SHA384";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PskCredentials {
    identity: String,
    secret: Vec<u8>,
}

impl PskCredentials {
    pub fn new(identity: String, secret: Vec<u8>) -> Result<Self> {
        Self::validate_identity(&identity)?;
        Self::validate_secret(&secret)?;
        Ok(Self { identity, secret })
    }

    fn validate_identity(identity: &str) -> Result<()> {
        if identity.is_empty() {
            return Err(UbiblkError::InvalidParameter {
                description: "PSK identity must not be empty".to_string(),
            });
        }
        Ok(())
    }

    fn validate_secret(secret: &[u8]) -> Result<()> {
        if secret.len() < 16 {
            return Err(UbiblkError::InvalidParameter {
                description: "PSK secret must be at least 16 bytes long".to_string(),
            });
        }
        Ok(())
    }
}

/// Parse PSK credentials from optional identity and base64-encoded secret.
/// This is used in command-line tools where the secret is provided as a
/// base64-encoded string.
pub fn parse_psk_credentials(
    identity: Option<String>,
    secret_b64: Option<String>,
    kek: &KeyEncryptionCipher,
) -> Result<Option<PskCredentials>> {
    match (identity, secret_b64) {
        (Some(identity), Some(secret_b64)) => {
            let encrypted_secret =
                STANDARD
                    .decode(secret_b64)
                    .map_err(|e| UbiblkError::InvalidParameter {
                        description: format!("Failed to decode psk_secret: {e}"),
                    })?;
            let decrypted_secret = kek.decrypt_psk_secret(encrypted_secret)?;
            Ok(Some(PskCredentials::new(identity, decrypted_secret)?))
        }
        (None, None) => Ok(None),
        _ => Err(UbiblkError::InvalidParameter {
            description: "psk_secret and psk_identity must both be set or both be unset"
                .to_string(),
        }),
    }
}

pub fn wrap_psk_client_stream(stream: DynStream, creds: &PskCredentials) -> Result<DynStream> {
    let mut builder = build_psk_context()?;
    let identity = creds.identity.clone().into_bytes();
    let secret = creds.secret.clone();

    builder.set_psk_client_callback(move |_, _, identity_buf, psk_buf| {
        if identity.len() >= identity_buf.len() {
            log::error!("PSK identity buffer is too small in client callback.");
            return Err(ErrorStack::get());
        }

        if secret.len() > psk_buf.len() {
            log::error!("PSK secret buffer is too small in client callback.");
            return Err(ErrorStack::get());
        }

        identity_buf[..identity.len()].copy_from_slice(&identity);
        identity_buf[identity.len()] = 0;
        psk_buf[..secret.len()].copy_from_slice(&secret);

        Ok(secret.len())
    });

    let ctx: SslContext = builder.build();
    let ssl = Ssl::new(&ctx).map_err(to_tls_error)?;
    let mut stream = SslStream::new(ssl, stream).map_err(to_tls_error)?;

    stream.connect().map_err(to_tls_error)?;

    Ok(Box::new(stream))
}

pub fn wrap_psk_server_stream(stream: DynStream, creds: &PskCredentials) -> Result<DynStream> {
    let mut builder = build_psk_context()?;
    let identity = creds.identity.clone().into_bytes();
    let secret = creds.secret.clone();

    builder.set_psk_server_callback(move |_, received_identity, psk_buf| {
        if !openssl::memcmp::eq(received_identity.unwrap_or_default(), &identity) {
            return Err(ErrorStack::get());
        }

        if secret.len() > psk_buf.len() {
            return Err(ErrorStack::get());
        }
        psk_buf[..secret.len()].copy_from_slice(&secret);

        Ok(secret.len())
    });

    let ctx: SslContext = builder.build();
    let mut ssl = Ssl::new(&ctx).map_err(to_tls_error)?;
    ssl.set_accept_state();
    let mut stream = SslStream::new(ssl, stream).map_err(to_tls_error)?;
    stream.accept().map_err(to_tls_error)?;

    Ok(Box::new(stream))
}

fn build_psk_context() -> Result<SslContextBuilder> {
    let mut builder = SslContext::builder(SslMethod::tls()).map_err(to_tls_error)?;

    // TODO: Support TLS 1.3 PSK
    builder.set_options(SslOptions::NO_TLSV1_3);
    builder.set_options(SslOptions::NO_TICKET);
    builder
        .set_cipher_list(PSK_CIPHER_SUITE)
        .map_err(to_tls_error)?;
    builder.set_verify(SslVerifyMode::NONE);

    Ok(builder)
}

fn to_tls_error<E: ToString>(err: E) -> UbiblkError {
    UbiblkError::TlsError {
        description: err.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_psk_credentials_success() {
        let kek = KeyEncryptionCipher::default();
        let secret = vec![0xBB; 32];
        let secret_b64 = STANDARD.encode(&secret);
        let creds =
            parse_psk_credentials(Some("test_identity".to_string()), Some(secret_b64), &kek)
                .expect("Should parse PSK credentials")
                .expect("Should be Some credentials");

        assert_eq!(creds.identity, "test_identity");
        assert_eq!(creds.secret, secret);
    }

    #[test]
    fn test_parse_psk_credentials_mismatched_args() {
        let kek = KeyEncryptionCipher::default();

        // Identity, no secret
        let err = parse_psk_credentials(Some("test".to_string()), None, &kek).unwrap_err();
        assert!(matches!(err, UbiblkError::InvalidParameter { .. }));

        // Secret, no identity
        let err = parse_psk_credentials(None, Some("c2VjcmV0".to_string()), &kek).unwrap_err();
        assert!(matches!(err, UbiblkError::InvalidParameter { .. }));
    }

    #[test]
    fn test_parse_psk_credentials_invalid_b64() {
        let kek = KeyEncryptionCipher::default();
        let err = parse_psk_credentials(
            Some("test".to_string()),
            Some("not-base64".to_string()),
            &kek,
        )
        .unwrap_err();

        if let UbiblkError::InvalidParameter { description } = err {
            assert!(description.contains("Failed to decode psk_secret"));
        } else {
            panic!("Wrong error type, got {:?}", err);
        }
    }

    #[test]
    fn test_psk_credentials_empty_identity() {
        let err = PskCredentials::new("".to_string(), vec![0x11; 16]).unwrap_err();
        assert!(matches!(err, UbiblkError::InvalidParameter { .. }));
    }

    #[test]
    fn test_parse_psk_credentials_short_secret() {
        let kek = KeyEncryptionCipher::default();
        let secret = vec![0x11; 8];
        let secret_b64 = STANDARD.encode(&secret);
        let err = parse_psk_credentials(Some("identity".to_string()), Some(secret_b64), &kek)
            .unwrap_err();
        assert!(matches!(err, UbiblkError::InvalidParameter { .. }));
    }
}
