use openssl::{
    error::ErrorStack,
    ssl::{Ssl, SslContext, SslContextBuilder, SslMethod, SslOptions, SslStream, SslVerifyMode},
};

use crate::{vhost_backend::Options, KeyEncryptionCipher, Result, UbiblkError};

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

    pub fn from_options(options: &Options, kek: &KeyEncryptionCipher) -> Result<Option<Self>> {
        match (&options.psk_identity, &options.psk_secret) {
            (Some(id), Some(sec)) => {
                Self::validate_identity(id)?;

                let secret = kek.decrypt_psk_secret(sec.clone())?;
                Self::validate_secret(&secret)?;

                Ok(Some(Self {
                    identity: id.clone(),
                    secret,
                }))
            }
            (None, None) => Ok(None),
            _ => Err(UbiblkError::InvalidParameter {
                description: "psk_secret and psk_identity must both be set or both be unset"
                    .to_string(),
            }),
        }
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

    fn make_options(identity: Option<&str>, secret: Option<Vec<u8>>) -> Options {
        Options {
            psk_identity: identity.map(|s| s.to_string()),
            psk_secret: secret,
            ..Default::default()
        }
    }

    fn valid_secret() -> Vec<u8> {
        vec![0xAA; 32]
    }

    #[test]
    fn test_credentials_success_plain() {
        let kek = KeyEncryptionCipher::default(); // Method::None
        let opts = make_options(Some("user"), Some(valid_secret()));

        let creds = PskCredentials::from_options(&opts, &kek)
            .expect("Should parse valid options")
            .expect("Should be Some credentials");

        assert_eq!(creds.identity, "user");
        assert_eq!(creds.secret, valid_secret());
    }

    #[test]
    fn test_credentials_none_when_empty() {
        let kek = KeyEncryptionCipher::default();
        let opts = make_options(None, None);

        let creds = PskCredentials::from_options(&opts, &kek).expect("Should succeed");
        assert!(creds.is_none());
    }

    #[test]
    fn test_error_missing_secret() {
        let kek = KeyEncryptionCipher::default();
        let opts = make_options(Some("user"), None); // Identity but no secret

        let err = PskCredentials::from_options(&opts, &kek).unwrap_err();
        assert!(matches!(err, UbiblkError::InvalidParameter { .. }));
    }

    #[test]
    fn test_error_missing_identity() {
        let kek = KeyEncryptionCipher::default();
        let opts = make_options(None, Some(valid_secret())); // Secret but no identity

        let err = PskCredentials::from_options(&opts, &kek).unwrap_err();
        assert!(matches!(err, UbiblkError::InvalidParameter { .. }));
    }

    #[test]
    fn test_error_empty_identity_string() {
        let kek = KeyEncryptionCipher::default();
        let opts = make_options(Some(""), Some(valid_secret()));

        let err = PskCredentials::from_options(&opts, &kek).unwrap_err();
        // Check description contains "empty"
        if let UbiblkError::InvalidParameter { description } = err {
            assert!(description.contains("empty"));
        } else {
            panic!("Wrong error type");
        }
    }

    #[test]
    fn test_error_secret_too_short() {
        let kek = KeyEncryptionCipher::default();
        let short_secret = vec![0u8; 15]; // 15 bytes < 16 bytes required
        let opts = make_options(Some("user"), Some(short_secret));

        let err = PskCredentials::from_options(&opts, &kek).unwrap_err();
        if let UbiblkError::InvalidParameter { description } = err {
            assert!(description.contains("at least 16 bytes"));
        } else {
            panic!("Wrong error type");
        }
    }
}
