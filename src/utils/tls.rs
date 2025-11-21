use std::fs;
use std::io::{self, Error, ErrorKind};
use std::net::TcpStream;
use std::path::Path;
use std::sync::Arc;

use hex::FromHexError;
use openssl::error::ErrorStack;
use openssl::ssl::{
    HandshakeError, SslAcceptor, SslConnector, SslMethod, SslStream, SslVerifyMode, SslVersion,
};

const TLS12_CIPHER_LIST: &str =
    "PSK-CHACHA20-POLY1305-SHA256:PSK-AES256-GCM-SHA384:PSK-AES128-GCM-SHA256";
const TLS13_CIPHER_SUITES: &str = "TLS_AES_256_GCM_SHA384:TLS_AES_128_GCM_SHA256";

pub fn prepare_psk_identity(identity: &str) -> io::Result<Vec<u8>> {
    if identity.is_empty() {
        return Err(Error::new(
            ErrorKind::InvalidInput,
            "PSK identity must not be empty",
        ));
    }
    if identity.as_bytes().contains(&0) {
        return Err(Error::new(
            ErrorKind::InvalidInput,
            "PSK identity may not include NUL bytes",
        ));
    }
    Ok(identity.as_bytes().to_vec())
}

pub fn read_psk_key(path: &Path) -> io::Result<Vec<u8>> {
    let contents = fs::read_to_string(path)?;
    let filtered: String = contents.chars().filter(|c| !c.is_whitespace()).collect();
    if filtered.is_empty() {
        return Err(Error::new(
            ErrorKind::InvalidData,
            "PSK key file does not contain any hexadecimal data",
        ));
    }

    let decoded = decode_hex(&filtered).map_err(|err| {
        Error::new(
            ErrorKind::InvalidData,
            format!("invalid hexadecimal PSK key: {err}"),
        )
    })?;

    if decoded.len() < 32 {
        return Err(Error::new(
            ErrorKind::InvalidData,
            "PSK key must be at least 32 bytes",
        ));
    }

    Ok(decoded)
}

fn decode_hex(input: &str) -> Result<Vec<u8>, FromHexError> {
    // hex::decode already ignores whitespace if we preprocess the string, but
    // we keep this helper to make the intent explicit and to avoid leaking
    // partial results when decoding fails.
    hex::decode(input)
}

pub fn build_psk_acceptor(
    identity: Arc<Vec<u8>>,
    key: Arc<Vec<u8>>,
) -> Result<SslAcceptor, ErrorStack> {
    let mut builder = openssl::ssl::SslAcceptor::mozilla_modern(SslMethod::tls_server())?;
    builder.set_min_proto_version(Some(SslVersion::TLS1_2))?;
    builder.set_max_proto_version(Some(SslVersion::TLS1_3))?;
    builder.set_verify(SslVerifyMode::NONE);
    builder.set_ciphersuites(TLS13_CIPHER_SUITES)?;
    builder.set_cipher_list(TLS12_CIPHER_LIST)?;

    let identity_for_cb = Arc::clone(&identity);
    let key_for_cb = Arc::clone(&key);
    builder.set_psk_server_callback(move |_, provided_identity, psk| {
        if let Some(received) = provided_identity {
            if received == identity_for_cb.as_slice() {
                if key_for_cb.len() > psk.len() {
                    return Err(ErrorStack::get());
                }
                psk[..key_for_cb.len()].copy_from_slice(&key_for_cb);
                return Ok(key_for_cb.len());
            }
        }
        Ok(0)
    });

    Ok(builder.build())
}

pub fn build_psk_connector(
    identity: Arc<Vec<u8>>,
    key: Arc<Vec<u8>>,
) -> Result<SslConnector, ErrorStack> {
    let mut builder = SslConnector::builder(SslMethod::tls_client())?;
    builder.set_min_proto_version(Some(SslVersion::TLS1_2))?;
    builder.set_max_proto_version(Some(SslVersion::TLS1_3))?;
    builder.set_verify(SslVerifyMode::NONE);
    builder.set_ciphersuites(TLS13_CIPHER_SUITES)?;
    builder.set_cipher_list(TLS12_CIPHER_LIST)?;

    let identity_for_cb = Arc::clone(&identity);
    let key_for_cb = Arc::clone(&key);
    builder.set_psk_client_callback(move |_, _, identity_buf, psk_buf| {
        if identity_for_cb.len() + 1 > identity_buf.len() || key_for_cb.len() > psk_buf.len() {
            return Err(ErrorStack::get());
        }
        identity_buf[..identity_for_cb.len()].copy_from_slice(&identity_for_cb);
        identity_buf[identity_for_cb.len()] = 0;
        psk_buf[..key_for_cb.len()].copy_from_slice(&key_for_cb);
        Ok(key_for_cb.len())
    });

    Ok(builder.build())
}

pub fn accept_psk_stream(
    acceptor: &SslAcceptor,
    stream: TcpStream,
) -> io::Result<SslStream<TcpStream>> {
    let mut attempt = acceptor.accept(stream);
    loop {
        match attempt {
            Ok(stream) => return Ok(stream),
            Err(HandshakeError::WouldBlock(mid)) => {
                attempt = mid.handshake();
            }
            Err(err) => return Err(handshake_err_to_io(err)),
        }
    }
}

pub fn connect_psk_stream(
    connector: &SslConnector,
    stream: TcpStream,
) -> io::Result<SslStream<TcpStream>> {
    let mut config = connector.configure()?;
    config.set_use_server_name_indication(false);
    config.set_verify_hostname(false);
    let mut attempt = config.connect("", stream);
    loop {
        match attempt {
            Ok(stream) => return Ok(stream),
            Err(HandshakeError::WouldBlock(mid)) => {
                attempt = mid.handshake();
            }
            Err(err) => return Err(handshake_err_to_io(err)),
        }
    }
}

fn handshake_err_to_io<H>(err: HandshakeError<H>) -> io::Error {
    match err {
        HandshakeError::Failure(mid) => Error::other(mid.into_error()),
        HandshakeError::SetupFailure(err) => Error::other(err),
        HandshakeError::WouldBlock(_) => Error::other("handshake unexpectedly would block"),
    }
}
