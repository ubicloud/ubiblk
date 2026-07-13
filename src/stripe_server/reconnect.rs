use std::collections::HashMap;
use std::thread::sleep;
use std::time::Duration;

use log::{info, warn};

use crate::block_device::UbiMetadata;
use crate::config::v2::secrets::ResolvedSecret;
use crate::config::v2::stripe_source::RemoteStripeConfig;
use crate::{Result, UbiblkError};

use super::{connect_to_stripe_server, RemoteStripeProvider, StripeServerClient};

const RECONNECT_INITIAL_BACKOFF: Duration = Duration::from_millis(500);
const RECONNECT_MAX_BACKOFF: Duration = Duration::from_secs(30);
const RECONNECT_MAX_ATTEMPTS: u32 = 10;

/// The stable geometry of the remote device, captured so a reconnect that lands
/// on a server exposing a different image can be rejected instead of silently
/// serving inconsistent data.
#[derive(Clone, Copy, PartialEq, Eq)]
struct MetadataFingerprint {
    stripe_sector_count: u64,
    stripe_count: u64,
}

impl MetadataFingerprint {
    fn of(metadata: &UbiMetadata) -> Self {
        Self {
            stripe_sector_count: metadata.stripe_sector_count(),
            stripe_count: metadata.stripe_count(),
        }
    }
}

/// Wraps a stripe client and transparently reconnects, with exponential
/// backoff, when a fetch fails because the connection dropped.
pub struct ReconnectingStripeClient<P, F>
where
    P: RemoteStripeProvider,
    F: FnMut() -> Result<P>,
{
    client: P,
    reconnect: F,
    expected_metadata: Option<MetadataFingerprint>,
    initial_backoff: Duration,
    max_backoff: Duration,
    max_attempts: u32,
}

impl<P, F> ReconnectingStripeClient<P, F>
where
    P: RemoteStripeProvider,
    F: FnMut() -> Result<P>,
{
    fn new(client: P, reconnect: F) -> Self {
        let expected_metadata = client.get_metadata().map(MetadataFingerprint::of);
        Self {
            client,
            reconnect,
            expected_metadata,
            initial_backoff: RECONNECT_INITIAL_BACKOFF,
            max_backoff: RECONNECT_MAX_BACKOFF,
            max_attempts: RECONNECT_MAX_ATTEMPTS,
        }
    }

    /// Re-establish the connection, retrying immediately once and then waiting
    /// `initial_backoff` and doubling up to `max_backoff` between subsequent
    /// attempts, until one succeeds or `max_attempts` are exhausted.
    fn reconnect_with_backoff(&mut self) -> Result<()> {
        let mut delay = self.initial_backoff;
        let mut last_err = None;
        for attempt in 1..=self.max_attempts {
            if attempt > 1 {
                sleep(delay);
                delay = (delay * 2).min(self.max_backoff);
            }
            match (self.reconnect)() {
                Ok(client) => {
                    self.accept_reconnected_client(client)?;
                    info!("reconnected to stripe server on attempt {attempt}");
                    return Ok(());
                }
                Err(err) => {
                    warn!(
                        "reconnect attempt {attempt}/{} failed: {err}",
                        self.max_attempts
                    );
                    last_err = Some(err);
                }
            }
        }
        Err(last_err.unwrap_or_else(|| {
            crate::ubiblk_error!(ProtocolError {
                description: "failed to reconnect to stripe server".to_string(),
            })
        }))
    }

    /// Install a freshly reconnected client, rejecting it if the server now
    /// exposes a device with different geometry than the one captured at
    /// construction — otherwise the caller's cached stripe metadata (and the
    /// data served from it) would be inconsistent with the new server.
    fn accept_reconnected_client(&mut self, client: P) -> Result<()> {
        if let Some(expected) = self.expected_metadata {
            let actual = client.get_metadata().map(MetadataFingerprint::of);
            if actual != Some(expected) {
                return Err(crate::ubiblk_error!(MetadataError {
                    description: "stripe server metadata changed across reconnect".to_string(),
                }));
            }
        }
        self.client = client;
        Ok(())
    }
}

impl<P, F> RemoteStripeProvider for ReconnectingStripeClient<P, F>
where
    P: RemoteStripeProvider,
    F: FnMut() -> Result<P>,
{
    fn fetch_stripe(&mut self, stripe_idx: u64) -> Result<Vec<u8>> {
        match self.client.fetch_stripe(stripe_idx) {
            Err(err) if is_connection_error(&err) => {
                warn!("stripe fetch failed ({err}); attempting to reconnect");
                self.reconnect_with_backoff()?;
                self.client.fetch_stripe(stripe_idx)
            }
            other => other,
        }
    }

    fn get_metadata(&self) -> Option<&UbiMetadata> {
        self.client.get_metadata()
    }
}

/// A dropped connection surfaces as an I/O error (including a read/write
/// timeout); protocol/data errors are not retried.
fn is_connection_error(err: &UbiblkError) -> bool {
    matches!(err, UbiblkError::IoError { .. })
}

/// Connect to the stripe server, wrapping the client so later fetches reconnect
/// (with backoff) if the connection drops.
pub fn connect_reconnecting_stripe_client(
    config: &RemoteStripeConfig,
    secrets: &HashMap<String, ResolvedSecret>,
) -> Result<ReconnectingStripeClient<StripeServerClient, impl FnMut() -> Result<StripeServerClient>>>
{
    let client = connect_to_stripe_server(config, secrets)?;
    let config = config.clone();
    let secrets = secrets.clone();
    Ok(ReconnectingStripeClient::new(client, move || {
        connect_to_stripe_server(&config, &secrets)
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn io_err() -> UbiblkError {
        crate::ubiblk_error!(IoError {
            source: std::io::Error::new(std::io::ErrorKind::BrokenPipe, "connection dropped"),
        })
    }

    /// Fails its first `fail_first` fetches with an I/O error, then succeeds.
    struct FlakyProvider {
        fail_first: u32,
        fetches: u32,
    }

    impl RemoteStripeProvider for FlakyProvider {
        fn fetch_stripe(&mut self, _stripe_idx: u64) -> Result<Vec<u8>> {
            self.fetches += 1;
            if self.fetches <= self.fail_first {
                Err(io_err())
            } else {
                Ok(vec![1, 2, 3])
            }
        }

        fn get_metadata(&self) -> Option<&UbiMetadata> {
            None
        }
    }

    fn no_wait<P, F>(client: P, reconnect: F, attempts: u32) -> ReconnectingStripeClient<P, F>
    where
        P: RemoteStripeProvider,
        F: FnMut() -> Result<P>,
    {
        let expected_metadata = client.get_metadata().map(MetadataFingerprint::of);
        ReconnectingStripeClient {
            client,
            reconnect,
            expected_metadata,
            initial_backoff: Duration::ZERO,
            max_backoff: Duration::ZERO,
            max_attempts: attempts,
        }
    }

    #[test]
    fn reconnects_after_connection_error_then_succeeds() {
        // First client's fetch fails (connection dropped); reconnect yields a
        // fresh client that succeeds.
        let first = FlakyProvider {
            fail_first: 1,
            fetches: 0,
        };
        let mut client = no_wait(
            first,
            || {
                Ok(FlakyProvider {
                    fail_first: 0,
                    fetches: 0,
                })
            },
            3,
        );

        let data = client
            .fetch_stripe(0)
            .expect("should succeed after reconnect");
        assert_eq!(data, vec![1, 2, 3]);
    }

    #[test]
    fn gives_up_after_max_reconnect_attempts() {
        let first = FlakyProvider {
            fail_first: 1,
            fetches: 0,
        };
        let mut client = no_wait(first, || Err(io_err()), 3);

        let err = client
            .fetch_stripe(0)
            .expect_err("should fail once reconnects are exhausted");
        assert!(matches!(err, UbiblkError::IoError { .. }));
    }

    #[test]
    fn does_not_reconnect_on_data_error() {
        struct DataErrorProvider;
        impl RemoteStripeProvider for DataErrorProvider {
            fn fetch_stripe(&mut self, _stripe_idx: u64) -> Result<Vec<u8>> {
                Err(crate::ubiblk_error!(StripeUnavailableData { stripe: 0 }))
            }
            fn get_metadata(&self) -> Option<&UbiMetadata> {
                None
            }
        }

        let mut client = no_wait(
            DataErrorProvider,
            || -> Result<DataErrorProvider> { panic!("must not reconnect on a data error") },
            3,
        );

        let err = client
            .fetch_stripe(0)
            .expect_err("data error should propagate");
        assert!(matches!(err, UbiblkError::StripeUnavailableData { .. }));
    }

    /// Fails its first fetch with an I/O error, then succeeds; reports a fixed
    /// metadata so a reconnect's geometry can be checked against it.
    struct MetadataProvider {
        metadata: UbiMetadata,
        fail_first: u32,
        fetches: u32,
    }

    impl RemoteStripeProvider for MetadataProvider {
        fn fetch_stripe(&mut self, _stripe_idx: u64) -> Result<Vec<u8>> {
            self.fetches += 1;
            if self.fetches <= self.fail_first {
                Err(io_err())
            } else {
                Ok(vec![1, 2, 3])
            }
        }

        fn get_metadata(&self) -> Option<&UbiMetadata> {
            Some(&self.metadata)
        }
    }

    #[test]
    fn rejects_reconnect_with_changed_metadata() {
        // The initial server exposes a 4-stripe device; the reconnect lands on a
        // server exposing 8 stripes, which must be refused rather than silently
        // serving data inconsistent with the caller's cached metadata.
        let first = MetadataProvider {
            metadata: *UbiMetadata::new(4, 4, 0),
            fail_first: 1,
            fetches: 0,
        };
        let mut client = no_wait(
            first,
            || {
                Ok(MetadataProvider {
                    metadata: *UbiMetadata::new(4, 8, 0),
                    fail_first: 0,
                    fetches: 0,
                })
            },
            3,
        );

        let err = client
            .fetch_stripe(0)
            .expect_err("reconnect to a different device must be rejected");
        assert!(matches!(err, UbiblkError::MetadataError { .. }));
    }
}
