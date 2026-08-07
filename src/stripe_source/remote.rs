use std::collections::HashMap;
use std::thread;

use crossbeam_channel::{unbounded, Receiver, Sender};
use log::{error, info, warn};

use crate::{
    block_device::{metadata_flags, SharedBuffer},
    stripe_server::RemoteStripeProvider,
    Result,
};

use super::StripeSource;

/// Result of a worker fetch: the stripe id and either its bytes or the error.
type FetchOutcome = (usize, Result<Vec<u8>>);

/// A stripe source backed by one or more connections to a remote stripe server.
///
/// Fetching a stripe over a single connection is a synchronous request/response
/// round-trip, so a single connection can only ever have one fetch in flight —
/// which caps throughput at one stripe per round-trip regardless of how many
/// fetches the `StripeFetcher` has queued. To use the available bandwidth we
/// spread requests across a pool of worker threads, each owning its own
/// connection (mirroring how the S3-backed `ArchiveStripeSource` uses a pool of
/// S3 workers). Requests are dispatched to whichever worker is free and
/// completions come back out of order, matched up by stripe id. The workers
/// only produce raw bytes (`SharedBuffer` is `!Send`); the copy into the
/// caller's buffer happens on `poll`. Dropping the source drops `request_tx`,
/// which makes the workers' `recv` return and the threads exit on their own.
pub struct RemoteStripeSource {
    source_sector_count: u64,
    remote_headers: Vec<u8>,
    request_tx: Sender<usize>,
    result_rx: Receiver<FetchOutcome>,
    pending: HashMap<usize, SharedBuffer>,
}

impl RemoteStripeSource {
    /// Build a source from a non-empty pool of pre-connected clients. Each
    /// client becomes a worker thread; more clients means more fetches in
    /// flight and higher aggregate throughput.
    pub fn new(
        clients: Vec<Box<dyn RemoteStripeProvider + Send>>,
        stripe_sector_count: u64,
    ) -> Result<Self> {
        if clients.is_empty() {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: "remote stripe source requires at least one connection".to_string(),
            }));
        }

        let metadata = clients
            .first()
            .and_then(|client| client.get_metadata())
            .ok_or_else(|| {
                crate::ubiblk_error!(MetadataError {
                    description: "metadata not fetched from remote server".to_string(),
                })
            })?;
        let remote_headers = metadata.stripe_headers.clone();

        let remote_stripe_sector_count = metadata.stripe_sector_count();
        if remote_stripe_sector_count != stripe_sector_count {
            return Err(crate::ubiblk_error!(InvalidParameter {
                description: format!(
                    "remote stripe sector count {remote_stripe_sector_count} does not match expected {stripe_sector_count}",
                ),
            }));
        }

        let stripe_count_with_data = remote_headers
            .iter()
            .rposition(|header| {
                header & (metadata_flags::WRITTEN | metadata_flags::HAS_SOURCE) != 0
            })
            .map(|index| index as u64 + 1)
            .unwrap_or(0);

        let source_sector_count = stripe_count_with_data
            .checked_mul(remote_stripe_sector_count)
            .ok_or_else(|| {
                crate::ubiblk_error!(InvalidParameter {
                    description: "remote stripe count too large (overflow)".to_string(),
                })
            })?;

        let connection_count = clients.len();
        let (request_tx, request_rx) = unbounded::<usize>();
        let (result_tx, result_rx) = unbounded::<FetchOutcome>();

        for (i, mut client) in clients.into_iter().enumerate() {
            let rx: Receiver<usize> = request_rx.clone();
            let tx: Sender<FetchOutcome> = result_tx.clone();
            thread::Builder::new()
                .name(format!("remote-fetch-{i}"))
                .spawn(move || {
                    while let Ok(stripe_id) = rx.recv() {
                        let result = client.fetch_stripe(stripe_id as u64);
                        if tx.send((stripe_id, result)).is_err() {
                            break;
                        }
                    }
                })?;
        }

        info!("RemoteStripeSource started with {connection_count} fetch connection(s)");

        Ok(Self {
            source_sector_count,
            remote_headers,
            request_tx,
            result_rx,
            pending: HashMap::new(),
        })
    }

    /// Copy a fetched stripe's bytes into the caller's buffer, zero-filling any
    /// remainder. Returns whether the copy succeeded.
    fn deliver(stripe_id: usize, data: &[u8], buffer: &SharedBuffer) -> bool {
        let mut buf_ref = buffer.borrow_mut();
        let buf = buf_ref.as_mut_slice();

        if data.len() > buf.len() {
            error!(
                "Stripe {} returned {} bytes which exceeds buffer size {}",
                stripe_id,
                data.len(),
                buf.len()
            );
            return false;
        }

        let (dst, rest) = buf.split_at_mut(data.len());
        dst.copy_from_slice(data);
        rest.fill(0);

        if !rest.is_empty() {
            warn!(
                "Stripe {} returned fewer bytes ({}) than buffer capacity ({})",
                stripe_id,
                data.len(),
                buf.len()
            );
        }
        true
    }
}

impl StripeSource for RemoteStripeSource {
    fn request(&mut self, stripe_id: usize, buffer: SharedBuffer) -> Result<()> {
        self.request_tx.send(stripe_id).map_err(|_| {
            crate::ubiblk_error!(IoError {
                source: std::io::Error::other("remote stripe fetch workers are gone"),
            })
        })?;
        self.pending.insert(stripe_id, buffer);
        Ok(())
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        let mut completions = Vec::new();

        while let Ok((stripe_id, result)) = self.result_rx.try_recv() {
            let buffer = match self.pending.remove(&stripe_id) {
                Some(buffer) => buffer,
                None => {
                    error!("Received completion for unknown stripe {stripe_id}");
                    continue;
                }
            };

            let success = match result {
                Ok(data) => Self::deliver(stripe_id, &data, &buffer),
                Err(err) => {
                    error!("Failed to fetch stripe {stripe_id}: {err}");
                    false
                }
            };

            completions.push((stripe_id, success));
        }

        completions
    }

    fn busy(&self) -> bool {
        !self.pending.is_empty()
    }

    fn sector_count(&self) -> u64 {
        self.source_sector_count
    }

    fn has_stripe(&self, stripe_id: usize) -> bool {
        if stripe_id >= self.remote_headers.len() {
            return false;
        }
        let written_on_remote = self.remote_headers[stripe_id] & metadata_flags::WRITTEN != 0;
        let exists_on_remote_base_image =
            self.remote_headers[stripe_id] & metadata_flags::HAS_SOURCE != 0;
        written_on_remote || exists_on_remote_base_image
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        backends::SECTOR_SIZE,
        block_device::{shared_buffer, UbiMetadata},
    };

    const STRIPE_SECTOR_COUNT_SHIFT: u8 = 4;
    const STRIPE_SECTORS: usize = 1 << STRIPE_SECTOR_COUNT_SHIFT;
    const STRIPE_SIZE: usize = STRIPE_SECTORS * SECTOR_SIZE;
    const TOTAL_STRIPES: usize = 16;

    struct MockRemoteStripeProvider {
        metadata: Box<UbiMetadata>,
    }

    impl MockRemoteStripeProvider {
        pub fn new() -> Self {
            let mut metadata = UbiMetadata::new(STRIPE_SECTOR_COUNT_SHIFT, TOTAL_STRIPES, 0);
            metadata.stripe_headers[2] = metadata_flags::WRITTEN;
            metadata.stripe_headers[0] = metadata_flags::HAS_SOURCE;
            Self { metadata }
        }

        pub fn new_with_bad_metadata() -> Self {
            let metadata = UbiMetadata::new(STRIPE_SECTOR_COUNT_SHIFT + 1, TOTAL_STRIPES, 0);
            Self { metadata }
        }
    }

    impl RemoteStripeProvider for MockRemoteStripeProvider {
        fn fetch_stripe(&mut self, stripe_id: u64) -> Result<Vec<u8>> {
            if stripe_id % 2 == 1 {
                return Err(crate::ubiblk_error!(IoError {
                    source: std::io::Error::other("simulated fetch error"),
                }));
            }
            Ok(vec![stripe_id as u8; STRIPE_SIZE])
        }

        fn get_metadata(&self) -> Option<&UbiMetadata> {
            Some(&self.metadata)
        }
    }

    /// Poll until `expected` completions have been collected or we give up.
    fn poll_until(source: &mut RemoteStripeSource, expected: usize) -> Vec<(usize, bool)> {
        let mut completions = Vec::new();
        for _ in 0..1000 {
            completions.extend(source.poll());
            if completions.len() >= expected {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(1));
        }
        completions
    }

    fn prep_with_connections(connections: usize) -> RemoteStripeSource {
        let clients: Vec<Box<dyn RemoteStripeProvider + Send>> = (0..connections)
            .map(|_| {
                Box::new(MockRemoteStripeProvider::new()) as Box<dyn RemoteStripeProvider + Send>
            })
            .collect();
        RemoteStripeSource::new(clients, STRIPE_SECTORS as u64).unwrap()
    }

    fn prep() -> RemoteStripeSource {
        prep_with_connections(1)
    }

    #[test]
    fn test_fetch_good_stripe() {
        let mut source = prep_with_connections(4);
        let buffer_1 = shared_buffer(STRIPE_SIZE);
        let buffer_2 = shared_buffer(STRIPE_SIZE);
        source.request(2, buffer_1.clone()).unwrap();
        source.request(4, buffer_2.clone()).unwrap();
        let completions = poll_until(&mut source, 2);
        assert_eq!(completions.len(), 2);

        for (stripe_id, success) in completions {
            assert!(success);
            let expected_byte = stripe_id as u8;
            let buf_ref = if stripe_id == 2 {
                buffer_1.borrow()
            } else {
                buffer_2.borrow()
            };
            for &byte in buf_ref.as_slice() {
                assert_eq!(byte, expected_byte);
            }
        }
    }

    #[test]
    fn test_fetch_stripe_with_error() {
        let mut source = prep();
        let buffer_1 = shared_buffer(STRIPE_SIZE);
        let buffer_2 = shared_buffer(STRIPE_SIZE);
        source.request(1, buffer_1.clone()).unwrap();
        source.request(3, buffer_2.clone()).unwrap();
        let completions = poll_until(&mut source, 2);
        assert_eq!(completions.len(), 2);
        for (_, success) in completions {
            assert!(!success);
        }
    }

    #[test]
    fn test_invalid_metadata() {
        let clients: Vec<Box<dyn RemoteStripeProvider + Send>> =
            vec![Box::new(MockRemoteStripeProvider::new_with_bad_metadata())];
        let result = RemoteStripeSource::new(clients, STRIPE_SECTORS as u64);
        assert!(result.is_err());
    }

    #[test]
    fn test_no_connections_is_error() {
        let clients: Vec<Box<dyn RemoteStripeProvider + Send>> = Vec::new();
        let result = RemoteStripeSource::new(clients, STRIPE_SECTORS as u64);
        let err = result.err().expect("empty client pool must error");
        assert!(
            err.to_string().contains("at least one connection"),
            "expected a clear 'at least one connection' error, got: {err}"
        );
    }

    #[test]
    fn test_zeroed_buffer_on_short_stripe() {
        let mut source = prep();
        let buffer = shared_buffer(STRIPE_SIZE + 100);
        source.request(2, buffer.clone()).unwrap();
        let completions = poll_until(&mut source, 1);
        assert_eq!(completions.len(), 1);
        assert_eq!(completions[0], (2, true));
        for (i, &byte) in buffer.borrow().as_slice().iter().enumerate() {
            if i < STRIPE_SIZE {
                assert_eq!(byte, 2u8);
            } else {
                assert_eq!(byte, 0u8);
            }
        }
    }

    #[test]
    fn test_has_stripe() {
        let source = prep();
        assert!(source.has_stripe(0));
        assert!(!source.has_stripe(1));
        assert!(source.has_stripe(2));
        assert!(!source.has_stripe(3));
        assert!(!source.has_stripe(202020)); // out of bounds
    }

    #[test]
    fn test_sector_count() {
        let source = prep();
        assert_eq!(source.sector_count(), (STRIPE_SECTORS as u64) * 3);
    }

    #[test]
    fn test_busy() {
        let mut source = prep();
        assert!(!source.busy());
        let buffer = shared_buffer(STRIPE_SIZE);
        source.request(2, buffer).unwrap();
        assert!(source.busy());
        let _ = poll_until(&mut source, 1);
        assert!(!source.busy());
    }

    /// A provider that records how many fetches run at the same instant across
    /// the whole pool, so a test can prove the connections fetch in parallel.
    struct ConcurrencyProvider {
        metadata: Box<UbiMetadata>,
        in_flight: std::sync::Arc<std::sync::atomic::AtomicUsize>,
        max_in_flight: std::sync::Arc<std::sync::atomic::AtomicUsize>,
    }

    impl RemoteStripeProvider for ConcurrencyProvider {
        fn fetch_stripe(&mut self, stripe_id: u64) -> Result<Vec<u8>> {
            use std::sync::atomic::Ordering;
            let now = self.in_flight.fetch_add(1, Ordering::SeqCst) + 1;
            self.max_in_flight.fetch_max(now, Ordering::SeqCst);
            std::thread::sleep(std::time::Duration::from_millis(20));
            self.in_flight.fetch_sub(1, Ordering::SeqCst);
            Ok(vec![stripe_id as u8; STRIPE_SIZE])
        }

        fn get_metadata(&self) -> Option<&UbiMetadata> {
            Some(&self.metadata)
        }
    }

    #[test]
    fn test_fetches_run_concurrently_across_connections() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        use std::sync::Arc;

        let in_flight = Arc::new(AtomicUsize::new(0));
        let max_in_flight = Arc::new(AtomicUsize::new(0));

        const CONNECTIONS: usize = 4;
        let clients: Vec<Box<dyn RemoteStripeProvider + Send>> = (0..CONNECTIONS)
            .map(|_| {
                Box::new(ConcurrencyProvider {
                    metadata: UbiMetadata::new(STRIPE_SECTOR_COUNT_SHIFT, TOTAL_STRIPES, 0),
                    in_flight: Arc::clone(&in_flight),
                    max_in_flight: Arc::clone(&max_in_flight),
                }) as Box<dyn RemoteStripeProvider + Send>
            })
            .collect();
        let mut source = RemoteStripeSource::new(clients, STRIPE_SECTORS as u64).unwrap();

        let requested = 8;
        for stripe_id in 0..requested {
            source
                .request(stripe_id, shared_buffer(STRIPE_SIZE))
                .unwrap();
        }
        let completions = poll_until(&mut source, requested);
        assert_eq!(completions.len(), requested);
        assert!(completions.iter().all(|(_, success)| *success));

        // With a single connection this would be 1; the pool must overlap
        // fetches across its connections.
        assert!(
            max_in_flight.load(Ordering::SeqCst) > 1,
            "expected concurrent fetches across connections, saw max {}",
            max_in_flight.load(Ordering::SeqCst)
        );
    }
}
