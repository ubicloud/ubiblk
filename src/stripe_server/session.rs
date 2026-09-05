use std::io::ErrorKind;

use log::{error, info};

use crate::{
    block_device::{
        metadata_flags, shared_buffer, wait_for_completion, SharedBuffer, SnapshotRequest,
    },
    UbiblkError,
};

use super::*;

impl StripeServerSession {
    fn stream_mut(&mut self) -> &mut DynStream {
        self.stream
            .as_mut()
            .expect("session stream is taken only when the session ends")
    }

    pub fn handle_requests(&mut self) {
        loop {
            if self.stream.is_none() {
                // The session handed its stream to the snapshot worker.
                return;
            }
            let Err(e) = self.handle_single_request() else {
                continue;
            };
            // The protocol is length-prefixed, so after any error the stream is
            // in an unknown state: a partially read/written message desyncs every
            // subsequent request, and retrying a failing read just busy-loops.
            // Tear the session down so the client reconnects onto a fresh one.
            match &e {
                UbiblkError::IoError { source, .. }
                    if matches!(
                        source.kind(),
                        ErrorKind::UnexpectedEof | ErrorKind::ConnectionReset
                    ) =>
                {
                    info!("Connection closed by peer");
                }
                UbiblkError::IoError { source, .. }
                    if matches!(source.kind(), ErrorKind::WouldBlock | ErrorKind::TimedOut) =>
                {
                    info!("Closing idle connection after read/write timeout");
                }
                _ => error!("Terminating stripe session after error: {e}"),
            }
            return;
        }
    }

    pub fn handle_single_request(&mut self) -> Result<()> {
        let mut opcode = [0u8; 1];

        self.stream_mut().read_exact(&mut opcode)?;

        match opcode[0] {
            HELLO_CMD => {
                self.handle_hello_request()?;
            }
            METADATA_CMD => {
                self.handle_metadata_request()?;
            }
            SUBSCRIBE_SNAPSHOT_CMD => {
                self.handle_subscribe_snapshot()?;
            }
            READ_STRIPE_CMD => {
                let mut stripe_id_bytes = [0u8; 8];
                self.stream_mut().read_exact(&mut stripe_id_bytes)?;

                let stripe_id = u64::from_le_bytes(stripe_id_bytes);

                self.handle_read_stripe_request(stripe_id)?;
            }
            _ => {
                error!("Received unknown opcode: {}", opcode[0]);
                self.stream_mut().write_all(&[STATUS_INVALID_COMMAND])?;
                self.stream_mut().flush()?;
            }
        }

        Ok(())
    }

    /// Hand this session's stream to the snapshot worker as a destination. The
    /// session ends here: from now on the worker owns the stream and writes
    /// push frames on it, and the fork pulls cold stripes on another session.
    fn handle_subscribe_snapshot(&mut self) -> Result<()> {
        let (Some(snapshot_ch), Some(snapshot_state)) =
            (self.snapshot_ch.clone(), self.snapshot_state.clone())
        else {
            info!("Snapshot subscribe refused: this server serves no snapshots");
            return self.reply_status(STATUS_NO_SNAPSHOT);
        };

        if !snapshot_state.snapshot_live() {
            info!("Snapshot subscribe refused: no snapshot is live");
            return self.reply_status(STATUS_NO_SNAPSHOT);
        }
        let generation = snapshot_state.generation();

        self.stream_mut().write_all(&[STATUS_OK])?;
        self.stream_mut().write_all(&generation.to_le_bytes())?;
        let compression = self.negotiate_compression()?;

        let id = self
            .next_destination_id
            .fetch_add(1, std::sync::atomic::Ordering::AcqRel);
        let stream = self.stream.take().expect("stream checked above");
        let mut destination = RemoteDestination::new(id, stream, compression);
        if let Some(socket) = self.socket.take() {
            destination = destination.with_socket(socket);
        }

        if snapshot_ch
            .send(SnapshotRequest::AddDestination {
                destination: Box::new(destination),
                generation,
            })
            .is_err()
        {
            error!("Snapshot worker is gone, dropping subscriber {id}");
            return Ok(());
        }

        info!("Snapshot destination {id} subscribed to generation {generation}");
        Ok(())
    }

    fn handle_hello_request(&mut self) -> Result<()> {
        info!("Handling hello request");
        self.stream_mut().write_all(&[STATUS_OK])?;
        self.stream_mut()
            .write_all(&PROTOCOL_VERSION.to_le_bytes())?;
        self.compression = self.negotiate_compression()?;
        Ok(())
    }

    /// Offer what this server can encode stripes with and take the client's
    /// pick. Written last in a reply the client is already reading, so a client
    /// that rejects the version hangs up rather than deadlocking here.
    fn negotiate_compression(&mut self) -> Result<WireCompression> {
        self.stream_mut()
            .write_all(&[WireCompression::supported_mask()])?;
        self.stream_mut().flush()?;

        let mut chosen = [0u8; 1];
        self.stream_mut().read_exact(&mut chosen)?;
        let compression = WireCompression::from_code(chosen[0])?;
        info!("Session will send stripes as {compression:?}");
        Ok(compression)
    }

    /// The metadata to hand a client: the file's, with the device's live
    /// written bits merged in, so a client learns which stripes actually hold
    /// data instead of what was on disk when this server started.
    fn served_metadata(&self) -> UbiMetadata {
        let mut metadata = (*self.metadata).clone();
        if let Some(live) = self.live_state.as_ref() {
            for (stripe_id, header) in metadata.stripe_headers.iter_mut().enumerate() {
                if live.stripe_written(stripe_id) {
                    *header |= metadata_flags::WRITTEN;
                }
            }
        }
        metadata
    }

    fn stripe_written(&self, stripe_id: u64) -> bool {
        if let Some(live) = self.live_state.as_ref() {
            if live.stripe_written(stripe_id as usize) {
                return true;
            }
        }
        self.metadata.stripe_headers[stripe_id as usize] & metadata_flags::WRITTEN != 0
    }

    fn handle_metadata_request(&mut self) -> Result<()> {
        info!("Handling metadata request");

        let served = self.served_metadata();
        let metadata_size = served.metadata_size();
        let mut metadata_buf = vec![0u8; metadata_size];
        served.write_to_buf(&mut metadata_buf)?;

        self.stream_mut().write_all(&[STATUS_OK])?;
        let metadata_size_bytes = (metadata_size as u64).to_le_bytes();
        self.stream_mut().write_all(&metadata_size_bytes)?;
        self.stream_mut().write_all(&metadata_buf)?;

        self.stream_mut().flush()?;

        info!("Successfully served metadata request");

        Ok(())
    }

    fn stripe_not_fetched(&self, stripe_id: u64) -> bool {
        let stripe_header = self.metadata.stripe_headers[stripe_id as usize];
        let has_source = stripe_header & metadata_flags::HAS_SOURCE != 0;
        let fetched = stripe_header & metadata_flags::FETCHED != 0;
        has_source && !fetched
    }

    fn stripe_has_data(&self, stripe_id: u64) -> bool {
        let stripe_header = self.metadata.stripe_headers[stripe_id as usize];
        let has_source = stripe_header & metadata_flags::HAS_SOURCE != 0;
        let fetched = stripe_header & metadata_flags::FETCHED != 0;
        self.stripe_written(stripe_id) || (has_source && fetched)
    }

    fn handle_read_stripe_request(&mut self, stripe_id: u64) -> Result<()> {
        info!("Handling read stripe request for stripe_id: {}", stripe_id);
        if stripe_id >= self.metadata.stripe_count() {
            return self.reply_status(STATUS_INVALID_STRIPE);
        }

        // While a snapshot is live, a stripe is only safe to serve from the
        // live device until its copy-out runs: after that prod's new content is
        // on disk and the snapshot's version exists only in what was pushed.
        if let Some(state) = self.snapshot_state.as_ref() {
            if state.snapshot_live() && !state.write_allowed_before_copy(stripe_id as usize) {
                info!("Stripe {stripe_id} was already pushed to subscribers");
                return self.reply_status(STATUS_ALREADY_PUSHED);
            }
        }

        let stripe_data = if self.stripe_not_fetched(stripe_id) {
            // Not yet copied into the local device: the data still lives in the
            // source, so serve it straight from there.
            if self.source.is_none() {
                info!("Stripe {} not fetched and no source available", stripe_id);
                return self.reply_status(STATUS_NOT_FETCHED);
            }
            self.read_stripe_from_source(stripe_id)
                .inspect_err(|_| self.notify_server_error())?
        } else if !self.stripe_has_data(stripe_id) {
            info!("Stripe {} cannot be served, notifying client", stripe_id);
            return self.reply_status(STATUS_NO_DATA);
        } else {
            self.read_stripe(stripe_id)
                .inspect_err(|_| self.notify_server_error())?
        };

        // The check above happened before the read; the write it was guarding
        // against can land while the read is in flight, and then this would
        // serve content from after the snapshot. Writes to a locked stripe are
        // held until its copy-out completes, so if the stripe still has not
        // been copied out now, nothing has overwritten it and what was read is
        // the snapshot's. If it has, the copy that was pushed is the good one
        // and this pull must not contradict it.
        if let Some(state) = self.snapshot_state.as_ref() {
            if state.snapshot_live() && !state.write_allowed_before_copy(stripe_id as usize) {
                info!("Stripe {stripe_id} was copied out while being read; deferring to the push");
                return self.reply_status(STATUS_ALREADY_PUSHED);
            }
        }

        let compression = self.compression;
        let stripe = stripe_data.borrow();
        let payload = compression.compress(stripe.as_slice())?;

        self.stream_mut().write_all(&[STATUS_OK])?;
        self.stream_mut()
            .write_all(&(payload.len() as u64).to_le_bytes())?;
        self.stream_mut().write_all(&payload)?;

        self.stream_mut().flush()?;

        info!("Successfully served stripe_id: {}", stripe_id);

        Ok(())
    }

    /// This session's stripe buffer, allocated once and handed out again for
    /// every stripe: a session serves one stripe at a time, so one is enough.
    fn stripe_buffer(&mut self) -> SharedBuffer {
        let stripe_len_bytes = self.metadata.stripe_size();
        self.stripe_buffer
            .get_or_insert_with(|| shared_buffer(stripe_len_bytes))
            .clone()
    }

    fn read_stripe(&mut self, stripe_id: u64) -> Result<SharedBuffer> {
        let stripe_sector_count = self.metadata.stripe_sector_count() as u32;

        let offset = stripe_id * (stripe_sector_count as u64);

        let buffer = self.stripe_buffer();
        self.stripe_channel
            .add_read(offset, stripe_sector_count, buffer.clone(), 0);
        self.stripe_channel.submit()?;
        wait_for_completion(
            self.stripe_channel.as_mut(),
            0,
            std::time::Duration::from_secs(30),
        )?;

        Ok(buffer)
    }

    fn read_stripe_from_source(&mut self, stripe_id: u64) -> Result<SharedBuffer> {
        let buffer = self.stripe_buffer();
        let source = self.source.as_mut().expect("caller checked source exists");
        source.request(stripe_id as usize, buffer.clone())?;
        source.wait_for_stripe(stripe_id as usize, std::time::Duration::from_secs(30))?;
        Ok(buffer)
    }

    /// Reply with a single status byte and no payload.
    fn reply_status(&mut self, status: u8) -> Result<()> {
        self.stream_mut().write_all(&[status])?;
        self.stream_mut().flush()?;
        Ok(())
    }

    fn notify_server_error(&mut self) {
        if let Err(e) = self.stream_mut().write_all(&[STATUS_SERVER_ERROR]) {
            error!("Failed to notify client of server error: {}", e);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::io::{Cursor, Read, Write};
    use std::sync::{Arc, Mutex};

    use crate::backends::SECTOR_SIZE;
    use crate::block_device::bdev_test::TestBlockDevice;
    use crate::stripe_server::StripeServer;

    use super::*;

    struct TestStream {
        read: Cursor<Vec<u8>>,
        writes: Arc<Mutex<Vec<u8>>>,
    }

    impl Read for TestStream {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            self.read.read(buf)
        }
    }

    impl Write for TestStream {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            self.writes.lock().unwrap().extend_from_slice(buf);
            Ok(buf.len())
        }

        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    fn make_session(
        input: Vec<u8>,
        metadata: Arc<UbiMetadata>,
        device: Arc<TestBlockDevice>,
    ) -> (StripeServerSession, Arc<Mutex<Vec<u8>>>) {
        let writes = Arc::new(Mutex::new(Vec::new()));
        let stream = TestStream {
            read: Cursor::new(input),
            writes: writes.clone(),
        };
        let server = StripeServer::new(device, metadata, None);
        let session = server.start_session(Box::new(stream)).unwrap();
        (session, writes)
    }

    #[test]
    fn test_handle_hello_request() {
        let metadata: Arc<UbiMetadata> = Arc::from(UbiMetadata::new(0, 1, 0));
        let device = Arc::new(TestBlockDevice::new(SECTOR_SIZE as u64));
        // The client answers the compression offer with its pick.
        let (mut session, writes) = make_session(
            vec![HELLO_CMD, WireCompression::Zstd.code()],
            metadata,
            device,
        );

        session.handle_single_request().unwrap();

        let mut expected = vec![STATUS_OK];
        expected.extend_from_slice(&PROTOCOL_VERSION.to_le_bytes());
        expected.push(WireCompression::supported_mask());
        assert_eq!(*writes.lock().unwrap(), expected);
        assert_eq!(session.compression, WireCompression::Zstd);
    }

    #[test]
    fn test_handle_metadata_request() {
        let metadata: Arc<UbiMetadata> = Arc::from(UbiMetadata::new(0, 2, 0));
        let device = Arc::new(TestBlockDevice::new(SECTOR_SIZE as u64));
        let (mut session, writes) = make_session(vec![METADATA_CMD], metadata.clone(), device);

        session.handle_single_request().unwrap();

        let metadata_size = metadata.metadata_size();
        let mut metadata_buf = vec![0u8; metadata_size];
        metadata
            .write_to_buf(&mut metadata_buf)
            .expect("write to buffer");

        let mut expected = vec![STATUS_OK];
        expected.extend_from_slice(&(metadata_size as u64).to_le_bytes());
        expected.extend_from_slice(&metadata_buf);

        assert_eq!(*writes.lock().unwrap(), expected);
    }

    #[test]
    fn test_handle_read_stripe_invalid_stripe() {
        let metadata: Arc<UbiMetadata> = Arc::from(UbiMetadata::new(0, 1, 0));
        let device = Arc::new(TestBlockDevice::new(SECTOR_SIZE as u64));
        let mut input = vec![READ_STRIPE_CMD];
        input.extend_from_slice(&1u64.to_le_bytes());
        let (mut session, writes) = make_session(input, metadata, device);

        session.handle_single_request().unwrap();

        assert_eq!(*writes.lock().unwrap(), vec![STATUS_INVALID_STRIPE]);
    }

    #[test]
    fn test_handle_read_stripe_no_data() {
        let metadata: Arc<UbiMetadata> = Arc::from(UbiMetadata::new(0, 1, 0));
        let device = Arc::new(TestBlockDevice::new(SECTOR_SIZE as u64));
        let mut input = vec![READ_STRIPE_CMD];
        input.extend_from_slice(&0u64.to_le_bytes());
        let (mut session, writes) = make_session(input, metadata, device);

        session.handle_single_request().unwrap();

        assert_eq!(*writes.lock().unwrap(), vec![STATUS_NO_DATA]);
    }

    #[test]
    fn test_handle_read_stripe_ok() {
        let mut metadata = UbiMetadata::new(0, 1, 0);
        metadata.set_stripe_header(0, metadata_flags::WRITTEN);
        let metadata: Arc<UbiMetadata> = Arc::from(metadata);

        let device = Arc::new(TestBlockDevice::new(SECTOR_SIZE as u64));
        let stripe_size = metadata.stripe_size();
        let pattern = vec![0x5Au8; stripe_size];
        device.write(0, &pattern, stripe_size);

        let mut input = vec![READ_STRIPE_CMD];
        input.extend_from_slice(&0u64.to_le_bytes());
        let (mut session, writes) = make_session(input, metadata, device);

        session.handle_single_request().unwrap();

        let mut expected = vec![STATUS_OK];
        expected.extend_from_slice(&(stripe_size as u64).to_le_bytes());
        expected.extend_from_slice(&pattern);

        assert_eq!(*writes.lock().unwrap(), expected);
    }

    #[test]
    fn test_handle_read_stripe_server_error() {
        let mut metadata = UbiMetadata::new(0, 1, 0);
        metadata.set_stripe_header(0, metadata_flags::WRITTEN);
        let metadata: Arc<UbiMetadata> = Arc::from(metadata);

        let device = Arc::new(TestBlockDevice::new(SECTOR_SIZE as u64));
        device
            .fail_next
            .store(true, std::sync::atomic::Ordering::SeqCst);

        let mut input = vec![READ_STRIPE_CMD];
        input.extend_from_slice(&0u64.to_le_bytes());
        let (mut session, writes) = make_session(input, metadata, device);

        assert!(session.handle_single_request().is_err());

        assert_eq!(*writes.lock().unwrap(), vec![STATUS_SERVER_ERROR]);
    }

    #[test]
    fn test_handle_unknown_opcode() {
        let metadata: Arc<UbiMetadata> = Arc::from(UbiMetadata::new(0, 1, 0));
        let device = Arc::new(TestBlockDevice::new(SECTOR_SIZE as u64));
        let (mut session, writes) = make_session(vec![0xAA], metadata, device);

        session.handle_single_request().unwrap();

        assert_eq!(*writes.lock().unwrap(), vec![STATUS_INVALID_COMMAND]);
    }

    /// A stream whose reads always fail with a non-EOF error, to prove
    /// `handle_requests` tears the session down instead of spinning forever.
    struct AlwaysErrorStream;

    impl Read for AlwaysErrorStream {
        fn read(&mut self, _buf: &mut [u8]) -> std::io::Result<usize> {
            Err(std::io::Error::other("persistent read error"))
        }
    }

    impl Write for AlwaysErrorStream {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            Ok(buf.len())
        }

        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    #[test]
    fn handle_requests_terminates_on_persistent_error() {
        let metadata: Arc<UbiMetadata> = Arc::from(UbiMetadata::new(0, 1, 0));
        let device = Arc::new(TestBlockDevice::new(SECTOR_SIZE as u64));
        let server = StripeServer::new(device, metadata, None);
        let mut session = server.start_session(Box::new(AlwaysErrorStream)).unwrap();

        // Returns rather than looping on the broken stream (would hang otherwise).
        session.handle_requests();
    }
}
