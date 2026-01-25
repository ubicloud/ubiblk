use std::io::ErrorKind;

use log::{error, info};

use crate::{
    block_device::{metadata_flags, shared_buffer, wait_for_completion, SharedBuffer},
    UbiblkError,
};

use super::*;

impl StripeServerSession {
    pub fn handle_requests(&mut self) {
        let mut done = false;
        while !done {
            if let Err(e) = self.handle_single_request() {
                match e {
                    UbiblkError::IoError { source, .. } => {
                        let kind = source.kind();
                        if kind == ErrorKind::UnexpectedEof || kind == ErrorKind::ConnectionReset {
                            info!("Connection closed by peer");
                            done = true;
                            continue;
                        } else {
                            error!("I/O error: {}", source);
                            continue;
                        }
                    }
                    _ => {
                        error!("Error handling request: {}", e);
                        continue;
                    }
                }
            }
        }
    }

    pub fn handle_single_request(&mut self) -> Result<()> {
        let mut opcode = [0u8; 1];

        self.stream.read_exact(&mut opcode)?;

        match opcode[0] {
            METADATA_CMD => {
                self.handle_metadata_request()?;
            }
            READ_STRIPE_CMD => {
                let mut stripe_id_bytes = [0u8; 8];
                self.stream.read_exact(&mut stripe_id_bytes)?;

                let stripe_id = u64::from_le_bytes(stripe_id_bytes);

                self.handle_read_stripe_request(stripe_id)?;
            }
            _ => {
                error!("Received unknown opcode: {}", opcode[0]);
                self.stream.write_all(&[STATUS_INVALID_COMMAND])?;
                self.stream.flush()?;
            }
        }

        Ok(())
    }

    fn handle_metadata_request(&mut self) -> Result<()> {
        info!("Handling metadata request");

        let metadata_size = self.metadata.metadata_size();
        let mut metadata_buf = vec![0u8; metadata_size];
        self.metadata.write_to_buf(&mut metadata_buf);

        self.stream.write_all(&[STATUS_OK])?;
        let metadata_size_bytes = (metadata_size as u64).to_le_bytes();
        self.stream.write_all(&metadata_size_bytes)?;
        self.stream.write_all(&metadata_buf)?;

        self.stream.flush()?;

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
        let written = stripe_header & metadata_flags::WRITTEN != 0;
        let has_source = stripe_header & metadata_flags::HAS_SOURCE != 0;
        let fetched = stripe_header & metadata_flags::FETCHED != 0;
        written || (has_source && fetched)
    }

    fn handle_read_stripe_request(&mut self, stripe_id: u64) -> Result<()> {
        info!("Handling read stripe request for stripe_id: {}", stripe_id);
        if stripe_id >= self.metadata.stripe_count() {
            self.stream.write_all(&[STATUS_INVALID_STRIPE])?;
            self.stream.flush()?;
            return Ok(());
        }

        if self.stripe_not_fetched(stripe_id) {
            info!(
                "Stripe {} has not been fetched from source, notifying client",
                stripe_id
            );
            self.stream.write_all(&[STATUS_NOT_FETCHED])?;
            self.stream.flush()?;
            return Ok(());
        }

        if !self.stripe_has_data(stripe_id) {
            info!("Stripe {} cannot be served, notifying client", stripe_id);
            self.stream.write_all(&[STATUS_NO_DATA])?;
            self.stream.flush()?;
            return Ok(());
        }

        let stripe_data = self.read_stripe(stripe_id).inspect_err(|_| {
            if let Err(e) = self.stream.write_all(&[STATUS_SERVER_ERROR]) {
                error!("Failed to notify client of server error: {}", e);
            }
        })?;

        let stripe_len_bytes = self.metadata.stripe_size();

        self.stream.write_all(&[STATUS_OK])?;
        self.stream
            .write_all(&(stripe_len_bytes as u64).to_le_bytes())?;
        self.stream.write_all(stripe_data.borrow().as_slice())?;

        self.stream.flush()?;

        info!("Successfully served stripe_id: {}", stripe_id);

        Ok(())
    }

    fn read_stripe(&mut self, stripe_id: u64) -> Result<SharedBuffer> {
        let stripe_sector_count = self.metadata.stripe_sector_count() as u32;
        let stripe_len_bytes = self.metadata.stripe_size();

        let offset = stripe_id * (stripe_sector_count as u64);

        let buffer = shared_buffer(stripe_len_bytes);
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
}

#[cfg(test)]
mod tests {
    use std::io::{Cursor, Read, Write};
    use std::sync::{Arc, Mutex};

    use crate::block_device::bdev_test::TestBlockDevice;
    use crate::stripe_server::StripeServer;
    use crate::vhost_backend::SECTOR_SIZE;

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
        let server = StripeServer::new(device, metadata);
        let session = server.start_session(Box::new(stream)).unwrap();
        (session, writes)
    }

    #[test]
    fn test_handle_metadata_request() {
        let metadata: Arc<UbiMetadata> = Arc::from(UbiMetadata::new(0, 2, 0));
        let device = Arc::new(TestBlockDevice::new(SECTOR_SIZE as u64));
        let (mut session, writes) = make_session(vec![METADATA_CMD], metadata.clone(), device);

        session.handle_single_request().unwrap();

        let metadata_size = metadata.metadata_size();
        let mut metadata_buf = vec![0u8; metadata_size];
        metadata.write_to_buf(&mut metadata_buf);

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
}
