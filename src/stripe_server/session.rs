use std::{cell::RefCell, io::ErrorKind, rc::Rc};

use log::{error, info};

use crate::{
    block_device::{wait_for_completion, SharedBuffer, STRIPE_WRITTEN_MASK},
    utils::AlignedBuf,
    vhost_backend::SECTOR_SIZE,
    VhostUserBlockError,
};

use super::*;

impl StripeServerSession {
    pub fn handle_requests(&mut self) {
        let mut done = false;
        while !done {
            if let Err(e) = self.handle_single_request() {
                match e {
                    VhostUserBlockError::IoError { source } => {
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
                return Err(VhostUserBlockError::InvalidParameter {
                    description: format!("Unknown opcode: {}", opcode[0]),
                });
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

    fn handle_read_stripe_request(&mut self, stripe_id: u64) -> Result<()> {
        info!("Handling read stripe request for stripe_id: {}", stripe_id);
        if stripe_id >= self.metadata.stripe_count() {
            self.stream.write_all(&[STATUS_INVALID_STRIPE])?;
            self.stream.flush()?;
            return Ok(());
        }

        let stripe_header = self.metadata.stripe_headers[stripe_id as usize];
        if stripe_header & STRIPE_WRITTEN_MASK == 0 {
            info!("Stripe {} is not written, notifying client", stripe_id);
            self.stream.write_all(&[STATUS_UNWRITTEN])?;
            self.stream.flush()?;
            return Ok(());
        }

        let stripe_data = self.read_stripe(stripe_id).inspect_err(|_| {
            if let Err(e) = self.stream.write_all(&[STATUS_SERVER_ERROR]) {
                error!("Failed to notify client of server error: {}", e);
            }
        })?;

        let stripe_sector_count = self.metadata.stripe_size() as u32;
        let stripe_len_bytes = (stripe_sector_count as usize) * SECTOR_SIZE;

        self.stream.write_all(&[STATUS_OK])?;
        self.stream
            .write_all(&(stripe_len_bytes as u64).to_le_bytes())?;
        self.stream.write_all(stripe_data.borrow().as_slice())?;

        self.stream.flush()?;

        info!("Successfully served stripe_id: {}", stripe_id);

        Ok(())
    }

    fn read_stripe(&mut self, stripe_id: u64) -> Result<SharedBuffer> {
        let stripe_sector_count = self.metadata.stripe_size() as u32;
        let stripe_len_bytes = (stripe_sector_count as usize) * SECTOR_SIZE;

        let offset = stripe_id * (stripe_sector_count as u64);

        let buffer = Rc::new(RefCell::new(AlignedBuf::new(stripe_len_bytes)));
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
