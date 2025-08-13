use crate::{
    block_device::{
        bdev_lazy::metadata::{load_metadata, SharedMetadataState},
        BlockDevice, IoChannel, UbiMetadata,
    },
    utils::aligned_buffer::AlignedBuf,
    vhost_backend::SECTOR_SIZE,
    Result, VhostUserBlockError,
};
use log::error;
use std::{cell::RefCell, rc::Rc};

const METADATA_WRITE_ID: usize = 0;
const METADATA_FLUSH_ID: usize = 1;

pub struct MetadataFlusher {
    channel: Box<dyn IoChannel>,
    metadata: Box<UbiMetadata>,
    shared_state: SharedMetadataState,
}

impl MetadataFlusher {
    pub fn new(metadata_dev: &dyn BlockDevice, source_sector_count: u64) -> Result<Self> {
        let mut channel = metadata_dev.create_channel()?;
        let metadata = load_metadata(&mut channel, metadata_dev.sector_count())?;

        // Validate stripe count
        let source_stripe_count = source_sector_count.div_ceil(metadata.stripe_size());
        if source_stripe_count > metadata.stripe_count() {
            return Err(VhostUserBlockError::InvalidParameter {
                description: format!(
                    "Source stripe count {} exceeds metadata stripe count {}",
                    source_stripe_count,
                    metadata.stripe_count()
                ),
            });
        }

        Ok(MetadataFlusher {
            channel,
            shared_state: SharedMetadataState::new(&metadata),
            metadata,
        })
    }

    pub fn shared_state(&self) -> SharedMetadataState {
        self.shared_state.clone()
    }

    pub fn stripe_sector_count(&self) -> u64 {
        1u64 << self.metadata.stripe_sector_count_shift
    }

    pub fn set_stripe_fetched(&mut self, stripe_id: usize) -> Result<()> {
        self.update_header(stripe_id, 0)
    }

    #[allow(dead_code)]
    pub fn set_stripe_written(&mut self, stripe_id: usize) -> Result<()> {
        self.update_header(stripe_id, 1)
    }

    fn update_header(&mut self, stripe_id: usize, bit: u8) -> Result<()> {
        let mask = 1 << bit;

        // Skip if bit already set
        if self.metadata.stripe_headers[stripe_id] & mask != 0 {
            return Ok(());
        }

        // Prepare metadata buffer
        let (sector_index, sector_buf) = self.prepare_metadata_buffer(stripe_id, mask)?;

        // Write and flush
        self.write_metadata(sector_index, sector_buf)?;
        self.flush_metadata()?;

        // Update local state
        self.metadata.stripe_headers[stripe_id] |= mask;
        self.update_shared_state(stripe_id, bit);

        Ok(())
    }

    fn prepare_metadata_buffer(
        &self,
        stripe_id: usize,
        mask: u8,
    ) -> Result<(u64, Rc<RefCell<AlignedBuf>>)> {
        let metadata_size = self.metadata.metadata_size();
        let buf_size = metadata_size.div_ceil(SECTOR_SIZE) * SECTOR_SIZE;
        let mut full_buf = vec![0u8; buf_size];

        self.metadata.write_to_buf(&mut full_buf[..metadata_size]);

        let byte_offset = SECTOR_SIZE + stripe_id;
        full_buf[byte_offset] |= mask;

        let sector_index = byte_offset / SECTOR_SIZE;
        let sector_offset = sector_index * SECTOR_SIZE;
        let mut sector_buf = AlignedBuf::new(SECTOR_SIZE);

        sector_buf
            .as_mut_slice()
            .copy_from_slice(&full_buf[sector_offset..sector_offset + SECTOR_SIZE]);

        Ok((sector_index as u64, Rc::new(RefCell::new(sector_buf))))
    }

    fn write_metadata(
        &mut self,
        sector_index: u64,
        sector_buf: Rc<RefCell<AlignedBuf>>,
    ) -> Result<()> {
        self.channel
            .add_write(sector_index, 1, sector_buf, METADATA_WRITE_ID);
        self.channel.submit()?;
        self.wait_for_completion(METADATA_WRITE_ID, "Metadata write failed")
    }

    fn flush_metadata(&mut self) -> Result<()> {
        self.channel.add_flush(METADATA_FLUSH_ID);
        self.channel.submit()?;
        self.wait_for_completion(METADATA_FLUSH_ID, "Metadata flush failed")
    }

    fn wait_for_completion(&mut self, expected_id: usize, error_msg: &str) -> Result<()> {
        loop {
            for (id, success) in self.channel.poll() {
                if id == expected_id {
                    if !success {
                        error!("{}", error_msg);
                        return Err(VhostUserBlockError::MetadataError {
                            description: error_msg.into(),
                        });
                    }
                    return Ok(());
                }
            }
        }
    }

    fn update_shared_state(&mut self, stripe_id: usize, bit: u8) {
        match bit {
            0 => self.shared_state.set_stripe_fetched(stripe_id),
            1 => self.shared_state.set_stripe_written(stripe_id),
            _ => {} // Handle other bits if needed
        }
    }
}
