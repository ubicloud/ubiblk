use std::sync::Arc;

use crate::{
    block_device::{load_metadata, UbiMetadata, STRIPE_WRITTEN_MASK},
    stripe_server::StripeServer,
    vhost_backend::{build_block_device, Options},
    KeyEncryptionCipher, Result,
};

pub fn prepare_stripe_server(
    options: &Options,
    kek: KeyEncryptionCipher,
) -> Result<Arc<StripeServer>> {
    let stripe_device = build_block_device(&options.path, options, kek.clone(), false)?;
    let metadata: Arc<UbiMetadata> = if let Some(metadata_path) = options.metadata_path.as_deref() {
        let metadata_device = build_block_device(metadata_path, options, kek, false)?;

        let mut metadata_channel = metadata_device.create_channel()?;
        let metadata = load_metadata(&mut metadata_channel, metadata_device.sector_count())?;
        Arc::from(metadata)
    } else {
        let sector_count = stripe_device.sector_count();
        let stripe_sector_count_shift = if sector_count > 0 {
            sector_count.ilog2() as u8
        } else {
            0
        };
        let stripe_sector_count = 1u64 << stripe_sector_count_shift;
        let stripe_count = sector_count.div_ceil(stripe_sector_count) as usize;
        let mut metadata = UbiMetadata::new(stripe_sector_count_shift, stripe_count, stripe_count);
        for stripe_header in metadata.stripe_headers.iter_mut() {
            *stripe_header |= STRIPE_WRITTEN_MASK;
        }
        Arc::from(metadata)
    };

    Ok(Arc::new(StripeServer::new(
        Arc::from(stripe_device),
        metadata,
    )))
}
