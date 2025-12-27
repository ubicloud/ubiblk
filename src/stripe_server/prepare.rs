use std::sync::Arc;

use crate::{
    block_device::{load_metadata, UbiMetadata},
    stripe_server::StripeServer,
    vhost_backend::{build_block_device, Options},
    KeyEncryptionCipher, Result, VhostUserBlockError,
};

pub fn prepare_stripe_server(
    options: &Options,
    kek: KeyEncryptionCipher,
) -> Result<Arc<StripeServer>> {
    let metadata_path =
        options
            .metadata_path
            .as_deref()
            .ok_or_else(|| VhostUserBlockError::InvalidParameter {
                description: "Missing metadata_path in config file".to_string(),
            })?;

    let stripe_device = build_block_device(&options.path, options, kek.clone(), false)?;
    let metadata_device = build_block_device(metadata_path, options, kek, false)?;

    let mut metadata_channel = metadata_device.create_channel()?;
    let metadata = load_metadata(&mut metadata_channel, metadata_device.sector_count())?;
    let metadata: Arc<UbiMetadata> = Arc::from(metadata);

    Ok(Arc::new(StripeServer::new(
        Arc::from(stripe_device),
        metadata,
    )))
}
