//! Nonpersistent spill storage owned by a single serving channel.
mod channel;

use super::{BlockDevice, IoChannel};
use crate::{
    archive::ArchiveStore,
    config::v2::{secrets::ResolvedSecret, stripe_source::ArchiveStorageConfig},
    stripe_source::StripeSourceBuilder,
    Result,
};
use std::{
    collections::HashMap,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
    time::Duration,
};

pub(crate) use channel::SpillIoChannel;

#[derive(Clone, Copy)]
pub struct Geometry {
    pub stripe_sectors: u64,
    pub device_sectors: u64,
    pub slots: usize,
}

impl Geometry {
    pub fn new(stripe_sectors: u64, device_sectors: u64, local_sectors: u64) -> Result<Self> {
        if !stripe_sectors.is_power_of_two()
            || !(64..=65536).contains(&stripe_sectors)
            || device_sectors == 0
        {
            return Err(invalid("invalid spill stripe geometry"));
        }
        let slots = local_sectors / stripe_sectors;
        if slots == 0 || slots * stripe_sectors >= device_sectors {
            return Err(invalid(
                "spill requires at least one slot and a local pool smaller than the device",
            ));
        }
        let stripes = device_sectors.div_ceil(stripe_sectors);
        // Bound all per-stripe state before allocating it, not just the slot array.
        if stripes > (256 * 1024 * 1024 / std::mem::size_of::<channel::Stripe>()) as u64 {
            return Err(invalid("spill stripe metadata would exceed 256 MiB"));
        }
        Ok(Self {
            stripe_sectors,
            device_sectors,
            slots: slots as usize,
        })
    }
    fn stripes(self) -> usize {
        self.device_sectors.div_ceil(self.stripe_sectors) as usize
    }
    fn bytes(self) -> usize {
        self.stripe_sectors as usize * 512
    }
}

pub(super) fn invalid(message: &str) -> crate::UbiblkError {
    crate::ubiblk_error!(InvalidParameter {
        description: message.to_string()
    })
}

/// Clones share only a one-time channel claim. No runtime state is shared.
pub struct SpillBlockDevice {
    base: Box<dyn BlockDevice>,
    geometry: Geometry,
    store: ArchiveStorageConfig,
    secrets: HashMap<String, ResolvedSecret>,
    claimed: Arc<AtomicBool>,
}

impl SpillBlockDevice {
    pub fn new(
        base: Box<dyn BlockDevice>,
        geometry: Geometry,
        store: ArchiveStorageConfig,
        secrets: HashMap<String, ResolvedSecret>,
    ) -> Box<Self> {
        Box::new(Self {
            base,
            geometry,
            store,
            secrets,
            claimed: Arc::new(AtomicBool::new(false)),
        })
    }
}

impl BlockDevice for SpillBlockDevice {
    fn sector_count(&self) -> u64 {
        self.geometry.device_sectors
    }
    fn clone(&self) -> Box<dyn BlockDevice> {
        Box::new(Self {
            base: self.base.clone(),
            geometry: self.geometry,
            store: self.store.clone(),
            secrets: self.secrets.clone(),
            claimed: self.claimed.clone(),
        })
    }
    fn create_channel(&self) -> Result<Box<dyn IoChannel>> {
        if self.claimed.swap(true, Ordering::AcqRel) {
            return Err(invalid(
                "spill permits only one serving channel, including device clones",
            ));
        }
        let result = (|| {
            let store: Box<dyn ArchiveStore + Send> =
                StripeSourceBuilder::build_archive_store(&self.store, &self.secrets)?;
            let mut run = [0u8; 16];
            openssl::rand::rand_bytes(&mut run)
                .map_err(|_| invalid("cannot generate spill run identity"))?;
            let run = run
                .iter()
                .map(|byte| format!("{byte:02x}"))
                .collect::<String>();
            let timeout = match &self.store {
                ArchiveStorageConfig::S3 {
                    operation_attempt_timeout_ms,
                    connect_timeout_ms,
                    max_attempts,
                    ..
                } => Duration::from_millis(
                    operation_attempt_timeout_ms
                        .saturating_add(*connect_timeout_ms)
                        .saturating_mul(u64::from(*max_attempts))
                        .max(1),
                ),
                _ => Duration::from_secs(30),
            };
            Ok(Box::new(SpillIoChannel::new(
                self.base.create_channel()?,
                store,
                self.geometry,
                run,
                timeout,
            )) as Box<dyn IoChannel>)
        })();
        if result.is_err() {
            self.claimed.store(false, Ordering::Release);
        }
        result
    }
}
