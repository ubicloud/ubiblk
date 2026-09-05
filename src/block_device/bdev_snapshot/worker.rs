use std::{
    sync::mpsc::{Receiver, RecvTimeoutError, TryRecvError},
    time::Duration,
};

use log::{debug, error, info, warn};

use crate::{
    block_device::{shared_buffer, wait_for_completion, BlockDevice, IoChannel},
    Result,
};

use super::{
    destination::{DestinationId, SnapshotDestination},
    state::SharedSnapshotState,
};

/// How long a single stripe read from the device below may take before the
/// copy-out is treated as failed.
const READ_TIMEOUT: Duration = Duration::from_secs(30);

/// The most destinations one snapshot may serve at a time.
pub const MAX_DESTINATIONS: usize = 8;

/// How long a fresh snapshot waits for its first subscriber before giving up.
///
/// A copy-out with nowhere to send has to either lose the stripe or hold the
/// write. Holding it briefly is what makes "snapshot, then start the fork" work
/// at all: prod would otherwise overwrite the snapshot in the seconds it takes
/// the fork to come up.
const SUBSCRIBER_GRACE: Duration = Duration::from_secs(60);

/// How often the worker wakes up with no request to serve, while a snapshot has
/// something to look after: a fork that may have died, or a stripe held for a
/// subscriber that may never come.
///
/// A fork that dies while prod is not writing is otherwise never noticed. Only
/// a copy-out asks whether a destination is still alive, and with nothing being
/// written no copy-out runs, so the snapshot stays live for as long as prod
/// stays quiet.
const IDLE_WAKEUP: Duration = Duration::from_secs(1);

pub enum SnapshotRequest {
    /// A write is waiting on this stripe, or a destination asked for it.
    CopyOut {
        stripe_id: usize,
    },
    /// A fork attaching to the snapshot it was told about. The generation says
    /// which snapshot it is reading, so two forks taken at different moments
    /// can be served at the same time.
    AddDestination {
        destination: Box<dyn SnapshotDestination>,
        generation: u64,
    },
    RemoveDestination(DestinationId),
    /// Freeze: lock every stripe and start serving the snapshot.
    Freeze,
    Shutdown,
}

/// Owns the snapshot destinations and does the copy-out reads.
///
/// It runs on its own thread so a slow or wedged destination costs the I/O
/// path nothing beyond the stripes it is actually holding.
/// A fork attached to a snapshot, and what it still has to be given.
///
/// Forks overlap: one taken at generation 3 and another at generation 5 can be
/// catching up at the same time. They are tracked separately because the live
/// device only holds a stripe's content until the first copy-out — after that
/// the older fork has its copy and must not be handed the newer content.
struct Subscriber {
    destination: Box<dyn SnapshotDestination>,
    generation: u64,
    /// Stripes this fork has not been given yet.
    needs: Vec<bool>,
}

impl Subscriber {
    fn needs(&self, stripe_id: usize) -> bool {
        self.needs.get(stripe_id).copied().unwrap_or(false)
    }
}

pub struct SnapshotWorker {
    read_channel: Box<dyn IoChannel>,
    state: SharedSnapshotState,
    destinations: Vec<Subscriber>,
    requests: Receiver<SnapshotRequest>,
    next_request_id: usize,
    /// Stripes whose copy-out is waiting for the first subscriber. The writes
    /// that triggered them are blocked until then.
    deferred: Vec<usize>,
    subscriber_grace: Duration,
    done: bool,
}

impl SnapshotWorker {
    pub fn new(
        source_dev: &dyn BlockDevice,
        state: SharedSnapshotState,
        requests: Receiver<SnapshotRequest>,
    ) -> Result<Self> {
        Ok(Self {
            read_channel: source_dev.create_channel()?,
            state,
            destinations: Vec::new(),
            requests,
            next_request_id: 0,
            deferred: Vec::new(),
            subscriber_grace: SUBSCRIBER_GRACE,
            done: false,
        })
    }

    pub fn destination_count(&self) -> usize {
        self.destinations.len()
    }

    /// How long a fresh snapshot holds writes waiting for its first subscriber.
    pub fn set_subscriber_grace(&mut self, grace: Duration) {
        self.subscriber_grace = grace;
    }

    #[cfg(test)]
    pub fn deferred_stripes(&self) -> &[usize] {
        &self.deferred
    }

    fn add_destination(&mut self, destination: Box<dyn SnapshotDestination>, generation: u64) {
        if self.destinations.len() >= MAX_DESTINATIONS {
            warn!(
                "Refusing snapshot destination {}: already serving {} destinations",
                destination.id(),
                MAX_DESTINATIONS
            );
            return;
        }
        info!(
            "Snapshot destination {} added for generation {generation}",
            destination.id()
        );
        // It has none of the snapshot yet, so it needs every stripe. What it can
        // read straight from prod it will pull; the rest arrives by push.
        self.destinations.push(Subscriber {
            destination,
            generation,
            needs: vec![true; self.state.stripe_count()],
        });
        self.publish_destination_count();
        self.run_deferred_copy_outs();
    }

    /// True once the newest snapshot has a fork attached. Until then a copy-out
    /// has nowhere to send that snapshot's content, so writes wait.
    fn latest_generation_subscribed(&self) -> bool {
        let latest = self.state.generation();
        self.destinations
            .iter()
            .any(|subscriber| subscriber.generation == latest)
    }

    /// Copy out the stripes that were waiting for someone to send them to.
    fn run_deferred_copy_outs(&mut self) {
        for stripe_id in std::mem::take(&mut self.deferred) {
            self.copy_out(stripe_id);
        }
    }

    /// Give up on a snapshot nobody ever subscribed to, releasing the writes it
    /// was holding.
    pub fn expire_grace_if_needed(&mut self) {
        if self.deferred.is_empty() || !self.destinations.is_empty() {
            return;
        }
        let Some(since_frozen) = self.state.since_frozen() else {
            return;
        };
        if since_frozen < self.subscriber_grace {
            return;
        }

        warn!(
            "No snapshot subscriber after {}s; ending the snapshot and releasing {} held stripes",
            self.subscriber_grace.as_secs(),
            self.deferred.len()
        );
        self.deferred.clear();
        self.state.end_snapshot();
    }

    fn publish_destination_count(&self) {
        self.state.set_destination_count(self.destinations.len());
    }

    fn remove_destination(&mut self, id: DestinationId) {
        self.destinations
            .retain(|subscriber| subscriber.destination.id() != id);
        self.publish_destination_count();
        self.end_snapshot_if_unwatched();
    }

    /// With no destination left there is nothing to protect, so every stripe
    /// goes back to Free and prod stops paying for the snapshot.
    fn end_snapshot_if_unwatched(&mut self) {
        if self.destinations.is_empty() && self.state.snapshot_live() {
            // End it properly rather than only releasing the stripes: with the
            // generation still set, the server would keep answering pulls from
            // the live device, and a fork still attached would silently read
            // post-snapshot content instead of being told the snapshot is gone.
            info!("Last snapshot destination is gone, ending the snapshot");
            self.state.end_snapshot();
        }
    }

    /// A destination that wants the whole snapshot — an exporter writing it to
    /// an archive, rather than a fork pulling what it needs — gets every stripe
    /// copied out, not just the ones prod overwrites.
    ///
    /// The sweep runs inline after the freeze, one stripe at a time, so it
    /// interleaves with the copy-outs that prod writes are waiting on rather
    /// than blocking them behind a full pass over the device.
    fn sweep_for_exporters(&mut self) {
        if !self
            .destinations
            .iter()
            .any(|subscriber| subscriber.destination.wants_all_stripes())
        {
            return;
        }

        info!("Sweeping every stripe for a snapshot exporter");
        for stripe_id in 0..self.state.stripe_count() {
            self.receive_requests(false);
            if self.done || self.destinations.is_empty() {
                return;
            }
            self.copy_out(stripe_id);
        }

        for subscriber in self.destinations.iter_mut() {
            subscriber.destination.finish();
        }
    }

    fn read_stripe(&mut self, stripe_id: usize) -> Result<Vec<u8>> {
        let sector_count = self.state.stripe_sector_count();
        let len = sector_count as usize * crate::backends::SECTOR_SIZE;
        let buf = shared_buffer(len);
        let id = self.next_request_id;
        self.next_request_id = self.next_request_id.wrapping_add(1);

        let sector_offset = stripe_id as u64 * sector_count;
        self.read_channel
            .add_read(sector_offset, sector_count as u32, buf.clone(), id);
        self.read_channel.submit()?;
        wait_for_completion(self.read_channel.as_mut(), id, READ_TIMEOUT)?;

        let data = buf.borrow().as_slice()[..len].to_vec();
        Ok(data)
    }

    /// Forget forks that have gone away. Done before every copy-out so a dead
    /// fork is dropped even when it is not the one holding a stripe up, and on
    /// every idle wakeup so one is dropped even when nothing is written.
    fn prune_dead_destinations(&mut self) {
        let before = self.destinations.len();
        self.destinations
            .retain(|subscriber| subscriber.destination.is_alive());
        if self.destinations.len() != before {
            info!(
                "Dropped {} snapshot destination(s) that went away",
                before - self.destinations.len()
            );
            self.publish_destination_count();
            self.end_snapshot_if_unwatched();
        }
    }

    /// Read the pre-write content of a stripe and hand it to every live
    /// destination. Destinations that fail are dropped, never retried: prod
    /// writes are waiting on this.
    fn copy_out(&mut self, stripe_id: usize) {
        self.prune_dead_destinations();

        if !self.state.begin_copy(stripe_id) {
            // Someone else already copied this stripe out, or it was never
            // locked in the first place.
            return;
        }

        // Only the forks that have not been given this stripe get it. A fork
        // taken before the last write already holds its own version.
        let waiting: Vec<usize> = self
            .destinations
            .iter()
            .enumerate()
            .filter(|(_, subscriber)| subscriber.needs(stripe_id))
            .map(|(index, _)| index)
            .collect();

        if waiting.is_empty() {
            if self.state.snapshot_live()
                && !self.latest_generation_subscribed()
                && self
                    .state
                    .since_frozen()
                    .is_some_and(|since_frozen| since_frozen < self.subscriber_grace)
            {
                // The newest fork is still coming up. Put the stripe back and
                // leave the write waiting rather than losing the only copy.
                debug!("Deferring copy-out of stripe {stripe_id} until a fork subscribes");
                self.state.defer_copy(stripe_id);
                self.deferred.push(stripe_id);
                return;
            }

            if self.state.snapshot_live() && !self.latest_generation_subscribed() {
                warn!("Snapshot has no subscriber and the grace period is over; ending it");
                self.state.finish_copy(stripe_id);
                self.state.end_snapshot();
                return;
            }

            // Everyone who needs this stripe already has it.
            self.state.finish_copy(stripe_id);
            return;
        }

        let data = match self.read_stripe(stripe_id) {
            Ok(data) => data,
            Err(e) => {
                // The write cannot be held forever on a read that will not
                // succeed. Release the stripe and let prod carry on; the
                // destination will see a short read rather than a hang.
                error!("Failed to read stripe {stripe_id} for snapshot: {e}");
                self.state.finish_copy(stripe_id);
                return;
            }
        };

        let mut failed = Vec::new();
        for index in waiting {
            let subscriber = &mut self.destinations[index];
            if let Err(e) = subscriber.destination.offer(stripe_id, &data) {
                warn!(
                    "Snapshot destination {} failed on stripe {stripe_id}: {e}",
                    subscriber.destination.id()
                );
                failed.push(subscriber.destination.id());
                continue;
            }
            subscriber.needs[stripe_id] = false;
        }

        for id in failed {
            info!("Dropping snapshot destination {id}");
            self.destinations
                .retain(|subscriber| subscriber.destination.id() != id);
        }
        self.publish_destination_count();

        self.state.finish_copy(stripe_id);
        self.end_snapshot_if_unwatched();
    }

    pub fn process_request(&mut self, request: SnapshotRequest) {
        match request {
            SnapshotRequest::CopyOut { stripe_id } => self.copy_out(stripe_id),
            SnapshotRequest::AddDestination {
                destination,
                generation,
            } => self.add_destination(destination, generation),
            SnapshotRequest::RemoveDestination(id) => self.remove_destination(id),
            SnapshotRequest::Freeze => {
                let generation = self.state.lock_all();
                info!("Snapshot generation {generation} frozen");
                self.sweep_for_exporters();
            }
            SnapshotRequest::Shutdown => {
                info!("Snapshot worker shutting down");
                self.done = true;
            }
        }
    }

    pub fn receive_requests(&mut self, block: bool) {
        if block {
            // With a fork attached or stripes held for one, wake up regularly
            // so a dead fork is dropped and the grace period can expire even if
            // no request arrives. With neither there is nothing to look after.
            let idle = self.destinations.is_empty() && self.deferred.is_empty();
            let blocking_recv = if idle {
                self.requests.recv().map_err(RecvTimeoutError::from)
            } else {
                self.requests.recv_timeout(IDLE_WAKEUP)
            };

            match blocking_recv {
                Ok(request) => self.process_request(request),
                Err(RecvTimeoutError::Timeout) => {
                    self.expire_grace_if_needed();
                    self.prune_dead_destinations();
                }
                Err(RecvTimeoutError::Disconnected) => {
                    error!("Snapshot worker request channel closed");
                    self.done = true;
                    return;
                }
            }
        }

        loop {
            match self.requests.try_recv() {
                Ok(request) => self.process_request(request),
                Err(TryRecvError::Empty) => break,
                Err(TryRecvError::Disconnected) => {
                    error!("Snapshot worker request channel disconnected");
                    self.done = true;
                    break;
                }
            }
        }
    }

    pub fn run(&mut self) {
        while !self.done {
            self.receive_requests(true);
        }
    }
}
