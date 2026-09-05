use std::sync::{
    atomic::Ordering,
    mpsc::{channel, Receiver, Sender},
};

use crate::{
    backends::SECTOR_SIZE,
    block_device::{bdev_test::TestBlockDevice, shared_buffer, BlockDevice},
};

use super::{
    destination::test_destination::TestDestination,
    device::SnapshotBlockDevice,
    state::{SharedSnapshotState, COPIED, FREE, LOCKED},
    worker::{SnapshotRequest, SnapshotWorker},
};

const STRIPE_SHIFT: u8 = 3; // 8 sectors per stripe
const STRIPE_SECTORS: u64 = 1 << STRIPE_SHIFT;

struct Harness {
    device: SnapshotBlockDevice,
    state: SharedSnapshotState,
    sender: Sender<SnapshotRequest>,
    receiver: Option<Receiver<SnapshotRequest>>,
    inner: TestBlockDevice,
}

fn harness(stripes: u64) -> Harness {
    let size = stripes * STRIPE_SECTORS * SECTOR_SIZE as u64;
    let inner = TestBlockDevice::new(size);
    let (sender, receiver) = channel();
    let device = SnapshotBlockDevice::new(BlockDevice::clone(&inner), STRIPE_SHIFT, sender.clone());
    let state = device.state();
    Harness {
        device,
        state,
        sender,
        receiver: Some(receiver),
        inner,
    }
}

fn setup(stripes: u64) -> (SnapshotBlockDevice, SharedSnapshotState) {
    let h = harness(stripes);
    (h.device, h.state)
}

fn buffer_of(byte: u8, sectors: u32) -> crate::block_device::SharedBuffer {
    let buf = shared_buffer(sectors as usize * SECTOR_SIZE);
    buf.borrow_mut().as_mut_slice().fill(byte);
    buf
}

#[test]
fn passes_io_through_when_no_snapshot_is_live() {
    let (device, state) = setup(4);
    let mut channel = device.create_channel().unwrap();

    assert_eq!(state.stripe_state(0), FREE);

    channel.add_write(0, 1, buffer_of(0xAB, 1), 1);
    channel.submit().unwrap();
    assert_eq!(channel.poll(), vec![(1, true)]);

    let read_buf = buffer_of(0, 1);
    channel.add_read(0, 1, read_buf.clone(), 2);
    channel.submit().unwrap();
    assert_eq!(channel.poll(), vec![(2, true)]);
    assert_eq!(read_buf.borrow().as_slice()[0], 0xAB);
}

/// A copy-out still in flight when a second snapshot is taken belongs to the
/// generation it started in. That generation's destinations were given the
/// stripe; the new generation's have not been. If the straggler were allowed to
/// report the stripe as copied, the server would refuse to serve a stripe whose
/// only copy went to the previous fork — and the new fork can then never finish
/// recovering, which is exactly what a benchmark run turned up.
#[test]
fn a_copy_out_that_outlives_its_snapshot_leaves_the_stripe_locked() {
    let (_device, state) = setup(4);

    state.lock_all();
    assert!(
        state.begin_copy(1),
        "the stripe was locked, so it can be claimed"
    );

    // A second fork is taken while that copy-out is in flight.
    state.lock_all();

    assert!(
        !state.finish_copy(1),
        "a copy-out from the previous snapshot must not complete into this one"
    );
    assert_eq!(
        state.stripe_state(1),
        LOCKED,
        "the stripe still owes this snapshot's destinations their copy"
    );
}

#[test]
fn write_to_locked_stripe_waits_for_the_copy_out() {
    let (device, state) = setup(4);
    let mut channel = device.create_channel().unwrap();

    state.lock_all();
    assert_eq!(state.stripe_state(0), LOCKED);

    channel.add_write(0, 1, buffer_of(0xCD, 1), 1);
    channel.submit().unwrap();
    // The write is held: the snapshot still needs this stripe's old content.
    assert!(channel.poll().is_empty());
    assert!(channel.busy());

    // A stripe the snapshot does not need any more lets writes through.
    assert!(state.begin_copy(0));
    state.finish_copy(0);
    assert_eq!(state.stripe_state(0), COPIED);

    assert_eq!(channel.poll(), vec![(1, true)]);
    assert!(!channel.busy());
}

#[test]
fn writes_to_other_stripes_are_not_blocked_by_a_locked_one() {
    let (device, state) = setup(4);
    let mut channel = device.create_channel().unwrap();

    state.lock_all();
    assert!(state.begin_copy(1));
    state.finish_copy(1);

    channel.add_write(STRIPE_SECTORS, 1, buffer_of(0x11, 1), 1);
    channel.submit().unwrap();
    assert_eq!(channel.poll(), vec![(1, true)]);
}

#[test]
fn reads_are_never_blocked_by_a_locked_stripe() {
    let (device, state) = setup(4);
    let mut channel = device.create_channel().unwrap();

    state.lock_all();

    channel.add_read(0, 1, buffer_of(0, 1), 1);
    channel.submit().unwrap();
    assert_eq!(channel.poll(), vec![(1, true)]);
}

#[test]
fn only_one_copy_out_is_started_per_stripe() {
    let (_device, state) = setup(2);
    state.lock_all();

    assert!(state.begin_copy(0), "first claim wins");
    assert!(
        !state.begin_copy(0),
        "second claim finds it already copying"
    );
}

#[test]
fn draining_holds_new_io_until_the_freeze_completes() {
    let (device, state) = setup(4);
    let mut channel = device.create_channel().unwrap();

    state.begin_drain();

    channel.add_read(0, 1, buffer_of(0, 1), 1);
    channel.add_write(0, 1, buffer_of(0x22, 1), 2);
    channel.submit().unwrap();

    // Nothing reaches the device below while draining, and with no requests in
    // flight the channel reports itself drained.
    assert!(channel.poll().is_empty());
    assert!(
        state.drained(),
        "nothing was in flight when the drain started"
    );

    // The freeze happens here; afterwards the layer runs again and replays.
    state.lock_all();
    assert!(state.begin_copy(0));
    state.finish_copy(0);
    state.resume();

    let mut completed = channel.poll();
    completed.sort();
    assert_eq!(completed, vec![(1, true), (2, true)]);
}

#[test]
fn releasing_the_snapshot_unblocks_every_stripe() {
    let (device, state) = setup(4);
    let mut channel = device.create_channel().unwrap();

    state.lock_all();
    channel.add_write(0, 1, buffer_of(0x33, 1), 1);
    channel.submit().unwrap();
    assert!(channel.poll().is_empty());

    // Last destination went away: the snapshot ends and prod carries on.
    state.release_all();
    assert_eq!(state.stripe_state(0), FREE);
    assert_eq!(channel.poll(), vec![(1, true)]);
}

#[test]
fn a_write_spanning_stripes_waits_for_all_of_them() {
    let (device, state) = setup(4);
    let mut channel = device.create_channel().unwrap();

    state.lock_all();
    assert!(state.begin_copy(0));
    state.finish_copy(0);

    // Spans stripes 0 and 1; stripe 1 is still locked.
    channel.add_write(STRIPE_SECTORS - 1, 2, buffer_of(0x44, 2), 1);
    channel.submit().unwrap();
    assert!(channel.poll().is_empty());

    assert!(state.begin_copy(1));
    state.finish_copy(1);
    assert_eq!(channel.poll(), vec![(1, true)]);
}

#[test]
fn each_freeze_gets_its_own_generation() {
    let (_device, state) = setup(2);
    assert_eq!(state.generation(), 0);
    assert_eq!(state.lock_all(), 1);
    state.release_all();
    assert_eq!(state.lock_all(), 2);
}

/// Attach a destination to the snapshot that is live right now.
fn attach(worker: &mut SnapshotWorker, state: &SharedSnapshotState, destination: TestDestination) {
    worker.process_request(SnapshotRequest::AddDestination {
        destination: Box::new(destination),
        generation: state.generation(),
    });
}

fn worker_for(h: &mut Harness) -> SnapshotWorker {
    SnapshotWorker::new(
        &h.inner,
        h.state.clone(),
        h.receiver.take().expect("receiver taken once"),
    )
    .unwrap()
}

#[test]
fn a_blocked_write_pushes_the_old_content_to_every_destination() {
    let mut h = harness(4);
    let mut worker = worker_for(&mut h);
    let mut channel = h.device.create_channel().unwrap();

    // Pre-snapshot content is what the snapshot must see.
    h.inner.write(0, &[0xAA; SECTOR_SIZE], SECTOR_SIZE);

    let first = TestDestination::new(1);
    let second = TestDestination::new(2);
    attach(&mut worker, &h.state, first.clone());
    attach(&mut worker, &h.state, second.clone());
    worker.process_request(SnapshotRequest::Freeze);

    // Prod overwrites stripe 0.
    channel.add_write(0, 1, buffer_of(0xBB, 1), 1);
    channel.submit().unwrap();
    assert!(channel.poll().is_empty(), "write waits for the copy-out");

    worker.receive_requests(false);

    assert_eq!(first.offered_stripes(), vec![0]);
    assert_eq!(second.offered_stripes(), vec![0]);
    assert_eq!(first.offered.lock().unwrap()[0].1[0], 0xAA);

    // With the old content safe, the write goes through.
    assert_eq!(channel.poll(), vec![(1, true)]);
    let mut written = [0u8; SECTOR_SIZE];
    h.inner.read(0, &mut written, SECTOR_SIZE);
    assert_eq!(written[0], 0xBB);
}

#[test]
fn one_copy_out_is_requested_per_stripe_however_many_writes_wait() {
    let mut h = harness(4);
    let mut worker = worker_for(&mut h);
    let mut channel = h.device.create_channel().unwrap();

    let destination = TestDestination::new(1);
    attach(&mut worker, &h.state, destination.clone());
    worker.process_request(SnapshotRequest::Freeze);

    for id in 1..=3 {
        channel.add_write(0, 1, buffer_of(0xCC, 1), id);
    }
    channel.submit().unwrap();
    assert!(channel.poll().is_empty());

    worker.receive_requests(false);
    assert_eq!(
        destination.offered_stripes(),
        vec![0],
        "the stripe is copied out once, not once per write"
    );

    let mut completed = channel.poll();
    completed.sort();
    assert_eq!(completed, vec![(1, true), (2, true), (3, true)]);
}

#[test]
fn a_destination_that_fails_is_dropped_and_prod_carries_on() {
    let mut h = harness(4);
    let mut worker = worker_for(&mut h);
    let mut channel = h.device.create_channel().unwrap();

    let healthy = TestDestination::new(1);
    let broken = TestDestination::new(2);
    broken.fail_next_offer.store(true, Ordering::SeqCst);
    attach(&mut worker, &h.state, healthy.clone());
    attach(&mut worker, &h.state, broken.clone());
    worker.process_request(SnapshotRequest::Freeze);

    channel.add_write(0, 1, buffer_of(0xDD, 1), 1);
    channel.submit().unwrap();
    worker.receive_requests(false);

    assert_eq!(worker.destination_count(), 1, "the broken one is dropped");
    assert_eq!(healthy.offered_stripes(), vec![0]);
    assert_eq!(channel.poll(), vec![(1, true)], "prod is not held up");
}

#[test]
fn losing_the_last_destination_ends_the_snapshot() {
    let mut h = harness(4);
    let mut worker = worker_for(&mut h);
    let mut channel = h.device.create_channel().unwrap();

    let destination = TestDestination::new(7);
    attach(&mut worker, &h.state, destination.clone());
    worker.process_request(SnapshotRequest::Freeze);
    assert_eq!(h.state.stripe_state(3), LOCKED);

    channel.add_write(3 * STRIPE_SECTORS, 1, buffer_of(0xEE, 1), 1);
    channel.submit().unwrap();
    assert!(channel.poll().is_empty());

    // The fork disconnected.
    worker.process_request(SnapshotRequest::RemoveDestination(7));

    assert_eq!(h.state.stripe_state(0), FREE, "every stripe is released");
    assert!(
        !h.state.snapshot_live(),
        "the snapshot is over, not just unlocked: a fork that is still attached \
         must be told rather than served post-snapshot content"
    );
    assert_eq!(
        h.state.generation(),
        1,
        "generations stay monotonic so a later snapshot cannot reuse this id"
    );
    assert_eq!(channel.poll(), vec![(1, true)]);
}

#[test]
fn a_dead_destination_is_not_offered_stripes() {
    let mut h = harness(4);
    let mut worker = worker_for(&mut h);
    let mut channel = h.device.create_channel().unwrap();

    let destination = TestDestination::new(1);
    destination.alive.store(false, Ordering::SeqCst);
    attach(&mut worker, &h.state, destination.clone());
    worker.process_request(SnapshotRequest::Freeze);

    channel.add_write(0, 1, buffer_of(0xFF, 1), 1);
    channel.submit().unwrap();
    worker.receive_requests(false);

    assert!(destination.offered_stripes().is_empty());
    assert_eq!(worker.destination_count(), 0);
    assert_eq!(channel.poll(), vec![(1, true)]);
}

/// A fork that dies while prod is not writing has nothing to reveal it: no
/// copy-out runs, so nothing asks whether it is still there. The worker has to
/// ask on its own, or the snapshot outlives its last fork for as long as prod
/// stays quiet, and the next snapshot finds a fork still attached to this one.
#[test]
fn a_dead_destination_is_pruned_without_a_write() {
    let mut h = harness(4);
    let mut worker = worker_for(&mut h);

    let destination = TestDestination::new(1);
    attach(&mut worker, &h.state, destination.clone());
    worker.process_request(SnapshotRequest::Freeze);
    assert_eq!(h.state.destination_count(), 1);

    // The fork goes away. Nothing is written, so no copy-out will notice.
    destination.alive.store(false, Ordering::SeqCst);

    // No request is queued: the worker wakes up on its own and looks.
    worker.receive_requests(true);

    assert!(destination.offered_stripes().is_empty(), "no copy-out ran");
    assert_eq!(worker.destination_count(), 0);
    assert_eq!(
        h.state.destination_count(),
        0,
        "snapshot_status no longer reports the dead fork"
    );
    assert!(
        !h.state.snapshot_live(),
        "it was the last fork, so the snapshot ends"
    );
    assert_eq!(h.state.stripe_state(0), FREE, "prod stops paying for it");
}

#[test]
fn a_dead_destination_is_pruned_while_another_keeps_the_snapshot() {
    let mut h = harness(4);
    let mut worker = worker_for(&mut h);

    let living = TestDestination::new(1);
    let dying = TestDestination::new(2);
    attach(&mut worker, &h.state, living.clone());
    attach(&mut worker, &h.state, dying.clone());
    worker.process_request(SnapshotRequest::Freeze);

    dying.alive.store(false, Ordering::SeqCst);
    worker.receive_requests(true);

    assert_eq!(worker.destination_count(), 1);
    assert_eq!(h.state.destination_count(), 1);
    assert!(h.state.snapshot_live(), "the other fork still needs it");
    assert_eq!(h.state.stripe_state(0), LOCKED);
}

#[test]
fn a_live_idle_destination_is_not_pruned() {
    let mut h = harness(4);
    let mut worker = worker_for(&mut h);

    let destination = TestDestination::new(1);
    attach(&mut worker, &h.state, destination.clone());
    worker.process_request(SnapshotRequest::Freeze);

    // A fork that is merely quiet is not a fork that is gone.
    worker.receive_requests(true);

    assert_eq!(worker.destination_count(), 1);
    assert_eq!(h.state.destination_count(), 1);
    assert!(h.state.snapshot_live());
    assert_eq!(h.state.stripe_state(0), LOCKED);
}

#[test]
fn destinations_are_capped() {
    let mut h = harness(2);
    let mut worker = worker_for(&mut h);

    for id in 0..(super::worker::MAX_DESTINATIONS as u64 + 3) {
        attach(&mut worker, &h.state, TestDestination::new(id));
    }

    assert_eq!(worker.destination_count(), super::worker::MAX_DESTINATIONS);
}

#[test]
fn freeze_through_the_worker_bumps_the_generation() {
    let mut h = harness(2);
    let mut worker = worker_for(&mut h);
    let _ = h.sender.send(SnapshotRequest::Freeze);
    worker.receive_requests(false);
    assert_eq!(h.state.generation(), 1);
    assert_eq!(h.state.stripe_state(0), LOCKED);
}

#[test]
fn an_idle_channel_does_not_hold_the_freeze_up() {
    let h = harness(4);
    // Two channels exist; neither is polled after the drain starts.
    let _first = h.device.create_channel().unwrap();
    let _second = h.device.create_channel().unwrap();
    assert_eq!(h.state.channel_count(), 2);

    h.state.begin_drain();
    assert_eq!(h.state.channel_states(), (0, 2, 0));

    // Nothing is in flight, so the freeze retires both without either of them
    // running.
    assert!(h.state.drained());
    assert_eq!(h.state.channel_states(), (0, 0, 2));

    h.state.resume();
    assert_eq!(h.state.channel_states(), (2, 0, 0));
}

#[test]
fn a_busy_channel_holds_the_freeze_until_its_io_completes() {
    let mut h = harness(4);
    let mut channel = h.device.create_channel().unwrap();

    // TestBlockDevice completes on submit, so hold the completion by not
    // polling: the request is in flight from the slot's point of view.
    channel.add_write(0, 1, buffer_of(0x55, 1), 1);
    channel.submit().unwrap();

    h.state.begin_drain();
    assert!(
        !h.state.drained(),
        "a channel with in-flight io is not drained"
    );

    assert_eq!(channel.poll(), vec![(1, true)]);
    assert!(h.state.drained());

    // Keep the harness alive for the sender the channel holds.
    let _ = h.receiver.take();
}

#[test]
fn a_write_waits_for_a_fork_that_has_not_subscribed_yet() {
    let mut h = harness(4);
    let mut worker = worker_for(&mut h);
    let mut channel = h.device.create_channel().unwrap();

    // Snapshot taken, but the fork is still starting up.
    worker.process_request(SnapshotRequest::Freeze);

    channel.add_write(0, 1, buffer_of(0x77, 1), 1);
    channel.submit().unwrap();
    worker.receive_requests(false);

    // Losing this stripe would tear the snapshot, so the write waits instead.
    assert_eq!(worker.deferred_stripes(), &[0]);
    assert_eq!(h.state.stripe_state(0), LOCKED);
    assert!(channel.poll().is_empty(), "the write is still held");
    assert_eq!(h.state.generation(), 1, "the snapshot is still live");

    // The fork arrives: the deferred copy-out runs and the write goes through.
    let destination = TestDestination::new(1);
    attach(&mut worker, &h.state, destination.clone());

    assert_eq!(destination.offered_stripes(), vec![0]);
    assert_eq!(h.state.stripe_state(0), COPIED);
    assert_eq!(channel.poll(), vec![(1, true)]);
}

#[test]
fn a_snapshot_nobody_subscribes_to_is_given_up() {
    let mut h = harness(4);
    let mut worker = worker_for(&mut h);
    let mut channel = h.device.create_channel().unwrap();
    worker.set_subscriber_grace(std::time::Duration::from_millis(0));

    worker.process_request(SnapshotRequest::Freeze);
    channel.add_write(0, 1, buffer_of(0x88, 1), 1);
    channel.submit().unwrap();
    worker.receive_requests(false);

    // With the grace already expired, the snapshot ends rather than being
    // served half-preserved to a fork that turns up later.
    worker.expire_grace_if_needed();

    assert!(!h.state.snapshot_live(), "the snapshot is gone");
    assert_eq!(h.state.stripe_state(0), FREE);
    assert!(worker.deferred_stripes().is_empty());
    assert_eq!(
        channel.poll(),
        vec![(1, true)],
        "prod is not held any longer"
    );
}

/// Two forks taken at different moments, both catching up at the same time.
///
/// This is the case a single "has this stripe been copied out?" flag cannot
/// express: after the first fork has been given a stripe, prod moves on, and the
/// second fork must get the *newer* content while the first keeps the older one.
#[test]
fn forks_taken_at_different_moments_each_see_their_own_snapshot() {
    let mut h = harness(4);
    let mut worker = worker_for(&mut h);
    let mut channel = h.device.create_channel().unwrap();

    // v1 is on the disk when the first fork is taken.
    h.inner.write(0, &[0x11; SECTOR_SIZE], SECTOR_SIZE);

    let early = TestDestination::new(1);
    worker.process_request(SnapshotRequest::Freeze);
    attach(&mut worker, &h.state, early.clone());

    // Prod overwrites the stripe: the early fork is handed v1.
    channel.add_write(0, 1, buffer_of(0x22, 1), 1);
    channel.submit().unwrap();
    worker.receive_requests(false);
    assert_eq!(channel.poll(), vec![(1, true)]);
    assert_eq!(early.offered_stripes(), vec![0]);
    assert_eq!(early.offered.lock().unwrap()[0].1[0], 0x11);

    // A second fork is taken now, when the disk holds v2.
    let late = TestDestination::new(2);
    worker.process_request(SnapshotRequest::Freeze);
    attach(&mut worker, &h.state, late.clone());
    assert_eq!(worker.destination_count(), 2, "both forks are served");

    // Prod overwrites again. The late fork needs v2; the early fork must not be
    // handed it, because v2 is not what its snapshot held.
    channel.add_write(0, 1, buffer_of(0x33, 1), 2);
    channel.submit().unwrap();
    worker.receive_requests(false);
    assert_eq!(channel.poll(), vec![(2, true)]);

    assert_eq!(late.offered_stripes(), vec![0]);
    assert_eq!(
        late.offered.lock().unwrap()[0].1[0],
        0x22,
        "the later fork sees the content as of its own snapshot"
    );
    assert_eq!(
        early.offered_stripes(),
        vec![0],
        "the earlier fork is not handed the stripe a second time"
    );
    assert_eq!(early.offered.lock().unwrap()[0].1[0], 0x11);
}

/// A stripe nobody still needs does not hold a write up.
#[test]
fn a_write_is_not_held_for_a_stripe_every_fork_already_has() {
    let mut h = harness(4);
    let mut worker = worker_for(&mut h);
    let mut channel = h.device.create_channel().unwrap();

    let destination = TestDestination::new(1);
    worker.process_request(SnapshotRequest::Freeze);
    attach(&mut worker, &h.state, destination.clone());

    for id in 1..=2 {
        channel.add_write(0, 1, buffer_of(0x44, 1), id);
        channel.submit().unwrap();
        worker.receive_requests(false);
        assert_eq!(channel.poll(), vec![(id, true)]);
    }

    assert_eq!(
        destination.offered_stripes(),
        vec![0],
        "the second write does not copy the stripe out again"
    );
}

/// A write that arrives while the freeze is draining is queued before any
/// stripe is locked, so `add_write` has nothing to ask for. When the layer runs
/// again that write must still get its stripe copied out — otherwise it waits
/// for a copy-out nobody will ever request, and every write behind it waits too.
///
/// This is the stall that showed up on the VMs under pgbench and never in the
/// single-write demos: a write in flight at the moment of the freeze.
#[test]
fn a_write_queued_during_the_freeze_still_gets_its_copy_out() {
    let mut h = harness(4);
    let mut worker = worker_for(&mut h);
    let mut channel = h.device.create_channel().unwrap();

    let destination = TestDestination::new(1);

    // The freeze starts and a write lands mid-drain.
    h.state.begin_drain();
    channel.add_write(0, 1, buffer_of(0x99, 1), 1);
    channel.submit().unwrap();
    assert!(channel.poll().is_empty(), "the write is held by the drain");

    // The snapshot is taken and the layer runs again.
    worker.process_request(SnapshotRequest::Freeze);
    attach(&mut worker, &h.state, destination.clone());
    h.state.resume();

    // Replaying asks for the copy-out this write never got to request.
    assert!(channel.poll().is_empty(), "still waiting on the copy-out");
    worker.receive_requests(false);
    assert_eq!(destination.offered_stripes(), vec![0]);

    assert_eq!(channel.poll(), vec![(1, true)], "the write finally lands");
}
