use super::*;
use std::sync::{Arc, Mutex};

#[derive(Default)]
struct Disk {
    bytes: Vec<u8>,
    paused: bool,
    limit: usize,
    fail_write: bool,
    fail_submit: bool,
    pending: VecDeque<(bool, u64, u32, SharedBuffer, usize)>,
}
struct DiskChannel(Arc<Mutex<Disk>>);
impl IoChannel for DiskChannel {
    fn add_read(&mut self, s: u64, n: u32, b: SharedBuffer, id: usize) {
        self.0
            .lock()
            .unwrap()
            .pending
            .push_back((false, s, n, b, id));
    }
    fn add_write(&mut self, s: u64, n: u32, b: SharedBuffer, id: usize) {
        self.0
            .lock()
            .unwrap()
            .pending
            .push_back((true, s, n, b, id));
    }
    fn add_flush(&mut self, _: usize) {
        panic!("prototype flush must not reach disk");
    }
    fn submit(&mut self) -> Result<()> {
        if self.0.lock().unwrap().fail_submit {
            Err(super::super::invalid("injected submit failure"))
        } else {
            Ok(())
        }
    }
    fn poll(&mut self) -> Vec<(usize, bool)> {
        let mut disk = self.0.lock().unwrap();
        if disk.paused {
            return vec![];
        }
        let mut out = vec![];
        for _ in 0..disk.pending.len().min(disk.limit) {
            let (write, s, n, b, id) = disk.pending.pop_front().unwrap();
            if write && disk.fail_write {
                disk.fail_write = false;
                out.push((id, false));
                continue;
            }
            let range = s as usize * 512..(s + n as u64) as usize * 512;
            if write {
                disk.bytes[range].copy_from_slice(&b.borrow().as_slice()[..n as usize * 512]);
            } else {
                b.borrow_mut().as_mut_slice()[..n as usize * 512]
                    .copy_from_slice(&disk.bytes[range]);
            }
            out.push((id, true));
        }
        out
    }
    fn busy(&self) -> bool {
        !self.0.lock().unwrap().pending.is_empty()
    }
}
#[derive(Default)]
struct Objects {
    data: HashMap<String, Vec<u8>>,
    puts: usize,
    hold: bool,
    fail_put: bool,
    gets: Vec<String>,
    pending_puts: Vec<(String, Vec<u8>)>,
}
struct Store(Arc<Mutex<Objects>>);
impl ArchiveStore for Store {
    fn start_get_object(&mut self, name: &str) {
        self.0.lock().unwrap().gets.push(name.into());
    }
    fn start_put_object(&mut self, name: &str, data: Vec<u8>) {
        let mut s = self.0.lock().unwrap();
        s.puts += 1;
        s.pending_puts.push((name.into(), data));
    }
    fn poll_gets(&mut self) -> Vec<(String, Result<Vec<u8>>)> {
        let mut s = self.0.lock().unwrap();
        if s.hold {
            return vec![];
        }
        std::mem::take(&mut s.gets)
            .into_iter()
            .map(|name| {
                let result = s
                    .data
                    .get(&name)
                    .cloned()
                    .ok_or_else(|| super::super::invalid("missing object"));
                (name, result)
            })
            .collect()
    }
    fn poll_puts(&mut self) -> Vec<(String, Result<()>)> {
        let mut s = self.0.lock().unwrap();
        if s.hold {
            return vec![];
        }
        std::mem::take(&mut s.pending_puts)
            .into_iter()
            .map(|(name, data)| {
                let result = if s.fail_put {
                    Err(super::super::invalid("put failed"))
                } else {
                    s.data.insert(name.clone(), data);
                    Ok(())
                };
                (name, result)
            })
            .collect()
    }
}
const STRIPE: u64 = 64;
fn stack(slots: usize) -> (SpillIoChannel, Arc<Mutex<Disk>>, Arc<Mutex<Objects>>) {
    let geometry = Geometry::new(STRIPE, STRIPE * 8 + 1, STRIPE * slots as u64).unwrap();
    let disk = Arc::new(Mutex::new(Disk {
        bytes: vec![0x77; geometry.bytes() * slots],
        limit: usize::MAX,
        ..Default::default()
    }));
    let store = Arc::new(Mutex::new(Objects::default()));
    (
        SpillIoChannel::new(
            Box::new(DiskChannel(disk.clone())),
            Box::new(Store(store.clone())),
            geometry,
            "run".into(),
            Duration::from_secs(30),
        ),
        disk,
        store,
    )
}
fn buffer(sectors: u32, byte: u8) -> SharedBuffer {
    let b = shared_buffer(sectors as usize * 512);
    b.borrow_mut().as_mut_slice().fill(byte);
    b
}
fn run(ch: &mut SpillIoChannel) -> Vec<(usize, bool)> {
    ch.submit().unwrap();
    let mut done = vec![];
    for _ in 0..1000 {
        done.extend(ch.poll());
        if !ch.busy() {
            return done;
        }
    }
    panic!("spill did not settle");
}
fn write(ch: &mut SpillIoChannel, stripe: u64, byte: u8) {
    ch.add_write(stripe * STRIPE, 1, buffer(1, byte), 1);
    assert_eq!(run(ch), vec![(1, true)]);
}
fn read(ch: &mut SpillIoChannel, stripe: u64, byte: u8) {
    let b = buffer(1, 0);
    ch.add_read(stripe * STRIPE, 1, b.clone(), 2);
    assert_eq!(run(ch), vec![(2, true)]);
    assert_eq!(b.borrow().as_slice(), vec![byte; 512]);
}

#[test]
fn one_slot_serves_concurrent_requests_for_more_stripes_than_it_holds() {
    let (mut ch, _, _) = stack(1);
    for stripe in 0..8 {
        ch.add_write(
            stripe * STRIPE,
            1,
            buffer(1, stripe as u8 + 1),
            stripe as usize,
        );
    }
    let done = run(&mut ch);
    assert_eq!(done.len(), 8);
    assert!(done.iter().all(|(_, ok)| *ok));
    for stripe in 0..8 {
        read(&mut ch, stripe, stripe as u8 + 1);
    }
    assert!(ch.stripes.iter().all(|s| s.active == 0));
}

#[test]
fn clean_and_zero_evictions_do_not_upload_again() {
    let (mut ch, _, store) = stack(1);
    read(&mut ch, 0, 0);
    read(&mut ch, 1, 0);
    assert_eq!(store.lock().unwrap().puts, 0);
    write(&mut ch, 0, 0xAB);
    read(&mut ch, 1, 0);
    assert_eq!(store.lock().unwrap().puts, 1);
    read(&mut ch, 0, 0xAB);
    read(&mut ch, 1, 0);
    assert_eq!(store.lock().unwrap().puts, 1);
}

#[test]
fn partial_writes_and_short_tail_survive_relocation() {
    let (mut ch, _, store) = stack(1);
    write(&mut ch, 8, 0x42);
    write(&mut ch, 0, 0xAB);
    read(&mut ch, 8, 0x42);
    let object = store
        .lock()
        .unwrap()
        .data
        .values()
        .find(|v| v[0] == 0x42)
        .unwrap()
        .clone();
    assert!(object[512..].iter().all(|b| *b == 0));
    let b = buffer(1, 9);
    ch.add_read(1, 1, b.clone(), 9);
    assert_eq!(run(&mut ch), vec![(9, true)]);
    assert!(b.borrow().as_slice().iter().all(|b| *b == 0));
}

#[test]
fn invalid_requests_and_flush_do_not_change_active_counts() {
    let (mut ch, _, _) = stack(1);
    ch.add_read(STRIPE - 1, 2, buffer(2, 0), 1);
    ch.add_write(STRIPE * 8 + 1, 1, buffer(1, 0), 2);
    ch.add_read(0, 2, buffer(1, 0), 3);
    ch.add_flush(4);
    assert_eq!(
        run(&mut ch),
        vec![(1, false), (2, false), (3, false), (4, true)]
    );
    assert!(ch.stripes.iter().all(|s| s.active == 0));
}

#[test]
fn failed_fetch_fails_every_waiter_and_a_later_request_can_retry() {
    let (mut ch, _, store) = stack(1);
    write(&mut ch, 0, 0xAB);
    read(&mut ch, 1, 0);
    let saved = std::mem::take(&mut store.lock().unwrap().data);
    ch.add_read(0, 1, buffer(1, 0), 7);
    ch.add_read(1, 1, buffer(1, 0), 8);
    assert_eq!(run(&mut ch), vec![(7, false), (8, false)]);
    assert_eq!(ch.stripes[0].active, 0);
    store.lock().unwrap().data = saved;
    read(&mut ch, 0, 0xAB);
}

#[test]
fn failed_upload_preserves_the_dirty_victim_and_fails_demand() {
    let (mut ch, _, store) = stack(1);
    write(&mut ch, 0, 0xAB);
    store.lock().unwrap().fail_put = true;
    ch.add_read(STRIPE, 1, buffer(1, 0), 2);
    assert_eq!(run(&mut ch), vec![(2, false)]);
    assert!(ch.stripes[0].dirty);
    read(&mut ch, 0, 0xAB);
    store.lock().unwrap().fail_put = false;
    read(&mut ch, 1, 0);
    read(&mut ch, 0, 0xAB);
}

#[test]
fn failed_write_keeps_the_slot_until_other_io_completes() {
    let (mut ch, disk, _) = stack(1);
    read(&mut ch, 0, 0);
    ch.add_write(0, 1, buffer(1, 1), 1);
    ch.add_write(1, 1, buffer(1, 2), 2);
    {
        let mut d = disk.lock().unwrap();
        d.fail_write = true;
        d.limit = 1;
    }
    ch.submit().unwrap();
    assert_eq!(ch.poll(), vec![(1, false)]);
    assert_eq!(ch.stripes[0].state, State::Failed(Some(0)));
    assert!(ch.free.is_empty());
    ch.add_read(STRIPE, 1, buffer(1, 0), 3);
    let results = run(&mut ch);
    assert!(results.contains(&(2, true)));
    assert!(results.contains(&(3, true)));
    assert_eq!(ch.stripes[0].state, State::Failed(None));
    ch.add_read(0, 1, buffer(1, 0), 4);
    assert_eq!(run(&mut ch), vec![(4, false)]);
}

#[test]
fn failed_submit_retains_an_accepted_fill_until_completion() {
    let (mut ch, disk, _) = stack(1);
    {
        let mut d = disk.lock().unwrap();
        d.fail_submit = true;
        d.paused = true;
    }
    ch.add_write(0, 1, buffer(1, 1), 1);
    ch.submit().unwrap();
    ch.poll();
    assert_eq!(ch.local.len(), 1);
    assert!(ch.free.is_empty());
    assert!(ch.transfer.is_some());
    {
        let mut d = disk.lock().unwrap();
        assert_eq!(d.pending.len(), 1);
        d.paused = false;
        d.fail_submit = false;
    }
    run(&mut ch);
    assert!(ch.local.is_empty());
    assert_eq!(ch.free.len(), 1);
}

#[test]
fn requests_arriving_during_eviction_wait_for_refetch() {
    let (mut ch, _, store) = stack(1);
    write(&mut ch, 0, 0xAB);
    store.lock().unwrap().hold = true;
    ch.add_read(STRIPE, 1, buffer(1, 0), 3);
    for _ in 0..10 {
        ch.poll();
    }
    assert_eq!(ch.stripes[0].state, State::Evicting(0));
    let b = buffer(1, 0);
    ch.add_read(0, 1, b.clone(), 4);
    store.lock().unwrap().hold = false;
    let results = run(&mut ch);
    assert_eq!(results.len(), 2);
    assert!(results.iter().all(|(_, ok)| *ok));
    assert_eq!(b.borrow().as_slice(), vec![0xAB; 512]);
}

#[test]
fn timed_out_store_does_not_accumulate_abandoned_operations() {
    let (mut ch, _, store) = stack(1);
    write(&mut ch, 0, 0xAB);
    store.lock().unwrap().hold = true;
    ch.timeout = Duration::ZERO;
    ch.add_read(STRIPE, 1, buffer(1, 0), 2);
    assert_eq!(run(&mut ch), vec![(2, false)]);
    read(&mut ch, 0, 0xAB);
    ch.add_read(STRIPE * 2, 1, buffer(1, 0), 3);
    assert_eq!(run(&mut ch), vec![(3, false)]);
    assert_eq!(store.lock().unwrap().puts, 1);
}

#[test]
fn failed_submit_does_not_strand_a_transfer_waiting_for_a_pinned_slot() {
    let (mut ch, disk, _) = stack(1);
    read(&mut ch, 0, 0);
    ch.add_write(0, 1, buffer(1, 1), 1);
    ch.add_read(STRIPE, 1, buffer(1, 0), 2);
    disk.lock().unwrap().fail_submit = true;
    ch.submit().unwrap();
    disk.lock().unwrap().fail_submit = false;
    let result = run(&mut ch);
    assert!(result.contains(&(1, false)));
    assert!(result.contains(&(2, false)));
    assert!(ch.transfer.is_none());
    assert_eq!(ch.stripes[1].active, 0);
}

#[test]
fn corrupted_object_fails_instead_of_becoming_a_slot() {
    let (mut ch, _, store) = stack(1);
    write(&mut ch, 0, 0xAB);
    read(&mut ch, 1, 0);
    store.lock().unwrap().data.values_mut().next().unwrap()[0] ^= 1;
    ch.add_read(0, 1, buffer(1, 0), 1);
    assert_eq!(run(&mut ch), vec![(1, false)]);
    assert_eq!(ch.stripes[0].state, State::Absent);
}

#[test]
fn device_clones_cannot_create_another_slot_owner() {
    use crate::block_device::{bdev_test::TestBlockDevice, BlockDevice};
    use crate::config::v2::stripe_source::ArchiveStorageConfig;
    let directory = tempfile::tempdir().unwrap();
    let base = Box::new(TestBlockDevice::new(STRIPE * 512));
    let geometry = Geometry::new(STRIPE, STRIPE * 8, STRIPE).unwrap();
    let device = super::super::SpillBlockDevice::new(
        base,
        geometry,
        ArchiveStorageConfig::Filesystem {
            path: directory.path().into(),
            archive_kek: None,
            autofetch: false,
        },
        HashMap::new(),
    );
    let clone = BlockDevice::clone(device.as_ref());
    let channel = device.create_channel().unwrap();
    assert!(clone.create_channel().is_err());
    drop(channel);
    assert!(
        device.create_channel().is_err(),
        "dropping a channel must not silently reset the logical disk"
    );
}
