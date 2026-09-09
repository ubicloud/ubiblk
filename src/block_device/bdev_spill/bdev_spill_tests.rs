use std::sync::Arc;

use crate::archive::{ArchiveStore, FileSystemStore};
use crate::backends::SECTOR_SIZE;
use crate::block_device::bdev_test::TestBlockDevice;
use crate::block_device::{shared_buffer, BlockDevice, IoChannel, UringBlockDevice};

use super::device::{SpillBlockDevice, StoreFactory};
use super::map::{AddressMap, Victim};

const CHUNK_SECTORS: u64 = 8; // 4 KiB
const CHUNK_LEN: usize = CHUNK_SECTORS as usize * SECTOR_SIZE;
/// The device presents four times what the disk below holds.
const CHUNKS: u64 = 16;
const SLOTS: u64 = 4;

fn store_factory(dir: &tempfile::TempDir) -> StoreFactory {
    let objects = dir.path().join("objects");
    Arc::new(move || {
        Ok(Box::new(FileSystemStore::new(objects.clone())?) as Box<dyn ArchiveStore + Send>)
    })
}

fn device(dir: &tempfile::TempDir) -> SpillBlockDevice {
    let base = TestBlockDevice::new(SLOTS * CHUNK_LEN as u64);
    SpillBlockDevice::new(
        BlockDevice::clone(&base),
        CHUNKS * CHUNK_SECTORS,
        CHUNK_SECTORS,
        "test",
        store_factory(dir),
    )
    .expect("spill device")
}

fn settle(chan: &mut Box<dyn IoChannel>) -> Vec<(usize, bool)> {
    let mut done = Vec::new();
    for _ in 0..100_000 {
        done.extend(chan.poll());
        if !chan.busy() {
            break;
        }
    }
    done
}

fn write_at(chan: &mut Box<dyn IoChannel>, sector: u64, sectors: u32, byte: u8, id: usize) {
    let buf = shared_buffer(sectors as usize * SECTOR_SIZE);
    buf.borrow_mut().as_mut_slice().fill(byte);
    chan.add_write(sector, sectors, buf, id);
    chan.submit().unwrap();
    assert_eq!(settle(chan), vec![(id, true)], "write at sector {sector}");
}

fn read_at(chan: &mut Box<dyn IoChannel>, sector: u64, sectors: u32, id: usize) -> Vec<u8> {
    let len = sectors as usize * SECTOR_SIZE;
    let buf = shared_buffer(len);
    chan.add_read(sector, sectors, buf.clone(), id);
    chan.submit().unwrap();
    assert_eq!(settle(chan), vec![(id, true)], "read at sector {sector}");
    let data = buf.borrow().as_slice()[..len].to_vec();
    data
}

fn write_chunk(chan: &mut Box<dyn IoChannel>, chunk_id: u64, byte: u8, id: usize) {
    write_at(
        chan,
        chunk_id * CHUNK_SECTORS,
        CHUNK_SECTORS as u32,
        byte,
        id,
    );
}

fn read_chunk(chan: &mut Box<dyn IoChannel>, chunk_id: u64, id: usize) -> Vec<u8> {
    read_at(chan, chunk_id * CHUNK_SECTORS, CHUNK_SECTORS as u32, id)
}

fn evict_named(device: &SpillBlockDevice, chunk_id: usize) -> bool {
    device.evict_named(chunk_id).expect("eviction failed")
}

#[test]
fn the_device_is_larger_than_the_disk_under_it() {
    let dir = tempfile::tempdir().unwrap();
    let device = device(&dir);
    let mut chan = device.create_channel().unwrap();

    assert_eq!(device.sector_count(), CHUNKS * CHUNK_SECTORS);
    assert_eq!(device.slots(), SLOTS as usize);

    for chunk_id in 0..CHUNKS {
        write_chunk(
            &mut chan,
            chunk_id,
            0x40 + chunk_id as u8,
            chunk_id as usize,
        );
        assert!(
            device.resident_chunks() <= SLOTS as usize,
            "more chunks are on the disk below than it has room for"
        );
    }

    for chunk_id in 0..CHUNKS {
        assert_eq!(
            read_chunk(&mut chan, chunk_id, 100 + chunk_id as usize),
            vec![0x40 + chunk_id as u8; CHUNK_LEN],
            "chunk {chunk_id} did not read back as itself"
        );
    }
}

#[test]
fn a_chunk_that_was_spilled_comes_back_byte_for_byte() {
    let dir = tempfile::tempdir().unwrap();
    let device = device(&dir);
    let mut chan = device.create_channel().unwrap();

    write_chunk(&mut chan, 3, 0xAB, 1);
    assert!(evict_named(&device, 3), "chunk 3 should have been uploaded");
    assert!(!device.is_resident(3));

    assert_eq!(read_chunk(&mut chan, 3, 2), vec![0xAB; CHUNK_LEN]);
}

#[test]
fn a_chunk_nothing_ever_wrote_reads_as_zeroes() {
    let dir = tempfile::tempdir().unwrap();
    let device = device(&dir);
    let mut chan = device.create_channel().unwrap();

    assert_eq!(read_chunk(&mut chan, 9, 1), vec![0; CHUNK_LEN]);
    assert!(
        !device.is_resident(9),
        "reading nothing should not use up a slot"
    );
}

#[test]
fn a_write_makes_the_copy_in_the_store_stale() {
    let dir = tempfile::tempdir().unwrap();
    let device = device(&dir);
    let mut chan = device.create_channel().unwrap();

    write_chunk(&mut chan, 0, 0x11, 1);
    assert!(evict_named(&device, 0));

    assert_eq!(read_chunk(&mut chan, 0, 2), vec![0x11; CHUNK_LEN]);
    write_chunk(&mut chan, 0, 0x22, 3);
    assert!(
        evict_named(&device, 0),
        "the write did not make the copy in the store stale"
    );

    assert_eq!(
        read_chunk(&mut chan, 0, 4),
        vec![0x22; CHUNK_LEN],
        "served the copy from before the write"
    );
}

#[test]
fn a_chunk_whose_copy_is_still_current_is_dropped_rather_than_uploaded() {
    let dir = tempfile::tempdir().unwrap();
    let device = device(&dir);
    let mut chan = device.create_channel().unwrap();

    write_chunk(&mut chan, 5, 0x35, 1);
    assert!(evict_named(&device, 5), "the first spill is an upload");

    read_chunk(&mut chan, 5, 2);
    assert!(
        !evict_named(&device, 5),
        "a chunk unchanged since it was uploaded was uploaded again"
    );
}

#[test]
fn the_policy_never_takes_a_pinned_slot() {
    let mut map = AddressMap::new(SLOTS as usize);
    for chunk_id in 0..SLOTS as usize {
        map.install(chunk_id, true).expect("a free slot");
    }
    let pinned = map.slot_of(2).expect("chunk 2 is resident");
    map.pin(pinned);

    let mut taken = Vec::new();
    while let Some(victim) = map.claim_victim() {
        taken.push(match victim {
            Victim::Clean { slot, .. } | Victim::Dirty { slot, .. } => slot,
        });
    }

    assert!(
        !taken.contains(&pinned),
        "a slot was taken from under a request in flight"
    );
    assert_eq!(
        taken.len(),
        SLOTS as usize - 1,
        "everything else should have been takeable"
    );
}

#[test]
fn a_request_across_a_chunk_boundary_finds_both_halves() {
    let dir = tempfile::tempdir().unwrap();
    let device = device(&dir);
    let mut chan = device.create_channel().unwrap();

    write_chunk(&mut chan, 6, 0x66, 1);
    write_chunk(&mut chan, 7, 0x77, 2);
    evict_named(&device, 6);
    evict_named(&device, 7);

    // Straddles the boundary: half from one slot, half from another, and both
    // have to be fetched back first.
    let straddle = read_at(&mut chan, 7 * CHUNK_SECTORS - 2, 4, 3);
    let mut want = vec![0x66; 2 * SECTOR_SIZE];
    want.extend(vec![0x77; 2 * SECTOR_SIZE]);
    assert_eq!(straddle, want);

    write_at(&mut chan, 7 * CHUNK_SECTORS - 2, 4, 0x99, 4);
    assert_eq!(
        read_at(&mut chan, 7 * CHUNK_SECTORS - 4, 8, 5),
        [
            vec![0x66; 2 * SECTOR_SIZE],
            vec![0x99; 4 * SECTOR_SIZE],
            vec![0x77; 2 * SECTOR_SIZE],
        ]
        .concat(),
        "the write across the boundary did not land on both chunks"
    );
}

#[test]
fn a_partial_write_keeps_the_rest_of_the_chunk() {
    let dir = tempfile::tempdir().unwrap();
    let device = device(&dir);
    let mut chan = device.create_channel().unwrap();

    write_chunk(&mut chan, 4, 0x44, 1);
    assert!(evict_named(&device, 4));
    // Something else takes the slot and leaves its own bytes in it, so a chunk
    // that is not fetched back shows as this rather than as itself.
    write_chunk(&mut chan, 12, 0xBB, 2);
    assert!(evict_named(&device, 12));

    // One sector of a chunk that is only in the store: the rest has to be
    // fetched rather than left as whatever the slot held.
    write_at(&mut chan, 4 * CHUNK_SECTORS + 3, 1, 0xEE, 3);
    let chunk = read_chunk(&mut chan, 4, 4);
    assert_eq!(&chunk[..3 * SECTOR_SIZE], &vec![0x44; 3 * SECTOR_SIZE][..]);
    assert_eq!(
        &chunk[3 * SECTOR_SIZE..4 * SECTOR_SIZE],
        &vec![0xEE; SECTOR_SIZE][..]
    );
    assert_eq!(&chunk[4 * SECTOR_SIZE..], &vec![0x44; 4 * SECTOR_SIZE][..]);
}

#[test]
fn a_partial_write_to_an_untouched_chunk_leaves_zeroes_around_it() {
    let dir = tempfile::tempdir().unwrap();
    let device = device(&dir);
    let mut chan = device.create_channel().unwrap();

    write_at(&mut chan, 11 * CHUNK_SECTORS + 2, 1, 0xCC, 1);
    let chunk = read_chunk(&mut chan, 11, 2);
    assert_eq!(&chunk[..2 * SECTOR_SIZE], &vec![0; 2 * SECTOR_SIZE][..]);
    assert_eq!(
        &chunk[2 * SECTOR_SIZE..3 * SECTOR_SIZE],
        &vec![0xCC; SECTOR_SIZE][..]
    );
    assert_eq!(&chunk[3 * SECTOR_SIZE..], &vec![0; 5 * SECTOR_SIZE][..]);
}

#[test]
fn a_read_of_a_chunk_the_store_lost_fails_rather_than_returning_rubbish() {
    let dir = tempfile::tempdir().unwrap();
    let device = device(&dir);
    let mut chan = device.create_channel().unwrap();

    write_chunk(&mut chan, 7, 0x77, 1);
    evict_named(&device, 7);
    std::fs::remove_dir_all(dir.path().join("objects")).unwrap();

    let buf = shared_buffer(CHUNK_LEN);
    chan.add_read(7 * CHUNK_SECTORS, CHUNK_SECTORS as u32, buf, 2);
    chan.submit().unwrap();
    assert_eq!(
        settle(&mut chan),
        vec![(2, false)],
        "a chunk that cannot be fetched must fail the read"
    );
}

/// The tests above run over a memory device. This one runs over io_uring and a
/// real file, whose size is the point: it stays at the cache's size while the
/// device presents four times that.
#[test]
fn a_real_file_stays_the_size_of_the_cache() {
    let dir = tempfile::tempdir().unwrap();
    let image = dir.path().join("cache.raw");
    let cache_len = SLOTS * CHUNK_LEN as u64;
    std::fs::File::create(&image)
        .unwrap()
        .set_len(cache_len)
        .unwrap();

    let device = SpillBlockDevice::new(
        UringBlockDevice::new(image.clone(), 8, false, false, false).unwrap(),
        CHUNKS * CHUNK_SECTORS,
        CHUNK_SECTORS,
        "real",
        store_factory(&dir),
    )
    .unwrap();
    let mut chan = device.create_channel().unwrap();

    for chunk_id in 0..CHUNKS {
        write_chunk(
            &mut chan,
            chunk_id,
            0x80 + chunk_id as u8,
            chunk_id as usize,
        );
    }
    assert_eq!(
        std::fs::metadata(&image).unwrap().len(),
        cache_len,
        "the file below grew past the cache it is supposed to be"
    );

    for chunk_id in 0..CHUNKS {
        assert_eq!(
            read_chunk(&mut chan, chunk_id, 200 + chunk_id as usize),
            vec![0x80 + chunk_id as u8; CHUNK_LEN],
            "chunk {chunk_id} did not come back from the store"
        );
    }
}
