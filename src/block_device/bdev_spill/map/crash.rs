//! Crash the map at every write it makes, and ask recovery what it sees.
//!
//! The scenario below commits, compacts, releases a slot and hands it to
//! another chunk. It is run once per write, stopping there, and the image that
//! survives is reopened several ways: with nothing unflushed reaching the disk,
//! with some of it reaching the disk, and with the last of it torn. Every
//! commit that returned `Ok` must still be there in all of them.

use std::collections::BTreeMap;

use super::fake::FakeStorage;
use super::format::{Authority, Binding};
use super::{sectors_needed, Map};

const CHUNKS: u64 = 8;
const JOURNAL_BLOCKS: u64 = 2;

fn binding() -> Binding {
    Binding {
        device_uuid: [5u8; 16],
        chunk_size: 64 * 1024,
        logical_sector_count: 4096,
        slot_count: 4,
        store_digest: [6u8; 32],
    }
}

/// What the scenario does, as pairs of chunk and authority. Slot 3 is released
/// by chunk 0 and taken by chunk 4, which is the sequence recovery must never
/// undo.
fn steps() -> Vec<Vec<(u64, Authority)>> {
    vec![
        vec![(0, Authority::Local { slot: 3 })],
        vec![(1, Authority::Local { slot: 1 }), (2, Authority::Zero)],
        vec![(3, Authority::Local { slot: 2 })],
        vec![(
            0,
            Authority::Remote {
                open: 9,
                generation: 1,
                digest: 42,
            },
        )],
        vec![(4, Authority::Local { slot: 3 })],
        vec![(5, Authority::Unreadable)],
        vec![(6, Authority::Local { slot: 0 }), (7, Authority::Zero)],
    ]
}

struct Run {
    storage: FakeStorage,
    acknowledged: BTreeMap<u64, Authority>,
}

/// Run the scenario against a map that was created cleanly, stopping at
/// `stop_at_write` if it is reached. Creation is crashed separately: a map
/// that was never finished has nothing to lose.
fn run(stop_at_write: Option<usize>) -> Run {
    let storage = FakeStorage::new(sectors_needed(CHUNKS, JOURNAL_BLOCKS));
    let mut map = Map::create(storage, binding(), CHUNKS, JOURNAL_BLOCKS).expect("map is created");
    let mut acknowledged = BTreeMap::new();
    if let Some(at) = stop_at_write {
        map.storage.fail_writes_from(at);
    }

    for step in steps() {
        for (chunk, authority) in &step {
            map.stage(*chunk, *authority).expect("chunk is in range");
        }
        if map.commit().is_err() {
            break;
        }
        for (chunk, authority) in step {
            acknowledged.insert(chunk, authority);
        }
    }

    Run {
        storage: map.storage().clone(),
        acknowledged,
    }
}

/// The images a crash at this point could leave: nothing unflushed, some of it,
/// all of it, and all of it with the last write torn partway.
fn images(storage: &FakeStorage) -> Vec<Vec<u8>> {
    let pending = storage.pending_count();
    let mut images = vec![storage.image_without_pending()];
    for kept in 1..=pending {
        let applied: Vec<usize> = (0..kept).collect();
        images.push(storage.image_after_crash(&applied, None));
        for torn in [0, 64, 300] {
            images.push(storage.image_after_crash(&applied, Some(torn)));
        }
    }
    images
}

fn writes_before_the_scenario() -> usize {
    let storage = FakeStorage::new(sectors_needed(CHUNKS, JOURNAL_BLOCKS));
    Map::create(storage, binding(), CHUNKS, JOURNAL_BLOCKS)
        .expect("map is created")
        .storage()
        .writes
}

#[test]
fn a_crash_at_any_write_keeps_every_acknowledged_commit() {
    let total_writes = run(None).storage.writes;
    let first = writes_before_the_scenario() + 1;
    assert!(
        total_writes > first + 10,
        "the scenario is too short to sweep"
    );

    for stop_at_write in first..=total_writes {
        let run = run(Some(stop_at_write));
        for (i, image) in images(&run.storage).into_iter().enumerate() {
            let map = Map::open(FakeStorage::from_image(image), binding()).unwrap_or_else(|e| {
                panic!("crash at write {stop_at_write}, image {i}: map does not open: {e}")
            });
            for (chunk, authority) in &run.acknowledged {
                assert_eq!(
                    map.authority(*chunk),
                    *authority,
                    "crash at write {stop_at_write}, image {i}: chunk {chunk} lost its commit"
                );
            }
        }
    }
}

/// Nothing a crash leaves behind may turn into an authority that was never
/// committed - a slot that was released staying local, most of all.
#[test]
fn a_crash_invents_nothing() {
    let total_writes = run(None).storage.writes;

    for stop_at_write in writes_before_the_scenario() + 1..=total_writes {
        let run = run(Some(stop_at_write));
        for (i, image) in images(&run.storage).into_iter().enumerate() {
            let map = Map::open(FakeStorage::from_image(image), binding()).expect("map opens");
            for chunk in 0..CHUNKS {
                let recovered = map.authority(chunk);
                let ever = steps()
                    .iter()
                    .flatten()
                    .any(|(c, a)| *c == chunk && *a == recovered);
                assert!(
                    recovered == Authority::Zero || ever,
                    "crash at write {stop_at_write}, image {i}: chunk {chunk} came back as \
                     {recovered:?}, which was never committed"
                );
            }
        }
    }
}

#[test]
fn a_crash_while_flushing_keeps_every_acknowledged_commit() {
    for flushes in 2..20 {
        let storage = FakeStorage::new(sectors_needed(CHUNKS, JOURNAL_BLOCKS));
        let mut map =
            Map::create(storage, binding(), CHUNKS, JOURNAL_BLOCKS).expect("map is created");
        map.storage.fail_flushes_from(flushes);

        let mut acknowledged = BTreeMap::new();
        for step in steps() {
            for (chunk, authority) in &step {
                map.stage(*chunk, *authority).expect("chunk is in range");
            }
            if map.commit().is_err() {
                break;
            }
            for (chunk, authority) in step {
                acknowledged.insert(chunk, authority);
            }
        }

        let image = map.storage().image_without_pending();
        let recovered = Map::open(FakeStorage::from_image(image), binding())
            .unwrap_or_else(|e| panic!("flush {flushes} failed: map does not open: {e}"));
        for (chunk, authority) in &acknowledged {
            assert_eq!(
                recovered.authority(*chunk),
                *authority,
                "flush {flushes}: chunk {chunk} lost its commit"
            );
        }
    }
}

/// A map whose creation was interrupted is either not a map at all or an empty
/// one. It is never a map that claims something was written.
#[test]
fn a_crash_while_creating_leaves_nothing_or_an_empty_map() {
    let clean = FakeStorage::new(sectors_needed(CHUNKS, JOURNAL_BLOCKS));
    let total = Map::create(clean, binding(), CHUNKS, JOURNAL_BLOCKS)
        .expect("map is created")
        .storage()
        .writes;

    for stop_at_write in 1..=total {
        let mut storage = FakeStorage::new(sectors_needed(CHUNKS, JOURNAL_BLOCKS));
        storage.fail_writes_from(stop_at_write);
        // Whatever survives, creating again must work: an interrupted attempt
        // leaves no superblock, so nothing is in the way of a second one.
        let image = match Map::create(storage, binding(), CHUNKS, JOURNAL_BLOCKS) {
            Ok(map) => map.storage().image_without_pending(),
            Err(_) => {
                FakeStorage::new(sectors_needed(CHUNKS, JOURNAL_BLOCKS)).image_without_pending()
            }
        };
        let retried = Map::create(
            FakeStorage::from_image(image.clone()),
            binding(),
            CHUNKS,
            JOURNAL_BLOCKS,
        );

        if let Ok(map) = Map::open(FakeStorage::from_image(image), binding()) {
            for chunk in 0..CHUNKS {
                assert_eq!(
                    map.authority(chunk),
                    Authority::Zero,
                    "an interrupted creation came back with chunk {chunk} written"
                );
            }
            assert!(retried.is_err(), "creating over a finished map was allowed");
        } else {
            assert!(
                retried.is_ok(),
                "an interrupted creation left something that blocks a retry"
            );
        }
    }
}
