# Single-queue spill prototype

Spill presents more space than the local disk holds. One ublk queue owns all
stripe placement, guest requests, and transfers. Spill adds no background
worker or shared runtime metadata. The store adapter may use its own I/O threads.

**This device is nonpersistent.** Each new backend environment starts an empty
logical device, even with the same disk, keys, and object store. FLUSH succeeds
as a no-op and provides no restart or crash durability. Do not use this prototype
for data that must survive closing the backend.

## Configuration

```toml
[device]
data_path = "hot.raw"
stripe_sector_count_shift = 11

[tuning]
num_queues = 1
queue_size = 64
seg_size_max = 1048576
io_engine = "io_uring"

[spill]
size_mb = 4096

[spill.store]
storage = "filesystem"
path = "cold"
```

Add the normal encryption and secret sections. Spill requires encryption even
when the unencrypted-disk development override is enabled. It sits below XTS;
objects contain ciphertext addressed by logical sector, independent of slot.

`size_mb` is the logical capacity in MiB. `data_path` is a smaller pool of whole
stripe-sized slots. The final logical stripe may be short. There is no map path,
persistent UUID, separate spill prefix, or transfer-concurrency option.

`store` reuses `ArchiveStorageConfig` and its filesystem path or S3 prefix.
Relative filesystem paths are relative to the configuration file. Spill uses
raw store operations; archive wrapping options such as `archive_kek` and
`autofetch` do not apply. Objects have a fresh random run prefix and unique
transfer names. Replaced objects remain in the store; collection is deferred.

The common `device.stripe_sector_count_shift` accepts 6 through 16. A stripe is
`512 * 2^shift` bytes; the default is 11 (1 MiB), matching lazy initialization.
If `metadata_path` is supplied, its geometry is used and an explicit conflict
is rejected. For spill, the metadata is only a geometry source: fetched/written
bits are not used and no lazy worker is created. A lazy stripe source is refused.

Spill also refuses extra queues, virtio/vhost, write-through, and generic tool
paths that could bypass its single-channel ownership. Device clones cannot
create another serving channel, even after the first channel has been dropped.
Metadata allocation is capped at 256 MiB before allocating the stripe vector.

ublk caps requests to both the stripe size and `seg_size_max`, sets
`chunk_sectors`, and verifies the effective limits before announcing the device.
Admission additionally rejects requests crossing a stripe boundary, extending
past capacity, or exceeding their buffer. Spill never splits a guest request.

## Runtime

The channel keeps a stripe vector, slot owners and free slots, a delayed-request
queue, in-flight local operations, and one stripe-sized transfer buffer.
Each stripe records its state, source (`Zero` or an object), active count,
dirty bit, and an access sequence number.

Requests count as active from admission until completion, including while queued
internally. Retries do not increment the count. Resident requests can proceed
while one missing stripe is being brought in. A resident stripe with active
requests cannot be evicted.

Transfers follow an explicit state machine:

```text
NeedSlot -> ReadVictim -> UploadVictim -> FetchStripe -> WriteSlot -> Done
```

Free slots skip eviction. Clean victims retain their source and skip upload.
Never-written stripes initialize raw zeros instead of fetching; encrypted reads
therefore match the existing fresh encrypted-disk behavior, not plaintext zeros.
The physical tail of a short final stripe is also initialized to raw zeros.

Writes modify only their slot subrange. Successful completion sets dirty before
releasing the active count. A failed write makes the stripe unreadable for the
rest of the run. Its slot is reclaimed only after all outstanding requests
settle. Repair is not implemented.

Failed fetches fail all current waiters, preserving the source for a later
request. Failed evictions retain the dirty victim. A submission error halts new
local work but keeps potentially accepted operations and buffers until their
completions arrive; uncertain resources are never recycled.

An explicit store error fails the attempt; a later request can retry. S3 retries
use the configured adapter policy. A store deadline disables further transfers
for that channel, avoiding accumulation of uncancellable abandoned operations;
resident I/O remains available. Filesystem operations can block the queue.

The existing ublk polling loop is retained. Cold access can consume CPU and delay
admission of the next frontend batch. The prototype does not add eventfd wake-ups
or redesign the frontend event loop.

## Validation

`cargo test` includes delayed completion, upload/fetch failure, dirty and clean
eviction, corruption, slot lifetime, duplicate-owner, short-stripe, and real
crypt-over-io_uring tests. The encrypted test moves eight stripes through one
local slot and verifies the untouched sectors and fresh-run behavior.

On a host with a working ublk driver, run the kernel-facing smoke test:

```sh
cargo build --bin ublk-backend
UBLK_BACKEND_BIN="$PWD/target/debug/ublk-backend" python3 tests/spill_single_queue/run.py
```

It uses a temporary device, verifies the kernel queue limits, and writes and
reads more data than fits locally. Large userspace I/O exercises kernel stripe
splitting. It requires noninteractive sudo and removes its temporary files and
stops the backend on exit.
