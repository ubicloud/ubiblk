# Point-in-time snapshots

A point-in-time snapshot captures a consistent image of a ubiblk block device at a
specific moment, while the device continues serving guest I/O. Snapshots can be stored
on local filesystems for backup, disaster recovery, or migration.

## Overview

Snapshots use a **stall-and-unlock** protocol: guest I/O is briefly paused to establish
a quiescent point, then stripes are copied one at a time to a staging device while guest
writes are gated per-stripe until their data is captured. The result is a byte-for-byte
copy of the device at the quiescent point, regardless of concurrent guest writes.

Key properties:
- **Consistency**: The snapshot reflects a single point in time (the moment all channels
  drain and the bgworker enters the Operating phase).
- **Minimal disruption**: Only the initial drain/stall takes global effect (typically a few
  milliseconds). After that, only writes to not-yet-copied stripes are delayed.
- **Crash safety**: If the process crashes mid-snapshot, recovery can resume from the last
  completed stripe using persisted metadata.

## Architecture

Snapshots are built on the `bdev_ops` framework, a generic stripe operation layer that
also powers [online key rotation](rekey.md). The framework provides the stall/drain
protocol, per-stripe write gating, and bgworker integration. Snapshot-specific logic
is encapsulated in `SnapshotOperation`, which implements the `StripeOperation` trait.

### Component overview

```
                        RPC request
                            |
                   SnapshotRpcHandler           rpc.rs:41
                            |
                    try_begin_stalling()        shared_state.rs:70
                            |
               +------------+-------------+
               |                          |
        OpsIoChannel(s)             BgWorker loop
        device.rs:32                bgworker.rs:197
               |                          |
     Per-IO gating:              SnapshotOperation
     - STALLING: queue all       snapshot.rs:34
     - OPERATING: gate writes        |
       on locked stripes         For each stripe:
                                   read target -> write staging -> flush
                                   on_stripe_done -> unlock stripe
                                        |
                                 SnapshotCoordinator
                                 uploader.rs:45
```

### Phase state machine

The operation proceeds through three phases, tracked in `OpsSharedState`
(`shared_state.rs:5-7`):

| Phase | Value | Description |
|-------|:-----:|-------------|
| `NORMAL` | 0 | No operation active. Single atomic load per I/O (negligible overhead). |
| `STALLING` | 1 | Draining in-flight I/O. All new requests queued in `OpsIoChannel`. |
| `OPERATING` | 2 | Copying stripes. Writes gated per-stripe; reads pass through. |

Transitions: `NORMAL -> STALLING -> OPERATING -> NORMAL`

### I/O gating during operation

`OpsIoChannel` (`device.rs:32`) wraps the underlying `LazyIoChannel` and intercepts
I/O based on the current phase:

| Phase | Writes | Reads | Flushes |
|-------|--------|-------|---------|
| NORMAL | pass-through | pass-through | pass-through |
| STALLING | queued | queued | queued |
| OPERATING | gated on locked stripes (`device.rs:162`) | pass-through | pass-through |

Reads pass through during OPERATING because `SnapshotOperation` sets `gate_reads = false`
(`snapshot.rs:82`): the target device is only read (not modified) during snapshot copy, so
guest reads remain safe.

When a guest write targets a locked (not-yet-copied) stripe, `OpsIoChannel` sends a
`PriorityProcess` request to the bgworker (`device.rs:174`), which prioritizes that
stripe's copy to minimize write latency.

### Per-stripe copy sequence

For each stripe, `SnapshotOperation::process_stripe` (`snapshot.rs:93`) executes:

1. **Read** from target device (`snapshot.rs:101-106`)
2. **Write** to staging device (`snapshot.rs:108-117`)
3. **Flush** staging for durability (`snapshot.rs:119-123`)

After flush completes, `on_stripe_done` increments the progress counter (`snapshot.rs:128`),
and the bgworker unlocks the stripe, allowing queued guest writes to proceed.

### Empty stripe skip optimization

Stripes where `has_source = false` and `written = false` contain no meaningful data (they
have never been fetched from a source and the guest has never written to them). The snapshot
coordinator skips these stripes entirely: no target read, no staging write, no staging flush.
The stripe is still unlocked and counted as processed for completion tracking, but `process_stripe`
and `on_stripe_done` are not called.

This optimization is controlled by `StripeOperation::skip_empty_stripes()` (`operation.rs:65`):
- `SnapshotOperation` returns `true` — empty stripes are skipped
- `RekeyOperation` returns `false` — all stripes are re-encrypted

The coordinator checks `SharedMetadataState` for each stripe (`ops_coordinator.rs`):
if `fetch_state == NoSource && write_state == NotWritten`, the stripe is skipped via
`skip_and_unlock_stripe()` which durably clears `OPS_LOCKED` and unlocks without I/O.

**Impact**: For a device with N total stripes and E empty stripes, the snapshot copies only
N - E stripes. Staging regions for skipped stripes are left unmodified (zeros or previous
content).

### Bgworker coordination

The bgworker (`bgworker.rs:197`) orchestrates the full lifecycle:

1. Receive `StartOperation` request (`bgworker.rs:124`)
2. Drain fetch and metadata pipelines (`bgworker.rs:228`)
3. Wait for all `OpsIoChannel` instances to drain (`bgworker.rs:233`)
4. Lock all stripes (`bgworker.rs:270`)
5. Transition to OPERATING (`bgworker.rs:281`)
6. Process stripes, prioritizing those with queued guest writes (`bgworker.rs:289`)
7. Call `operation.complete()` and transition back to NORMAL (`bgworker.rs:401`)

## Quick start

### Prerequisites

- A running ubiblk device with RPC enabled (`rpc_socket_path` in config)
- A staging destination with enough free space for the full device

### Create a snapshot (local filesystem)

```bash
# Request a snapshot to a local directory
echo '{"command": "create_snapshot", "destination": {"LocalFs": {"path": "/mnt/backup/snapshot-2026-02-08"}}}' \
  | socat - UNIX-CONNECT:/var/run/ubiblk/rpc.sock

# Response:
# {"id": 1, "stripe_count": 1024, "stripe_size_bytes": 1048576, "total_bytes": 1073741824}
```

### Monitor progress

```bash
# Poll snapshot status
echo '{"command": "snapshot_status"}' \
  | socat - UNIX-CONNECT:/var/run/ubiblk/rpc.sock

# Response:
# {"id": 1, "state": "Copying", "stripes_copied": 512, "stripes_uploaded": 512, "stripe_count": 1024, "error": null}
```

Possible states: `Stalling`, `Copying`, `Complete`, `Failed`.

### Cancel a snapshot

```bash
echo '{"command": "cancel_snapshot"}' \
  | socat - UNIX-CONNECT:/var/run/ubiblk/rpc.sock
```

Cancellation is supported (`snapshot.rs:148`). The bgworker stops processing remaining
stripes and transitions back to NORMAL. Already-copied stripes are retained in the staging
directory.

## RPC interface

All commands are sent as JSON over a Unix domain socket (line-buffered, one request per
line). The socket path is configured via `rpc_socket_path` in the device config.

### `create_snapshot`

Starts a new point-in-time snapshot.

**Request:**
```json
{
  "command": "create_snapshot",
  "destination": {
    "LocalFs": { "path": "/mnt/backup/my-snapshot" }
  }
}
```

**Response (success):**
```json
{
  "id": 1,
  "stripe_count": 1024,
  "stripe_size_bytes": 1048576,
  "total_bytes": 1073741824
}
```

**Response (error — operation already in progress):**
```json
{
  "error": "another operation is already in progress"
}
```

Handler: `rpc.rs:70-136`

### `snapshot_status`

Returns the current snapshot status.

**Request:**
```json
{ "command": "snapshot_status" }
```

**Response:**
```json
{
  "id": 1,
  "state": "Copying",
  "stripes_copied": 512,
  "stripes_uploaded": 512,
  "stripe_count": 1024,
  "error": null
}
```

State values (`uploader.rs:28-39`):

| State | Meaning |
|-------|---------|
| `Stalling` | Draining in-flight I/O from all channels |
| `Copying` | Bgworker is copying stripes to staging |
| `Uploading` | All stripes copied; uploading to destination (S3 only) |
| `Complete` | Snapshot fully archived |
| `Failed` | Error occurred; check `error` field |

Handler: `rpc.rs:138-159`

### `cancel_snapshot`

Cancels a running snapshot.

**Request:**
```json
{ "command": "cancel_snapshot" }
```

**Response:**
```json
{ "result": "cancel requested" }
```

Cancellation takes effect after the current stripe finishes processing.
Handler: `rpc.rs:161-171`

## Configuration

Snapshots require an existing ubiblk device with RPC enabled. No additional device config
fields are needed; all snapshot parameters are passed via the RPC `create_snapshot` command.

### Destination types

| Type | Description |
|------|-------------|
| `LocalFs` | Write directly to a local or mounted filesystem path. No separate upload phase — snapshot is complete as soon as all stripes are copied. |

### Staging requirements

- The destination path must be writable and have enough free space for the full device
  (stripe_count * stripe_size_bytes).
- For `LocalFs` destinations, the staging device **is** the final destination.

## Crash recovery

Snapshot state is persisted in the device metadata to enable crash recovery:

- **Phase** (`ops_phase`): Stored in metadata header sector 0. Persisted when transitioning
  from STALLING to OPERATING.
- **Stripe locks** (`OPS_LOCKED` bit): Bit 3 in each per-stripe header byte. Set for all
  stripes at the start of OPERATING; cleared durably as each stripe is copied.
- **Operation metadata**: Snapshot ID and staging path stored in sector 0.

See `findings/snapshot-crash-persistence.md` for the full persistence protocol design.

### Crash scenarios

| Crash timing | State on disk | Recovery |
|:-------------|:--------------|:---------|
| Before STALLING | No state persisted | Clean startup, no recovery needed |
| During STALLING | Phase not persisted (volatile only) | Reverts to NORMAL; retry via RPC |
| During OPERATING | Phase=OPERATING, stripe locks persisted | Resume from locked stripes; re-copy any stripe with `OPS_LOCKED` set |
| After all stripes copied | Phase=NORMAL | Staging file is complete; no recovery needed |

**Idempotency**: Re-copying a locked stripe is safe because write gating prevents guest
writes to locked stripes, so the target device data for that stripe is unchanged from the
quiescent point.

Recovery is implemented in `bgworker.rs` (`recover_interrupted_operation`): on startup, if
`ops_phase == OPERATING`, the bgworker reads the stripe lock bitmap and re-copies all
locked stripes from the target to the staging device.

## Performance

### Hot-path cost (no snapshot active)

One `Acquire` atomic load per I/O request: `phase.load(Acquire) == NORMAL`
(`shared_state.rs:58`). This is negligible compared to io_uring submission cost.

### Stall duration

The global stall lasts until:
1. All `OpsIoChannel` instances drain their in-flight I/O
2. The bgworker drains its fetch and metadata flush pipelines
3. The target device is flushed

**Typical**: A few milliseconds.
**Worst case**: One full stripe fetch latency (source read + target write + flush +
metadata flush), if a fetch is in-flight when stalling begins.

### Per-stripe latency

Each stripe copy involves one read + one write + one flush to the staging device. For
1 MiB stripes on NVMe:
- Read: ~0.3 ms
- Write: ~0.3 ms
- Flush: ~0.1-1 ms
- **Total: ~1-2 ms per stripe**

### Write latency impact

Guest writes to not-yet-copied stripes are delayed until the stripe is copied. The
`PriorityProcess` mechanism ensures these stripes are processed next, bounding the
additional latency to one stripe copy time (~1-2 ms on NVMe).

Guest writes to already-copied (unlocked) stripes are unaffected.

### Total snapshot time

For a 1 TiB device with 1 MiB stripes (1,048,576 stripes):
- Copy phase: ~1,048,576 * 1.5 ms ~ 26 minutes (sequential, single-threaded)
- Actual time is lower due to priority processing interleaving
- Empty stripes (`!has_source && !written`) are skipped with zero I/O, reducing total time
  proportional to the fraction of empty stripes

## Limitations

1. **One operation at a time**: Only one snapshot (or rekey) can run concurrently, enforced
   by the `try_begin_stalling()` CAS (`shared_state.rs:70`). A second `create_snapshot`
   request while one is active returns an error.

2. **Staging disk space**: The destination must have free space equal to the full device
   size. For `LocalFs`, this is the final storage cost.

3. **Cannot snapshot during rekey**: Snapshots and [online rekey](rekey.md) share the
   `bdev_ops` framework and are mutually exclusive. Wait for rekey to complete before
   taking a snapshot.

4. **Bgworker single-threaded**: Stripe copies are processed one at a time on the bgworker
   thread. This bounds throughput to sequential I/O speed.

## Code references

| Component | File | Lines |
|-----------|------|-------|
| StripeOperation trait | `src/block_device/bdev_ops/operation.rs` | 23-57 |
| SnapshotOperation | `src/block_device/bdev_ops/snapshot.rs` | 34-150 |
| SnapshotCoordinator | `src/block_device/bdev_ops/uploader.rs` | 45-65 |
| OpsIoChannel (I/O gating) | `src/block_device/bdev_ops/device.rs` | 32-247 |
| OpsSharedState | `src/block_device/bdev_ops/shared_state.rs` | 14-40 |
| SnapshotRpcHandler | `src/backends/common/rpc.rs` | 41-171 |
| Bgworker operation loop | `src/block_device/bdev_lazy/bgworker.rs` | 212-419 |
| Crash recovery | `src/block_device/bdev_lazy/bgworker.rs` | `recover_interrupted_operation` |
