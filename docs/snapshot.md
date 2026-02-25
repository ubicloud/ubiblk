# Snapshots

ubiblk supports live, point-in-time snapshots of a running block device.
A snapshot freezes the current disk state and creates a new active data file
that records only the changes made after the snapshot. The original data
becomes a read-only copy-on-write (COW) source for the new disk.

Snapshots are triggered via the RPC interface while the device is running.
No downtime or guest cooperation is required.

## How Snapshots Work

A ubiblk device with metadata consists of two files:

- **Data file** — the block device contents (e.g., `/var/lib/ubiblk/data.img`)
- **Metadata file** — per-stripe tracking headers (e.g., `/var/lib/ubiblk/metadata.bin`)

When a snapshot is taken:

1. All in-flight I/O is drained (completed or queued).
2. A new, empty data file and a new metadata file are created.
3. The new metadata marks every stripe as having a **source** — the old data
   file.
4. The old data file becomes read-only and serves as the COW source.
5. Queued I/O resumes against the new data file.

After the snapshot, reads and writes behave as follows:

- **Writes** go to the new data file.
- **Reads** for stripes that have been written to (or fetched from the source)
  are served from the new data file.
- **Reads** for stripes that have not yet been touched are served from the
  old data file (the COW source).

A background worker lazily copies stripes from the old data file to the new
one as they are accessed.

## Prerequisites

Snapshots require:

- A **metadata file** configured in the device config (`metadata_path` in
  `[device]`).
- An **RPC socket** configured (`rpc_socket` in `[device]`).

Devices without a metadata layer do not support snapshots. The `snapshot`
RPC command returns an error in this case.

## RPC Commands

Snapshots are controlled through two RPC commands sent over the Unix
domain socket configured by `rpc_socket`. Commands are JSON objects, one
per line.

### `snapshot` — Trigger a Snapshot

Creates a point-in-time snapshot. The caller specifies absolute paths for
the new data file and new metadata file.

**Request:**

```json
{
  "command": "snapshot",
  "new_data_path": "/var/lib/ubiblk/data.snap.1.img",
  "new_metadata_path": "/var/lib/ubiblk/metadata.snap.1.bin"
}
```

| Field               | Type   | Required | Description                          |
|---------------------|--------|----------|--------------------------------------|
| `command`           | string | yes      | Must be `"snapshot"`                 |
| `new_data_path`     | string | yes      | Absolute path for the new data file  |
| `new_metadata_path` | string | yes      | Absolute path for the new metadata file |

Both paths must be absolute. The target files must not already exist — the
daemon creates them with mode `0600`.

**Response (success):**

```json
{
  "snapshot": {
    "status": "initiated",
    "snapshot_id": "snap-1740500000"
  }
}
```

The `snapshot_id` is a unique identifier for this snapshot operation.

**Response (error — snapshot already in progress):**

```json
{
  "error": "snapshot already in progress (state: draining)"
}
```

**Response (error — no metadata layer):**

```json
{
  "error": "snapshot requires a metadata layer (metadata_path must be configured)"
}
```

**Response (error — missing parameters):**

```json
{
  "error": "snapshot command requires 'new_data_path' and 'new_metadata_path' fields"
}
```

**Response (error — file creation failure):**

```json
{
  "error": "failed to create data file: Permission denied"
}
```

### `snapshot_status` — Query Snapshot State

Returns the current snapshot state and information about the last completed
snapshot.

**Request:**

```json
{
  "command": "snapshot_status"
}
```

**Response (idle, no prior snapshot):**

```json
{
  "snapshot_status": {
    "state": "idle",
    "last_snapshot": null
  }
}
```

**Response (snapshot in progress):**

```json
{
  "snapshot_status": {
    "state": "draining",
    "last_snapshot": null
  }
}
```

**Response (idle, after successful snapshot):**

```json
{
  "snapshot_status": {
    "state": "idle",
    "last_snapshot": {
      "snapshot_id": "snap-1740500000",
      "result": "success",
      "old_data_path": "/var/lib/ubiblk/data.img",
      "new_data_path": "/var/lib/ubiblk/data.snap.1.img",
      "new_metadata_path": "/var/lib/ubiblk/metadata.snap.1.bin",
      "completed_at_unix": 1740500005
    }
  }
}
```

**Response (idle, after failed snapshot):**

```json
{
  "snapshot_status": {
    "state": "idle",
    "last_snapshot": {
      "snapshot_id": "snap-1740500000",
      "result": "failed",
      "error": "failed to create new data file: Permission denied",
      "completed_at_unix": 1740500003
    }
  }
}
```

The `state` field reflects the current phase of the snapshot lifecycle:

| State           | Meaning                                                  |
|-----------------|----------------------------------------------------------|
| `idle`          | No snapshot in progress. Normal I/O.                     |
| `draining`      | I/O channels are completing in-flight operations.        |
| `snapshotting`  | All I/O drained; creating new files and swapping layers. |
| `resuming`      | Swap complete; I/O channels are replaying queued requests.|

### Example: Taking a Snapshot with `nc`

```bash
echo '{"command": "snapshot", "new_data_path": "/var/lib/ubiblk/data.snap.1.img", "new_metadata_path": "/var/lib/ubiblk/metadata.snap.1.bin"}' \
  | nc -U /var/run/ubiblk-rpc.sock
```

Check status:

```bash
echo '{"command": "snapshot_status"}' | nc -U /var/run/ubiblk-rpc.sock
```

## File Layout

The daemon does not enforce a naming convention for snapshot files — the
caller chooses paths via the RPC command. The recommended convention is to
add a `.snap.<N>` suffix to the original file names, where `<N>` is a
monotonically increasing generation number.

### Example: Initial State

```
/var/lib/ubiblk/data.img         # active data file
/var/lib/ubiblk/metadata.bin     # active metadata file
```

### Example: After First Snapshot

```
/var/lib/ubiblk/data.img              # read-only COW source (original data)
/var/lib/ubiblk/metadata.bin          # original metadata (no longer active)
/var/lib/ubiblk/data.snap.1.img       # new active data file (writes go here)
/var/lib/ubiblk/metadata.snap.1.bin   # new active metadata (all stripes marked as having a source)
```

### File Properties

| File             | Permissions | Sparse | Description                        |
|------------------|-------------|--------|------------------------------------|
| New data file    | `0600`      | yes    | Same size as original data file    |
| New metadata file| `0600`      | no     | Sized for the device's stripe count|

Both files are created with `O_CREAT | O_EXCL | O_NOFOLLOW` to prevent
overwriting existing files and following symlinks.

## Limitations

- **One snapshot at a time.** A new snapshot cannot be triggered while one
  is in progress. The `snapshot` command returns an error if the device is
  in any state other than `idle`.

- **No snapshot chaining.** Only a single level of snapshot is supported.
  Taking a second snapshot on top of an existing snapshot is not supported.
  To take another snapshot, first flatten (merge) the current snapshot back
  into the base data file, then snapshot again.

- **Requires a metadata layer.** Snapshots only work when `metadata_path`
  is configured in the `[device]` section. Devices without metadata do not
  track per-stripe state and cannot support COW behavior.

- **Encryption keys are shared.** The new data file uses the same encryption
  configuration (XTS keys) as the original. Snapshot files cannot use
  different encryption keys.

- **Paths must be absolute.** The RPC `snapshot` command does not resolve
  relative paths. Both `new_data_path` and `new_metadata_path` must be
  absolute.

## Architecture

The snapshot feature is implemented as a `bdev_snapshot` layer that sits
between the userspace I/O interface and the existing `bdev_lazy` layer in
the device stack.

### Device Stack

```
Userspace I/O
      |
SnapshotBlockDevice     intercepts I/O for drain/queue during snapshot
      |
LazyBlockDevice         COW reads from source, writes to active data file
      |
CryptBlockDevice        encryption layer (if configured)
      |
I/O Engine              io_uring or sync backend (actual disk I/O)
```

### Snapshot Lifecycle

When a `snapshot` RPC command is received, the snapshot layer coordinates
all I/O channels through a four-phase lifecycle:

```
     snapshot RPC
         |
     +-------+
     | Idle  |  normal pass-through
     +---+---+
         |
         v
  +-----------+
  | Draining  |  each channel completes in-flight I/O, queues new requests
  +-----+-----+
        |  all channels drained
        v
 +--------------+
 | Snapshotting  |  no I/O active; create files, swap device layers
 +------+-------+
        |  swap complete
        v
  +-----------+
  | Resuming  |  channels replay queued I/O against the new device
  +-----+-----+
        |  all channels resumed
        v
     +------+
     | Idle |  normal operation on new data file
     +------+
```

**Draining:** Each I/O channel stops sending new operations to the
underlying device and waits for all in-flight operations to complete.
New I/O requests arriving during this phase are queued in memory.

**Snapshotting:** With all I/O quiesced, the snapshot layer creates the
new data and metadata files, initializes metadata with all stripes marked
as having a source, stops the old background worker, starts a new
background worker pointing at the new files, and updates the lazy layer
to use the new device stack.

**Resuming:** Each I/O channel replays its queued requests against the
new device in the original order, then returns to normal operation.

The entire operation is coordinated using lock-free atomics for state
tracking and counters. Each I/O channel checks the current state on every
poll cycle and acts accordingly — no locks are held on the I/O hot path.

### Background Worker

The background worker is responsible for lazily copying stripes from the
COW source to the active data file. During a snapshot:

1. The old background worker is stopped (it was fetching stripes for the
   old device configuration).
2. A new background worker is started with the old data file as its stripe
   source and the new data file as its target.
3. As the guest accesses stripes that haven't been copied yet, the
   background worker fetches them from the old data file on demand.
