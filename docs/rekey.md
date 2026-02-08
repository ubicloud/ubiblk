# Data key rotation

Data key rotation re-encrypts all device data with a fresh XTS-AES-256 key pair, revoking
the old key. ubiblk supports both an **offline tool** (`ubiblk-rekey`) for exclusive-access
rotation and **online rekey** via RPC while the device is serving guest I/O.

## Overview

### Why rotate data keys?

| Scenario | KEK rotation sufficient? | Data key rotation needed? |
|----------|:------------------------:|:-------------------------:|
| Old KEK compromised (config file leaked) | Yes | Yes |
| XTS key pair extracted from memory dump | No | **Yes** |
| XTS key pair recovered from unshredded backup | No | **Yes** |
| IEEE 1619-2025 block count limit exceeded | No | **Yes** |
| NIST SP 800-57 cryptoperiod expired (2 years) | Partial | **Yes** |
| Compliance audit requiring full key rotation | No | **Yes** |

KEK rotation re-wraps keys without data I/O, but does not revoke an exposed XTS key pair.
Only data key rotation — re-encrypting every sector — revokes the actual encryption key.

### IEEE 1619-2025 key scope limits

The 2025 revision of IEEE Std 1619 (XTS-AES) defines cumulative limits on 128-bit blocks
encrypted under a single key:

| Threshold | XTS blocks | Data equivalent | Risk level |
|:---------:|:----------:|:---------------:|:----------:|
| Soft limit | 2^36 (~68.7 billion) | ~1 TiB | Recommended rotation point |
| Hard limit | 2^44 (~17.6 trillion) | ~256 TiB | Must not exceed |

These are cumulative across all writes, not just the current volume contents. Every sector
write consumes 32 XTS blocks (512 bytes / 16 bytes per block), so a 1 TiB volume with
100% write amplification effectively consumes 2 TiB of the budget.

### NIST SP 800-57 cryptoperiod

NIST recommends an originator usage period of at most 2 years for symmetric data encryption
keys. After this period, the key should be replaced even absent compromise.

## Architecture

### Key hierarchy

```
KeyEncryptionCipher (KEK)                src/crypt/key.rs
  method: None | Aes256Gcm
  key: 32-byte AES-256 key
  |
  +-- Wraps XTS key pairs (AES-256-GCM, per-encryption 12-byte nonce)
  +-- Wraps HMAC keys in archive metadata
  +-- Wraps PSK and AWS credentials

XtsBlockCipher                           src/crypt/block.rs
  key1: [u8; 32]    (AES-256 encryption key)
  key2: [u8; 32]    (AES-256 tweaking key)
  |
  +-- Per-sector XTS-AES-256 encryption/decryption
```

### Offline rekey (`ubiblk-rekey`)

The offline tool requires exclusive device access (no backend running). It re-encrypts
stripes sequentially, persisting progress to the config file after each stripe for crash
recovery.

```
ubiblk-rekey
  |
  check_exclusive_access()       rekey/mod.rs:20
  |
  Load config + KEK
  |
  Generate new XTS key pair      XtsBlockCipher::random()
  |
  ConfigUpdater::start_rekey()   rekey/progress.rs:28
  |  (atomic config write: set pending_encryption_key, rekey_state=InProgress)
  |
  For each stripe:
    rekey_stripe()               rekey/mod.rs:189
      read -> decrypt(old) -> encrypt(new) -> write
    flush
    update_progress()            rekey/progress.rs:48
  |
  complete_rekey()               rekey/progress.rs:55
  |  (atomic config write: move pending key to encryption_key, remove rekey fields)
  |
  Done
```

### Online rekey (via RPC)

Online rekey uses the same [bdev_ops framework](snapshot.md#architecture) as snapshots,
with two key differences:

1. **`gate_reads = true`** (`rekey.rs:55`): Reads to locked stripes are also gated, because
   the stripe's encryption key changes during rekey.
2. **`supports_cancel = false`** (`rekey.rs:132`): Partial rekey leaves the disk in a
   mixed-key state that must be resolved.

The `DualKeyCryptIoChannel` (`dual_key.rs:78`) sits in the I/O stack and routes
encrypt/decrypt calls to the correct key based on per-stripe rekeyed state:

```
Guest I/O
  |
  OpsIoChannel                   bdev_ops/device.rs:32
  |  (gates reads + writes on locked stripes during OPERATING)
  |
  DualKeyCryptIoChannel          bdev_ops/dual_key.rs:78
  |  (selects old_xts or new_xts per stripe via DualKeyState)
  |
  LazyIoChannel                  bdev_lazy/device.rs
  |
  UringBlockDevice               bdev_uring.rs
```

**Memory ordering**: `DualKeyState::mark_rekeyed` stores with `Release` (`dual_key.rs:32`),
and `is_rekeyed` loads with `Acquire` (`dual_key.rs:38`). The stripe lock unlock
(`shared_state.rs:86`) also uses `Release`, ensuring the rekeyed flag is visible to all
frontend threads before they can issue I/O to the unlocked stripe.

## Quick start (offline)

### Prerequisites

- The device must not be in use (no ublk or vhost backend running)
- The device config file must have `encryption_key` set
- A KEK file (recommended) or `--allow-regular-file-as-kek`

### Run the rekey tool

```bash
ubiblk-rekey --config /etc/ubiblk/device.yaml --kek /dev/stdin <<< "$(cat /path/to/kek)"
```

Or with a regular KEK file (not recommended for production):

```bash
ubiblk-rekey -f /etc/ubiblk/device.yaml -k /path/to/kek.yaml --allow-regular-file-as-kek
```

The tool will:
1. Verify exclusive access (check that no RPC socket exists)
2. Generate a new random XTS-AES-256 key pair
3. Re-encrypt all stripes, printing progress
4. Update the config file with the new key

### Resume after interruption

If the process is interrupted (crash, `kill`, power loss), simply re-run the same command.
The tool detects `rekey_state: in_progress` in the config and resumes from the last
completed stripe:

```bash
# Same command — automatically resumes
ubiblk-rekey -f /etc/ubiblk/device.yaml -k /path/to/kek.yaml --allow-regular-file-as-kek
```

### CLI arguments

| Argument | Short | Required | Description |
|----------|:-----:|:--------:|-------------|
| `--config` | `-f` | Yes | Path to the ubiblk device config YAML |
| `--kek` | `-k` | No | Path to the key encryption key file. Recommended: named pipe or `/dev/stdin` |
| `--allow-regular-file-as-kek` | — | No | Allow reading KEK from a regular file (default: disallowed for security) |

Source: `src/bin/rekey.rs:13-16`, `src/cli.rs`

## Quick start (online)

Online rekey re-encrypts the device while it continues serving guest I/O.

### Start rekey via RPC

```bash
echo '{"command": "start_rekey"}' \
  | socat - UNIX-CONNECT:/var/run/ubiblk/rpc.sock

# Response:
# {"status": "stalling", "stripes_processed": 0, "stripe_count": 1024}
```

The backend generates a new key pair internally and begins the stall-drain-rekey protocol.

### Monitor progress

```bash
echo '{"command": "rekey_status"}' \
  | socat - UNIX-CONNECT:/var/run/ubiblk/rpc.sock

# Response:
# {"state": "operating", "stripes_processed": 512, "stripe_count": 1024}
```

State values:

| State | Meaning |
|-------|---------|
| `idle` | No rekey in progress |
| `stalling` | Draining in-flight I/O from all channels |
| `operating` | Re-encrypting stripes |

### Note: online rekey cannot be canceled

Unlike [snapshots](snapshot.md), online rekey cannot be canceled once started
(`rekey.rs:132`). Partial rekey leaves the disk in a mixed-key state where some stripes
use the old key and some use the new key. The `DualKeyCryptIoChannel` handles this
transparently, but the operation must run to completion.

## Crash recovery

### Offline rekey

The offline tool persists three fields in the device config YAML:

```yaml
pending_encryption_key:       # New XTS key pair (KEK-encrypted)
  - "<base64 new_key1>"
  - "<base64 new_key2>"
rekey_state: in_progress      # or: not_started, complete
rekey_progress: 42            # Stripe index: stripes [0, 42) are rekeyed
```

Source: `src/config/device.rs:130-140`

**Write ordering**: Stripe data is flushed **before** `rekey_progress` is advanced in the
config file. The config file itself is updated atomically (write temp -> fsync -> rename ->
fsync parent directory) via `ConfigUpdater::atomic_write` (`rekey/progress.rs:136`).

**Recovery on restart**: When the tool detects `rekey_state: in_progress`, it loads both
keys and resumes from stripe `rekey_progress`. The boundary stripe (at the progress index)
is always re-processed to handle the case where the stripe was written but the config
was not yet updated.

### Idempotency proof

Re-encrypting an already-rekeyed stripe produces identical ciphertext:

1. Let `P` be the plaintext of the stripe's sectors
2. After rekeying: `C_new = XTS_Encrypt(key_new, sector, P)`
3. Re-rekey: `XTS_Decrypt(key_new, sector, C_new) = P`, then `XTS_Encrypt(key_new, sector, P) = C_new`

The operation is idempotent. This means crash recovery never produces incorrect data.

### Crash scenarios (offline)

| Crash timing | State on disk | Recovery action | Data loss? |
|:-------------|:--------------|:----------------|:----------:|
| Before any write | Nothing changed | Restart from progress | No |
| After sector write, before fsync | Sectors may or may not be persisted | Re-encrypt boundary stripe | No |
| After fsync, before config update | Stripe rekeyed, progress stale | Re-encrypt boundary (idempotent) | No |
| After config update | Clean state | Continue from progress+1 | No |

### Online rekey

Online rekey crash recovery uses the same metadata persistence as
[snapshots](snapshot.md#crash-recovery): `ops_phase` and per-stripe `OPS_LOCKED` bits
in the device metadata. On startup, if `ops_phase == OPERATING`, the bgworker detects
the interrupted rekey and clears state (key material is not persisted in metadata by design;
the rekey must be restarted via RPC).

## Key scope tracking

To comply with IEEE 1619-2025, ubiblk tracks the cumulative number of XTS blocks encrypted
under the current key via the `xts_block_count` config field.

### Counter behavior

- **Increment on write**: Each sector write adds 32 to the counter (512 bytes / 16 bytes
  per XTS block).
- **Persistence**: The counter is persisted periodically (approximate count with safety
  margin is sufficient — the IEEE limits have wide margins).
- **Reset on rekey**: When data key rotation completes, `xts_block_count` resets to 0.

### Warning thresholds

| Threshold | XTS blocks | Data equivalent | Action |
|:---------:|:----------:|:---------------:|:------:|
| Soft limit | 2^36 | ~1 TiB | Warning log: "XTS key scope approaching IEEE 1619-2025 soft limit. Consider key rotation." |
| Hard limit | 2^44 | ~256 TiB | Error log: "XTS key scope exceeds IEEE 1619-2025 hard limit! Key rotation required." |

### Config field

```yaml
xts_block_count: 1234567890   # total 128-bit blocks encrypted under current key
```

## Performance

### Offline rekey

Rekeying reads and writes every sector once. Assuming sequential I/O on NVMe (~3 GB/s):

| Volume size | Read time | Write time | Fsync overhead | Total time |
|:-----------:|:---------:|:----------:|:--------------:|:----------:|
| 1 GiB | 0.3s | 0.3s | ~1s | **~2s** |
| 100 GiB | 33s | 33s | ~100s | **~3 min** |
| 1 TiB | 340s | 340s | ~1000s | **~28 min** |

I/O amplification: 2x the volume size (one full read + one full write).

CPU overhead is not the bottleneck: XTS-AES-256 with AES-NI achieves 5-10 GB/s per core.

### Online rekey

Online rekey processes one stripe per bgworker iteration. Per-stripe cost is the same as
offline (~1-2 ms on NVMe for 1 MiB stripes), but guest I/O interleaves between stripes.

**Guest I/O impact during rekey**:
- Writes to the currently-locked stripe: delayed by one stripe rekey time (~1-2 ms)
- Writes to unlocked stripes: unaffected
- Reads to locked stripes: delayed (gate_reads=true, unlike snapshots)
- Reads to unlocked stripes: unaffected (DualKeyCryptIoChannel selects the correct key)

## Archive implications

Archives are self-contained. Each archive stores its own copy of the XTS encryption key in
its `metadata.json`, KEK-encrypted and independent of the live device's current key.

| Scenario | Behavior |
|:---------|:---------|
| Reading an old archive (pre-rekey) | Uses the archive's own key pair. Works unchanged. |
| Creating a new archive (post-rekey) | `StripeArchiver` generates a fresh, independent key per archive. The device's current key is irrelevant to archive encryption. |
| Old archives remain readable | Yes, as long as the KEK can decrypt the archive's key. |

**No re-encryption of archives is needed.** Archives are immutable after creation and
completely decoupled from the live device's key lifecycle.

**Caveat**: If the KEK is also rotated, archive `metadata.json` files need their keys
re-wrapped with the new KEK. This is a KEK-rotation concern, not a data-key-rotation
concern.

## Limitations

1. **Online rekey cannot be canceled**: Once started, the operation must run to completion.
   Partial rekey leaves the disk in a mixed-key state handled transparently by
   `DualKeyCryptIoChannel`, but there is no way to undo progress.

2. **Exclusive access for offline tool**: `ubiblk-rekey` requires no backend (ublk/vhost)
   running on the device. It checks for an active socket before starting
   (`rekey/mod.rs:20`).

3. **One operation at a time**: Online rekey and [snapshots](snapshot.md) share the
   `bdev_ops` framework and cannot run concurrently. The `try_begin_stalling()` CAS
   (`shared_state.rs:70`) enforces mutual exclusion.

4. **Read gating during online rekey**: Unlike snapshots (which only gate writes), online
   rekey gates both reads and writes to locked stripes (`rekey.rs:55`). This adds latency
   for reads targeting the currently-rekeyed stripe.

5. **Bgworker single-threaded**: Stripe re-encryption is sequential, bounded by the
   bgworker's single-threaded I/O throughput.

## Code references

### Offline rekey

| Component | File | Lines |
|-----------|------|-------|
| CLI entry point | `src/bin/rekey.rs` | 13-25 |
| Rekey orchestrator | `src/rekey/mod.rs` | 53-236 |
| Config progress tracking | `src/rekey/progress.rs` | 17-168 |
| RekeyState enum | `src/config/device.rs` | 13-18 |
| Rekey config fields | `src/config/device.rs` | 130-140 |

### Online rekey

| Component | File | Lines |
|-----------|------|-------|
| RekeyOperation | `src/block_device/bdev_ops/rekey.rs` | 24-134 |
| DualKeyState | `src/block_device/bdev_ops/dual_key.rs` | 17-40 |
| DualKeyCryptIoChannel | `src/block_device/bdev_ops/dual_key.rs` | 78-188 |
| DualKeyCryptBlockDevice | `src/block_device/bdev_ops/dual_key.rs` | 189-195 |
| RekeyRpcHandler | `src/backends/common/rpc.rs` | 192-280 |
| StripeOperation trait | `src/block_device/bdev_ops/operation.rs` | 23-57 |
| OpsIoChannel (I/O gating) | `src/block_device/bdev_ops/device.rs` | 32-247 |
| Bgworker operation loop | `src/block_device/bdev_lazy/bgworker.rs` | 212-419 |
