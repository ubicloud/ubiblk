# Configuration Reference

ubiblk uses a TOML configuration file. The root file is typically named
`config.toml` and may include additional files for secrets or stripe source
settings.

## Sections

A config file has these top-level sections:

| Section | Required | Description |
|---------|----------|-------------|
| `[device]` | yes | Device paths and identity |
| `[tuning]` | no | I/O performance knobs (all fields have defaults) |
| `[encryption]` | yes* | Encryption key reference |
| `[danger_zone]` | no | Safety overrides for development |
| `[stripe_source]` | no | Where to fetch stripes from |
| `[secrets.*]` | no | Named secret definitions |

\* Encryption is required unless `danger_zone.allow_unencrypted_disk = true`.

## Include System

The root config can pull in additional TOML files:

```toml
include = ["secrets.toml", "stripe_source.toml"]
```

Rules:
- Paths are relative to the directory containing `config.toml`.
- Append `?` to make an include optional (silently skipped if missing):
  `"stripe_source.toml?"`.
- Included files must not declare their own `include` (no nesting).
- Duplicate key paths across files are rejected.
- Each included file contributes disjoint top-level sections that are merged
  into the root config.

## `[device]`

Core device paths and identity.

```toml
[device]
data_path = "/dev/sda"
metadata_path = "/var/lib/ubiblk/meta"   # optional
vhost_socket = "/var/run/ubiblk.sock"    # optional
rpc_socket = "/var/run/ubiblk-rpc.sock"  # optional
device_id = "vm123"                      # optional, default: "ubiblk"
track_written = false                    # optional, default: false
sector_size = 512                        # optional, default: 512
```

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `data_path` | path | yes | — | Base block device or file |
| `metadata_path` | path | no | — | Stripe metadata file |
| `vhost_socket` | path | no | — | vhost-user socket path (required for `vhost-backend`) |
| `rpc_socket` | path | no | — | RPC Unix socket path |
| `device_id` | string | no | `"ubiblk"` | Identifier returned to the guest |
| `track_written` | boolean | no | `false` | Track which stripes have been written |
| `sector_size` | integer | no | `512` | Logical sector size the guest's data is laid out in: 512, 1024, 2048 or 4096. `data_path` must be on a device with this logical sector size, or the volume is refused. A guest's partition table counts in these sectors, so do not change it for an existing volume. |

## `[tuning]`

Performance tuning. All fields are optional with sensible defaults.

```toml
[tuning]
num_queues = 4
queue_size = 128
seg_size_max = 65536
seg_count_max = 4
physical_block_size = 4096
min_io_size = 4096
opt_io_size = 4096
poll_timeout_us = 1000
cpus = [0, 1, 2, 3]
io_engine = "io_uring"
write_through = false
direct_io = true
```

| Field | Type | Default | Valid range | Description |
|-------|------|---------|-------------|-------------|
| `num_queues` | integer | 1 | 1–63 | Number of virtqueues |
| `queue_size` | integer | 64 | power of 2, max 65536 | Queue depth |
| `seg_size_max` | integer | 65536 | 1–1048576 | Max I/O segment size (bytes) |
| `seg_count_max` | integer | 4 | 1–256 | Max segments per I/O |
| `physical_block_size` | integer | 4096 | power of 2, 512–`min_io_size` | Advertised physical block size (bytes) |
| `min_io_size` | integer | 4096 | power of 2, `physical_block_size`–16777216 | Advertised minimum efficient I/O size (bytes) |
| `opt_io_size` | integer | 4096 | power of 2, `min_io_size`–2147483648 | Advertised optimal sustained I/O size (bytes) |
| `poll_timeout_us` | integer | 1000 | 0–10000000 | Poll timeout in microseconds |
| `cpus` | list of integers | none | — | CPU pinning (length must match `num_queues`) |
| `io_engine` | string | `"io_uring"` | `"io_uring"`, `"sync"` | I/O engine |
| `write_through` | boolean | false | — | Enable write-through mode. Writes are durable when they complete, unless [disposable volume optimizations](#disposable-volume-optimizations) are enabled |
| `direct_io` | boolean | true | — | Open the data file with `O_DIRECT`. `false` requires [disposable volume optimizations](#disposable-volume-optimizations); see [Host page cache](#host-page-cache) |

The I/O topology settings apply to both the vhost-user and ublk backends.
The 4 KiB defaults suit backing devices with 4 KiB physical sectors, including
512e disks; ubiblk does not detect the backing device's physical topology. For
a device with 512-byte physical sectors, all three values can be set to 512.
Minimum and optimal sizes must be multiples of the preceding size, which the
power-of-two and ordering requirements enforce. The minimum size limit comes
from virtio's 16-bit count of logical blocks.

The logical sector size is not configurable. It is the logical sector size of
the device that holds `data_path`, detected when the disk is opened: 512 bytes
on most drives, 4096 bytes on drives formatted with 4 KiB logical sectors. It
is advertised as the logical block size, and topology values smaller than it
are raised to it. See [Sector size](../README.md#sector-size).

These values advertise alignment and preferred I/O sizes to the guest or host
kernel. They do not resize or coalesce requests and do not change ubiblk's
512-byte metadata updates. Existing configurations that omit these fields use
the new defaults: vhost-user now advertises 4 KiB physical, minimum, and optimal
sizes instead of 512 bytes; ublk's defaults remain 4 KiB.

## `[encryption]`

Encryption settings. The `xts_key` field must reference a named secret using
the `ref` sub-key.

```toml
[encryption]
xts_key.ref = "xts-key"
```

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `xts_key.ref` | string | yes | Reference to a 64-byte XTS key |

The referenced secret must resolve to exactly 64 bytes (two 32-byte AES keys:
data key and tweak key).

## `[danger_zone]`

Safety overrides for development and testing. The `enabled` flag must be `true`
for any individual bypass to take effect.

```toml
[danger_zone]
enabled = true
allow_unencrypted_disk = true
allow_inline_plaintext_secrets = true
allow_secret_over_regular_file = true
allow_unencrypted_connection = true
allow_env_secrets = true
allow_disposable_volume_optimizations = true
```

| Flag | Default | Effect when enabled |
|------|---------|---------------------|
| `enabled` | false | Master switch — all other flags are ignored unless this is true |
| `allow_unencrypted_disk` | false | Allow omitting the `[encryption]` section |
| `allow_inline_plaintext_secrets` | false | Allow `source.inline` secrets without a KEK |
| `allow_secret_over_regular_file` | false | Allow reading `source.file` secrets from regular files (not just pipes) |
| `allow_unencrypted_connection` | false | Allow remote connections without PSK |
| `allow_env_secrets` | false | Allow `source.env` secrets (environment variables persist in `/proc/PID/environ`) |
| `allow_disposable_volume_optimizations` | false | Use this disk for a single backend run. Discard it on exit. See [Disposable volume optimizations](#disposable-volume-optimizations) |

## Secrets

Secrets are declared as sub-tables under `[secrets]`. Each secret has a
`source` and an optional `encrypted_by` reference for envelope encryption.

```toml
[secrets.config-kek]
source.file = "/run/secrets/kek.pipe"

[secrets.xts-key]
source.inline = "TmVjZXNzYXJ5IGJ5dGVzIGhlcmU..."
encoding = "base64"
encrypted_by.ref = "config-kek"
```

### Source types

Each source is specified as a sub-key of `source`:

| Sub-key | Format | Description |
|---------|--------|-------------|
| `source.file` | path | Read secret from a file. Regular files are rejected unless `allow_secret_over_regular_file` is set; prefer named pipes. |
| `source.inline` | string | Inline secret data. Without `encrypted_by`, requires `allow_inline_plaintext_secrets`. |
| `source.env` | string | Read secret from an environment variable. Requires `allow_env_secrets`. |

Secret data must not exceed 8192 bytes after decoding.

**Security note on `source.env`:** Environment variables remain in the process
environment for its entire lifetime and are readable via `/proc/PID/environ` by
the same UID or root. Unlike pipe-based secrets which are consumed and discarded,
env var secrets persist. For this reason, `source.env` requires
`danger_zone.allow_env_secrets` to be enabled. For production use, prefer
`source.file` with a named pipe, which delivers the secret through a
one-time-read channel that leaves no trace in the process environment.

### Secret encoding

Each secret can set an `encoding` field (defaults to `plaintext` when omitted):

| Value | Description |
|-------|-------------|
| `plaintext` | Use the loaded bytes as-is. |
| `base64` | Decode the loaded bytes as base64 to obtain the final secret bytes. |

### KEK encryption

The `encrypted_by` field references another secret that holds a 32-byte AES-256-GCM key.
The source data is then treated as encrypted:

    [12-byte nonce || ciphertext || 16-byte GCM tag]

The secret's key name (e.g., `"xts-key"`) is used as additional authenticated
data (AAD) during decryption. This binds the ciphertext to the specific secret
name.

### Secret references

Config fields reference secrets using a `ref` sub-key:

```toml
[encryption]
xts_key.ref = "xts-key"
```

References inside `[secrets]` (the `encrypted_by` field) are handled through topological
sorting to resolve dependencies in the correct order.

### Resolution rules

1. All secrets are topologically sorted by KEK dependencies.
2. Each secret's source bytes are loaded.
3. If `encrypted_by` is specified, the raw bytes are decrypted using the resolved KEK.
4. Circular KEK dependencies are detected and rejected.

## `[stripe_source]`

Configures where to fetch stripes from. Discriminated by the `type` field.

### Raw

A local raw disk image:

```toml
[stripe_source]
type = "raw"
image_path = "/path/to/image.raw"
autofetch = false         # optional, default: false
copy_on_read = false      # optional, default: false
```

### Archive (filesystem)

An archive stored on the local filesystem:

```toml
[stripe_source]
type = "archive"
storage = "filesystem"
path = "/path/to/archive/root"
archive_kek.ref = "archive-kek"
autofetch = false         # optional, default: false
```

### Archive (S3)

An archive stored in an S3-compatible object store:

```toml
[stripe_source]
type = "archive"
storage = "s3"
bucket = "encrypted-stripes"
prefix = "v1/"                              # optional
region = "eu-west-1"                        # optional
access_key_id.ref = "aws-access-key"
secret_access_key.ref = "aws-secret-key"
session_token.ref = "aws-session-token"      # optional
archive_kek.ref = "archive-kek"
endpoint = "https://s3.example.com"         # optional
connections = 16                            # optional, default: 16
autofetch = false                           # optional, default: false
```

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `bucket` | string | yes | — | S3 bucket name |
| `prefix` | string | no | — | Key prefix (must not contain `.` or `..` path components) |
| `region` | string | no | — | AWS region |
| `access_key_id.ref` | string | yes | — | Reference to AWS access key ID secret |
| `secret_access_key.ref` | string | yes | — | Reference to AWS secret access key secret |
| `session_token.ref` | string | no | — | Reference to AWS session token secret (for temporary credentials) |
| `archive_kek.ref` | string | yes | — | Reference to 32-byte archive KEK secret |
| `endpoint` | string | no | — | Custom S3 endpoint URL |
| `connections` | integer | no | 16 | Number of S3 connections (must be > 0) |
| `autofetch` | boolean | no | false | Fetch stripes in the background |
| `connect_timeout_ms` | integer | no | 5000 | S3 connection timeout in milliseconds |
| `operation_attempt_timeout_ms` | integer | no | 20000 | S3 operation attempt timeout in milliseconds |
| `max_attempts` | integer | no | 3 | Max S3 operation attempts (initial attempt + retries) |
| `rate_limited_retry` | table | no | disabled | Jittered retry delay for rate-limited responses. See below. |

#### `rate_limited_retry`

By default, retries use the AWS SDK's jittered exponential backoff: retry _n_
waits a random duration in `[0, min(1s · 2ⁿ, 20s))`, so the first retry can fire
almost immediately. When the object store rate-limits rapid retries to the same
key, that near-instant retry can be rejected (some return `429`, which the SDK
does not retry by default) and fail the whole archive.

When `enabled`, a response with a transient status (`500`/`502`/`503`/`504`) or a
throttling status (`429`) is instead retried after `min_delay_ms + rand[0,
jitter_ms)` — a constant floor plus jitter, rather than exponential backoff.

```toml
[stripe_source.rate_limited_retry]
enabled      = true
min_delay_ms = 1500
jitter_ms    = 1500
```

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `enabled` | boolean | false | Turn the rate-limited retry delay on |
| `min_delay_ms` | integer | 0 | Floor: minimum delay before a retry (must be > 0 when enabled) |
| `jitter_ms` | integer | 0 | Width of the random jitter added on top of `min_delay_ms` (0 = no jitter) |

It applies to every S3 operation of the client it is set on. Only responses with
an HTTP status are delayed — client-side
timeouts and connection failures use the SDK's normal backoff. The delay is flat,
not exponential: a retry classifier cannot see the attempt number, so it cannot
grow the delay per attempt — but a constant floor is what avoids the rate limit.

### Remote

A remote stripe server over TLS-PSK:

```toml
[stripe_source]
type = "remote"
address = "1.2.3.4:4555"
autofetch = false         # optional, default: false

[stripe_source.psk]
identity = "client1"
secret.ref = "psk-secret"
```

PSK is required unless `danger_zone.allow_unencrypted_connection` is enabled.
The PSK secret must be at least 16 bytes.

### Disposable volume optimizations

Enable `danger_zone.allow_disposable_volume_optimizations` only for volumes
you discard when the backend exits, including after a clean shutdown. The
backend keeps changes to the lazy stripe map in RAM. Even a guest flush leaves
the on-disk map stale. Reopening, archiving, or serving the volume through a
remote stripe server can therefore return old source data or omit guest writes.

This flag replaces `allow_crash_unsafe_optimizations`. Remove the old key when
upgrading. Enable the new flag only if the volume has a single-use lifetime.

#### In-memory stripe metadata

With the default settings, fetching a stripe or marking it written updates the
metadata device and flushes the change. On a disposable volume, both operations
update the in-memory map immediately and issue no metadata I/O.

#### Unflushed stripe fetches

A fetch normally writes the source data to the disk and flushes it before
marking the stripe fetched. On a disposable volume, the backend marks the
stripe fetched as soon as the write completes and skips the flush.

#### Write-through without O_SYNC

With `tuning.write_through`, the guest sees a disk with no volatile write
cache. On a disposable volume, ubiblk opens the disk and metadata files without
`O_SYNC`. Writes still use direct I/O, while the host filesystem can defer
journal commits for operations such as allocating blocks in a sparse file.

#### Host page cache

With `tuning.direct_io = false`, the data file is opened without `O_DIRECT`,
so reads and writes go through the host page cache. Guest reads of recently
written or read blocks are served from host memory, and writes complete once
they reach it. A host crash can lose writes the guest saw complete, which is
only acceptable for a disposable volume. The cache holds ciphertext when the
disk is encrypted. The host needs memory outside its VM reservations for the
cache to help.
The guest is still shown the logical sector size of the device under the data
file, so `device.sector_size` does not change with this option.

#### Whole-stripe writes

A single guest write that covers an entire unfetched stripe can replace its
contents without copying data from the source. This saves one source read and
one disk write per stripe. A partial write still needs the source data for the
sectors it leaves untouched.

Linux guests send requests of at most `seg_count_max * seg_size_max` bytes
(256 KiB with the defaults). Choose a stripe size that a single guest request
can cover to benefit from this optimization. The stripe size is set with
`init-metadata --stripe-sector-count-shift` and defaults to 1 MiB.

## Example Configs

### Development (plaintext, no encryption)

A single-file config for local development:

```toml
[device]
data_path = "/tmp/dev-disk.raw"

[danger_zone]
enabled = true
allow_unencrypted_disk = true
allow_inline_plaintext_secrets = true
allow_secret_over_regular_file = true
```

### Production (KEK-encrypted secrets, layered files)

Split secrets into a separate file:

**config.toml:**
```toml
include = ["secrets.toml"]

[device]
data_path = "/dev/sda"
metadata_path = "/var/lib/ubiblk/meta"
vhost_socket = "/var/run/ubiblk.sock"
rpc_socket = "/var/run/ubiblk-rpc.sock"

[tuning]
num_queues = 4
queue_size = 128

[encryption]
xts_key.ref = "xts-key"
```

**secrets.toml:**
```toml
[secrets.config-kek]
source.file = "/run/secrets/kek.pipe"

[secrets.xts-key]
source.inline = "<AES-256-GCM encrypted XTS key>"
encoding = "base64"
encrypted_by.ref = "config-kek"
```

### Archive stripe source with S3

**config.toml:**
```toml
include = ["secrets.toml", "stripe_source.toml"]

[device]
data_path = "/dev/nvme0n1"
metadata_path = "/var/lib/ubiblk/meta"
vhost_socket = "/var/run/ubiblk.sock"
rpc_socket = "/var/run/ubiblk-rpc.sock"

[encryption]
xts_key.ref = "xts-key"
```

**secrets.toml:**
```toml
[secrets.config-kek]
source.file = "/run/secrets/kek.pipe"

[secrets.xts-key]
source.inline = "<encrypted XTS key>"
encoding = "base64"
encrypted_by.ref = "config-kek"

[secrets.archive-kek]
source.inline = "<encrypted archive KEK>"
encoding = "base64"
encrypted_by.ref = "config-kek"

[secrets.aws-access-key]
source.env = "AWS_ACCESS_KEY_ID"

[secrets.aws-secret-key]
source.env = "AWS_SECRET_ACCESS_KEY"
```

The S3 credentials above use `source.env`, so the config must include:

```toml
[danger_zone]
enabled = true
allow_env_secrets = true
```

**stripe_source.toml:**
```toml
[stripe_source]
type = "archive"
storage = "s3"
bucket = "encrypted-stripes"
prefix = "v1/"
region = "eu-west-1"
access_key_id.ref = "aws-access-key"
secret_access_key.ref = "aws-secret-key"
session_token.ref = "aws-session-token"      # optional
archive_kek.ref = "archive-kek"
autofetch = true
```

### Remote stripe source

**config.toml:**
```toml
include = ["secrets.toml", "stripe_source.toml"]

[device]
data_path = "/dev/sda"
metadata_path = "/var/lib/ubiblk/meta"
vhost_socket = "/var/run/ubiblk.sock"
rpc_socket = "/var/run/ubiblk-rpc.sock"

[encryption]
xts_key.ref = "xts-key"
```

**stripe_source.toml:**
```toml
[stripe_source]
type = "remote"
address = "10.0.0.1:4555"
autofetch = true

[stripe_source.psk]
identity = "client1"
secret.ref = "psk-secret"
```
