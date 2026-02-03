# ubiblk

A block device utilities collection for virtualized environments.

## Building

1. Install Rust and Cargo:
   - Follow the instructions at [rustup.rs](https://rustup.rs/).
2. Install `isa-l_crypto`:

```bash
sudo apt-get install autoconf libtool nasm clang
git clone https://github.com/intel/isa-l_crypto
cd isa-l_crypto/
./autogen.sh
./configure --prefix=/usr --libdir=/usr/lib
make -j32
sudo make install
```

3. Build the project:

```bash
cargo build --release
```

4. Run the tests:

```bash
cargo test
```

## Documentation

- [Remote stripe server, shell, and protocol](docs/remote-stripe.md)
- [Archive binary and archive format](docs/archive.md)

## vhost-backend

The `vhost-backend` binary launches a vhost-user-blk backend based on a YAML
configuration file.

**Usage:**
```bash
vhost-backend --config <CONFIG_YAML> [--kek <KEK_FILE>] [--unlink-kek]
```

**Arguments:**
- `-f, --config <CONFIG_YAML>`  Path to the backend YAML configuration file.
- `-k, --kek <KEK_FILE>`   (Optional) Path to the key encryption file for encrypted block device support.
- `-u, --unlink-kek`       (Optional) Unlink (delete) the KEK file after use.

**Configuration:**
The configuration YAML must define:
- `path`: Base device path.
- `stripe_source`: (Optional) Stripe source configuration (local raw image, remote server, or archive).
- `image_path`: (Optional, deprecated) Image path for lazy stripe fetch.
- `metadata_path`: Metadata file path. **Required** whenever `stripe_source` or legacy `image_path` is set.
- `rpc_socket_path`: (Optional) Path to a Unix domain socket for runtime RPC commands.
- `socket`: (Optional) vhost-user socket path (required when running `vhost-backend`).
- `num_queues`, `queue_size`, `seg_size_max`, `seg_count_max`, `poll_queue_timeout_us` (optional): Virtqueue and I/O tuning parameters.
- `copy_on_read`: (Optional) Copy stripes from the stripe source only when accessed.
  **Required** to be set to true for `remote` and `archive` stripe sources.
- `track_written`: (Optional) Track stripes that have been written.
- `write_through`: (Optional) Enable the write-through mode.
- `autofetch`: (Optional) Automatically fetch stripes from the stripe source in the background.
- `encryption_key`: (Optional) AES-XTS keys provided as base64 encoded strings.
- `device_id`: (Optional) Identifier returned to the guest for GET_ID.
- `io_engine`: (Optional) I/O engine to use for file operations. Allowed values: `io_uring` (default), `sync`.
- `cpus`: (Optional) List of CPU indices to pin backend threads to. When
  provided, the length must match `num_queues`.

**Examples:**
```bash
vhost-backend --config config.yaml
```

## ublk-backend

The `ublk-backend` binary exposes the backend through the Linux ublk driver.

**Note:** Treat this backend as experimental. It hasn't been tested as
extensively as `vhost-backend`.

**Usage:**
```bash
ublk-backend --config <CONFIG_YAML> [--kek <KEK_FILE>] [--unlink-kek] [--device-symlink <PATH>]
```

**Notes:**
- Requires a Linux kernel with `CONFIG_BLK_DEV_UBLK` enabled and access to
  `/dev/ublk-control` (typically root or a udev rule).
- Uses the same configuration file as `vhost-backend`. The `socket` value is
  ignored for ublk since it does not create a vhost-user socket.

After startup, a block device such as `/dev/ublkb0` is created and can be used
with standard tools.

### Checking ublk support

To check if your kernel supports ublk, run:

```bash
grep CONFIG_BLK_DEV_UBLK /boot/config-$(uname -r)
```

If the output is `CONFIG_BLK_DEV_UBLK=y`, then ublk support is built into the
kernel. If it is `CONFIG_BLK_DEV_UBLK=m`, then ublk is built as a module and you
need to:

1. Install extra kernel modules if not already installed:

```bash
sudo apt-get install linux-modules-extra-$(uname -r)
```

2. Load the ublk module:

```bash
sudo modprobe ublk_drv
```

To make it load automatically at boot:

```bash
echo "ublk_drv" | sudo tee /etc/modules-load.d/ublk.conf
```

## RPC Interface

When `rpc_socket_path` is provided, the backend listens for newline-delimited
JSON commands on the specified Unix socket. The following commands are
supported:

- `{"command": "version"}` – returns the backend version string.
- `{"command": "status"}` – returns the background worker status report or
  `null` when no background worker is active.
- `{"command": "queues"}` – returns an array of I/O activity snapshots for
  each queue.

Example using socat to query the status and pretty-print the response:

```bash
$ echo '{"command": "status"}' | socat - UNIX-CONNECT:/tmp/ubiblk-rpc.sock | jq .
{
  "status": {
    "stripes": {
      "fetched": 428,
      "no_source": 4608,
      "total": 8192
    }
  }
}
```

## Configuration File Format

The backend configuration YAML must match the `Options` struct fields:

```yaml
path: "/path/to/block-device.raw"        # String: base device path
stripe_source:                           # Optional: stripe source configuration
  source: raw                            # raw | remote | archive
  path: "/path/to/ubi-image.raw"         # Local stripe source path
metadata_path: "/path/to/metadata"       # Required when stripe_source or image_path is set
rpc_socket_path: "/tmp/ubiblk-rpc.sock"  # Optional: RPC Unix socket path
socket: "/tmp/vhost.sock"                # Optional: vhost‐user socket path (required for vhost-backend)
num_queues: 1                            # Integer: number of virtqueues
cpus: [0]                                # Optional: CPU list matching num_queues
queue_size: 64                           # Integer: size of each virtqueue
seg_size_max: 65536                      # Integer: max IO segment size (bytes)
seg_count_max: 4                         # Integer: max segments per IO
poll_queue_timeout_us: 1000              # Integer: poll timeout in microseconds
copy_on_read: false                      # Optional: copy stripes on first read (must be true for remote/archive sources)
track_written: false                     # Optional: track written stripes
write_through: false                     # Optional: enable write-through mode
autofetch: false                         # Optional: fetch stripes automatically
device_id: "ubiblk"                      # Optional: device identifier
io_engine: "io_uring"                    # Optional: io_uring (default) or sync
encryption_key:                          # Optional: AES‐XTS keys (base64 encoded)
  - "x74Yhe/ovgxY4BrBaM6Wm/9firf9k/N+ayvGsskBo+hjQtrL+nslCDC5oR/HpSDL"
  - "TJn65Jb//AYqu/a8zlpb0IlXC4vwFQ5DtbQkMTeliEAwafr0DEH+5hNro8FuVzQ+"
```

To use a remote stripe server:

```yaml
stripe_source:
  source: remote
  address: "1.2.3.4:4555"
  psk_identity: "client1"               # Optional: must be set together with psk_secret
  psk_secret: "BASE64-ENCODED-SECRET"   # Optional: KEK-encrypted PSK secret
```

To use an archive stripe source from the local filesystem:

```yaml
stripe_source:
  source: archive
  type: filesystem
  path: "/path/to/archive"
  archive_kek:                       # Optional: KEK for archive encryption keys
    method: "aes256-gcm"
    key: "BASE64-ENCODED-KEY"
    init_vector: "BASE64-ENCODED-IV"
    auth_data: "BASE64-ENCODED-AAD"
```

To use an archive stripe source from an S3-compatible object store:

```yaml
stripe_source:
  source: archive
  type: s3
  bucket: "my-bucket"
  prefix: "path/inside/bucket"        # Optional: prefix inside the bucket
  endpoint: "https://s3.example.com"  # Optional: custom S3 endpoint
  region: "auto"                      # Optional: AWS region
  profile: "r2"                       # Optional: aws-cli profile name
  credentials:                        # Optional: KEK-encrypted credentials
    access_key_id: "BASE64-ENCODED-ACCESS-KEY-ID"
    secret_access_key: "BASE64-ENCODED-SECRET-ACCESS-KEY"
  connections: 16                     # Optional: number of connections
  archive_kek:                        # Optional: KEK for archive encryption keys
    method: "aes256-gcm"
    key: "BASE64-ENCODED-KEY"
    init_vector: "BASE64-ENCODED-IV"
    auth_data: "BASE64-ENCODED-AAD"
```

The legacy `image_path` option is still accepted for backward compatibility, but it is deprecated.

## Lazy Stripe Fetching

When a stripe source and `metadata_path` are provided, the backend copies data
from the stripe source to the base device in units called *stripes*. The size of a
stripe is `2^stripe-sector-count-shift` sectors and the status of every stripe
is recorded in the metadata file.

If a write operation is issued to a stripe that has not been fetched yet, the
backend will first copy the stripe from the stripe source to the base device and
then perform the write operation. However, reads are handled differently based
on `copy_on_read`:

- **`copy_on_read = false`** – A read never triggers a fetch. Read from an
  unfetched stripe will read directly from the stripe source. This mode is only
  supported when the stripe source is a local raw image file.
- **`copy_on_read = true`** – A read from an unfetched stripe triggers a fetch
  and completes once the stripe has been copied to the base device.

The metadata is created with `init-metadata` and stored at `metadata_path`. The
first sector contains a magic header, and subsequent sectors store a byte for
each stripe. Each byte includes bit flags for whether the stripe has been
fetched, written, and whether it exists in the source.

Setting `autofetch` to `true` instructs the backend to keep fetching stripes in
the background whenever no manual fetch requests are pending. This can be used
to progressively catch up with the stripe source even if the guest only accesses
a small portion of the device.

## Key Encryption Key (KEK) File
The keys in the configuration file can be encrypted using a KEK file. The KEK file should contain the encryption key in base64 format. The backend will use this key to decrypt the block device keys at runtime.

```yaml
method: "aes256-gcm"                # Encryption method (aes256-gcm or none)
key: "wHKSFBsRXW/VPLsJKl/mnsMs7X3Pt8NWjzZkch8Ku60=" # Base64 encoded key
init_vector: "UEt+wI+Ldq1UgQ/P"     # Base64 encoded IV
auth_data: "dm0zamdlejhfMA=="       # Base64 encoded auth data
```

## init-metadata

Initialises the metadata file required when running the backend in lazy stripe
fetch mode. The tool creates the binary metadata at `metadata_path` using the
`UbiMetadata` layout, which stores a magic identifier, version fields, and a
byte per stripe containing fetched, written, and has-source flags. This file
is loaded by the backend on startup.

```bash
init-metadata --config <CONFIG_YAML> [--kek <KEK_FILE>] [--unlink-kek] \
             [--stripe-sector-count-shift <SHIFT>]
```

- `-f, --config <CONFIG_YAML>`: Path to the backend configuration file.
- `-k, --kek <KEK_FILE>`: (Optional) KEK file for encrypted keys.
- `-u, --unlink-kek`: (Optional) Delete the KEK file after use.
- `-s, --stripe-sector-count-shift`: (Optional) Stripe size as a power of two
  sectors (default: `11`).


## Developer Tools

#### dump-metadata

`dump-metadata` inspects the metadata file referenced by a backend configuration
and prints a summary of fetched, written, and has-source stripes. Provide the
same configuration file that the backend uses, plus an optional KEK file when
working with encrypted metadata.

```bash
dump-metadata --config config.yaml [--kek kek.yaml]
```

#### xts

`xts` encodes or decodes AES-XTS encrypted data files using the same
configuration format as the backend. The tool reads keys from the configuration
file (and optional KEK file) and processes sectors from an input file into an
output file.

```bash
xts --config config.yaml [--kek kek.yaml] [--start <SECTOR>] [--len <SECTORS>] \
    [--action encode|decode] <INPUT> <OUTPUT>
```

## License

This project is licensed under the GNU Affero General Public License v3.0
(**AGPL-3.0-only**), unless otherwise stated.

Some portions of the code are derived from third-party projects, and retain
their original licenses. See comments in source files and the `LICENSES`
directory for details.
