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

## vhost-backend

The `vhost-backend` utility launches a vhost-user-blk backend based on a YAML
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
- `path`: Base disk image path.
- `image_path`: (Optional) Image path for lazy stripe fetch.
- `metadata_path`: (Optional) Metadata file path used for lazy fetch. Required when `image_path` is set.
- `rpc_socket_path`: (Optional) Path to a Unix domain socket for runtime RPC commands.
- `socket`: vhost-user socket path.
- `num_queues`, `queue_size`, `seg_size_max`, `seg_count_max`, `poll_queue_timeout_us` (optional): Virtqueue and I/O tuning parameters.
- `copy_on_read`: (Optional) Copy stripes from the image only when accessed.
- `track_written`: (Optional) Track stripes that have been written.
- `write_through`: (Optional) Enable the write-through mode.
- `autofetch`: (Optional) Automatically fetch stripes from the image in the background.
- `encryption_key`: (Optional) AES-XTS keys provided as base64 encoded strings.
- `io_debug_path`: (Optional) Path for I/O debug log.
- `device_id`: (Optional) Identifier returned to the guest for GET_ID.
- `io_engine`: (Optional) I/O engine to use for file operations. Allowed values: `io_uring` (default), `sync`.
- `cpus`: (Optional) List of CPU indices to pin backend threads to. When
  provided, the length must match `num_queues`.

**Examples:**
```bash
vhost-backend --config config.yaml
```

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
path: "/path/to/block-device.raw"        # String: base disk image path
image_path: "/path/to/ubi-image.raw"     # Optional String: UBI image for lazy fetch
metadata_path: "/path/to/metadata"       # Optional: metadata path for lazy fetch
rpc_socket_path: "/tmp/ubiblk-rpc.sock"  # Optional: RPC Unix socket path
socket: "/tmp/vhost.sock"                # String: vhost‐user socket path
num_queues: 4                            # Integer: number of virtqueues
cpus: [0, 1, 2, 3]                       # Optional: CPU list matching num_queues
queue_size: 256                          # Integer: size of each virtqueue
seg_size_max: 4096                       # Integer: max IO segment size (bytes)
seg_count_max: 1                         # Integer: max segments per IO
poll_queue_timeout_us: 500               # Integer: poll timeout in microseconds
io_debug_path: "/tmp/io_debug.log"       # Optional: path for I/O debug log
copy_on_read: false                      # Optional: copy stripes on first read
track_written: false                     # Optional: track written stripes
write_through: false                     # Optional: enable write-through mode
autofetch: false                         # Optional: fetch stripes automatically
device_id: "ubiblk"                      # Optional: device identifier
io_engine: "io_uring"                    # Optional: io_uring (default) or sync
encryption_key:                          # Optional: AES‐XTS keys (base64 encoded)
  - "x74Yhe/ovgxY4BrBaM6Wm/9firf9k/N+ayvGsskBo+hjQtrL+nslCDC5oR/HpSDL"
  - "TJn65Jb//AYqu/a8zlpb0IlXC4vwFQ5DtbQkMTeliEAwafr0DEH+5hNro8FuVzQ+"
```

## Lazy Stripe Fetching

When `image_path` and `metadata_path` are provided, the backend copies data
from the image to the base device in units called *stripes*. The size of a
stripe is `2^stripe-sector-count-shift` sectors and the status of every stripe
is recorded in the metadata file.

If a write operation is issued to a stripe that has not been fetched yet, the
backend will first copy the stripe from the image to the base device and then
perform the write operation. However, reads are handled differently based on
`copy_on_read`:

- **`copy_on_read = false`** – A read never triggers a fetch. Read from an
  unfetched stripe will read directly from the image.
- **`copy_on_read = true`** – A read from an unfetched stripe triggers a fetch
  and completes once the stripe has been copied to the base device.

The metadata is created with `init-metadata` and stored at `metadata_path`. The
first sector contains a magic header, and subsequent sectors store a byte for
each stripe indicating whether that stripe has been fetched.

Setting `autofetch` to `true` instructs the backend to keep fetching stripes in
the background whenever no manual fetch requests are pending. This can be used
to progressively catch up with the base image even if the guest only accesses a
small portion of the device.

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
`UbiMetadata` layout, which stores a magic identifier, version fields and a byte
for each stripe indicating whether it has been fetched. This file may reside on
a regular file or block device and is loaded by the backend on startup.

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

`dump-metadata` inspects the metadata file referenced by a backend
configuration and prints a summary of fetched and written stripes. Provide the
same configuration file that the backend uses, plus an optional KEK file when
working with encrypted metadata.

```bash
dump-metadata --config config.yaml [--kek kek.yaml]
```

#### replay-log

`replay-log` replays READ and WRITE operations stored in an I/O debug log onto a
disk image. The log is produced by the backend when `io_debug_path` is set.

```bash
replay-log --log io_debug.log --disk disk.img
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

This project is licensed under the GNU Affero General Public License v3.0 or
later (AGPL-3.0-or-later), unless otherwise stated.

Some portions of the code are derived from third-party projects, and retain
their original licenses. See comments in source files for details.
