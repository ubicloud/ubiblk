# ubiblk

A block device utilities collection for virtualized environments.

## Building

1. Install Rust and Cargo:
   - Follow the instructions at [rustup.rs](https://rustup.rs/).
2. Install `isa-l_crypto` (Optional. Recommended for higher performance):

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
# With isa-l_crypto
cargo build --release

# Without isa-l_crypto
cargo build --release --features disable-isal-crypto
```

4. Run the tests:

```bash
# With isa-l_crypto
cargo test

# Without isa-l_crypto
cargo test --release --features disable-isal-crypto
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
- `remote_image`: (Optional) Remote stripe source served by `remote-bdev-server`.
- `metadata_path`: (Optional) Metadata file path used for lazy fetch. Required when `image_path` is set.
- `status_path`: (Optional) Path where stripe statistics are written in JSON format.
- `socket`: vhost-user socket path.
- `num_queues`, `queue_size`, `seg_size_max`, `seg_count_max`, `poll_queue_timeout_us` (optional): Virtqueue and I/O tuning parameters.
- `skip_sync`: (Optional) Skip flush handling for faster operation.
- `copy_on_read`: (Optional) Copy stripes from the image only when accessed.
- `track_written`: (Optional) Track stripes that have been written.
- `write_through`: (Optional) Enable the write-through mode.
- `autofetch`: (Optional) Automatically fetch stripes from the image in the background.
- `encryption_key`: (Optional) AES-XTS keys provided as base64 encoded strings.
- `io_debug_path`: (Optional) Path for I/O debug log.
- `device_id`: (Optional) Identifier returned to the guest for GET_ID.
- `cpus`: (Optional) List of CPU indices to pin backend threads to. When
  provided, the length must match `num_queues`.

**Examples:**
```bash
vhost-backend --config config.yaml
```

## Configuration File Format

The backend configuration YAML must match the `Options` struct fields:

```yaml
path: "/path/to/block-device.raw"        # String: base disk image path
image_path: "/path/to/ubi-image.raw"     # Optional String: UBI image for lazy fetch
remote_image:                             # Optional: remote server providing stripes
  address: "203.0.113.42:4555"           # Required when remote_image is set
  tls_psk_identity: "ubiblk-prod"        # Optional: PSK identity for TLS
  tls_psk_key: "AQIDBAUGBwgJCgsMDQ4PEA==" # Optional: base64 encoded PSK bytes
metadata_path: "/path/to/metadata"       # Optional: metadata path for lazy fetch
status_path: "/tmp/ubiblk-status.json"   # Optional: JSON stripe statistics output path
socket: "/tmp/vhost.sock"                # String: vhost‐user socket path
num_queues: 4                            # Integer: number of virtqueues
cpus: [0, 1, 2, 3]                       # Optional: CPU list matching num_queues
queue_size: 256                          # Integer: size of each virtqueue
seg_size_max: 4096                       # Integer: max IO segment size (bytes)
seg_count_max: 1                         # Integer: max segments per IO
poll_queue_timeout_us: 500               # Integer: poll timeout in microseconds
io_debug_path: "/tmp/io_debug.log"       # Optional: path for I/O debug log
skip_sync: false                         # Optional: skip flush handling
copy_on_read: false                      # Optional: copy stripes on first read
track_written: false                     # Optional: track written stripes
write_through: false                     # Optional: enable write-through mode
autofetch: false                         # Optional: fetch stripes automatically
device_id: "ubiblk"                      # Optional: device identifier
encryption_key:                          # Optional: AES‐XTS keys (base64 encoded)
  - "x74Yhe/ovgxY4BrBaM6Wm/9firf9k/N+ayvGsskBo+hjQtrL+nslCDC5oR/HpSDL"
  - "TJn65Jb//AYqu/a8zlpb0IlXC4vwFQ5DtbQkMTeliEAwafr0DEH+5hNro8FuVzQ+"
```

When `remote_image` is provided the backend fetches stripes from a
`remote-bdev-server` instance instead of a local `image_path`. The optional TLS
fields must either both be present or both omitted. The `tls_psk_key` field
expects base64-encoded bytes; to reuse a hexadecimal key file generated for the
server, convert it with `xxd -r -p tls-psk.hex | base64`.

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

## remote-bdev-server

`remote-bdev-server` exposes stripe data from an on-disk image over TCP. Use it
as the `remote_image` source for lazy stripe fetching when the image is not
locally available.

```bash
remote-bdev-server --config /path/to/ubiblk.yaml [--bind 0.0.0.0:4555] \
                   [--tls-psk-identity <IDENTITY> --tls-psk-key /path/to/tls-psk.hex]
```

- The configuration file must reference the block device (`path`) and its
  metadata (`metadata_path`) and must not set `image_path`.
- Specify `--bind` to control the listening address. The default is
  `127.0.0.1:4555`.
- TLS is optional. When enabled, the identity must match the one provided by
  clients and the key file must contain hexadecimal bytes of the shared PSK.

## remote-shell

`remote-shell` is a troubleshooting utility that connects to a
`remote-bdev-server`, downloads metadata and stripes on demand, and prints the
results.

```bash
remote-shell 203.0.113.42:4555 \
    [--tls-psk-identity <IDENTITY> --tls-psk-key /path/to/tls-psk.hex]
```

The TLS options behave the same way as in `remote-bdev-server`.
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
