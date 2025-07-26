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

If `isa-l_crypto` is not available, build using the `disable-isal-crypto` feature:

```bash
cargo build --release --features disable-isal-crypto
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
- `socket`: vhost-user socket path.
- `num_queues`, `queue_size`, `seg_size_max`, `seg_count_max`, `poll_queue_timeout_us` (optional): Virtqueue and I/O tuning parameters.
- `skip_sync`: (Optional) Skip flush handling for faster operation.
- `copy_on_read`: (Optional) Copy stripes from the image only when accessed.
- `direct_io`: (Optional) Use direct I/O (O_DIRECT) when accessing files. When enabled, request buffers are aligned to the larger of 4096 bytes or the host filesystem block size.
- `encryption_key`: (Optional) AES-XTS keys provided as base64 encoded strings.
- `io_debug_path`: (Optional) Path for I/O debug log.
- `device_id`: (Optional) Identifier returned to the guest for GET_ID.

**Examples:**
```bash
vhost-backend --config config.yaml
```

## Configuration File Format

The backend configuration YAML must match the `Options` struct fields:

```yaml
path: "/path/to/block-device.raw"        # String: base disk image path
image_path: "/path/to/ubi-image.raw"     # Optional String: UBI image for lazy fetch
metadata_path: "/path/to/metadata"       # Optional: metadata path for lazy fetch
socket: "/tmp/vhost.sock"                # String: vhost‐user socket path
num_queues: 4                            # Integer: number of virtqueues
queue_size: 256                          # Integer: size of each virtqueue
seg_size_max: 4096                       # Integer: max IO segment size (bytes)
seg_count_max: 1                         # Integer: max segments per IO
poll_queue_timeout_us: 500               # Integer: poll timeout in microseconds
io_debug_path: "/tmp/io_debug.log"       # Optional: path for I/O debug log
skip_sync: false                         # Optional: skip flush handling
copy_on_read: false                      # Optional: copy stripes on first read
direct_io: false                         # Optional: use O_DIRECT
device_id: "ubiblk"                      # Optional: device identifier
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

The metadata is created with `init-metadata` and stored at `metadata_path`.  It
contains a magic header and a byte for each stripe indicating whether that
stripe has been fetched.

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

#### replay-log

`replay-log` replays READ and WRITE operations stored in an I/O debug log onto a
disk image. The log is produced by the backend when `io_debug_path` is set.

```bash
replay-log --log io_debug.log --disk disk.img
```

## License

This project is licensed under the GNU Affero General Public License v3.0 or
later (AGPL-3.0-or-later), unless otherwise stated.

Some portions of the code are derived from third-party projects, and retain
their original licenses. See comments in source files for details.
