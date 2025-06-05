# ubiblk

A block device utilities collection for virtualized environments.


## Building

This requires `isa-l_crypto`:

```
sudo apt-get install autoconf libtool nasm clang
git clone https://github.com/intel/isa-l_crypto
cd isa-l_crypto/
./autogen.sh
./configure --prefix=/usr --libdir=/usr/lib
make -j32
sudo make install
```

## vhost-frontend

A small command-line tool that can connect to a vhost-user-blk backend and run
through the different frontend stages.  See
[docs/vhost-frontend.md](docs/vhost-frontend.md) for full documentation.

## vhost-backend

The `vhost-backend` utility launches a vhost-user-blk backend based on a YAML configuration file.
It now supports advanced features such as lazy stripe fetching for efficient I/O, integrated block encryption via KEK,
and configurable I/O debug logging.

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
- `encryption_key`: (Optional) AES-XTS keys provided as base64 encoded strings.
- `io_debug_path`: (Optional) Path for I/O debug log.

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
encryption_key:                          # Optional: AES‐XTS keys (base64 encoded)
  - "x74Yhe/ovgxY4BrBaM6Wm/9firf9k/N+ayvGsskBo+hjQtrL+nslCDC5oR/HpSDL"
  - "TJn65Jb//AYqu/a8zlpb0IlXC4vwFQ5DtbQkMTeliEAwafr0DEH+5hNro8FuVzQ+"
```

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
fetch mode.

```bash
init-metadata --config <CONFIG_YAML> [--kek <KEK_FILE>] [--unlink-kek] \
             [--stripe-sector-count-shift <SHIFT>]
```

- `-f, --config <CONFIG_YAML>`: Path to the backend configuration file.
- `-k, --kek <KEK_FILE>`: (Optional) KEK file for encrypted keys.
- `-u, --unlink-kek`: (Optional) Delete the KEK file after use.
- `-s, --stripe-sector-count-shift`: (Optional) Stripe size as a power of two
  sectors (default: `11`).

## replay-log

`replay-log` replays READ and WRITE operations stored in an I/O debug log onto a
disk image. The log is produced by the backend when `io_debug_path` is set.

```bash
replay-log --log io_debug.log --disk disk.img
```

## Coverage

The project uses [cargo-tarpaulin](https://github.com/xd009642/tarpaulin) to generate test coverage.
To produce a local report run:

```bash
cargo tarpaulin --out Html
```

Coverage is also collected in CI via `.github/workflows/coverage.yaml` and uploaded to Codecov.
