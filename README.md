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

- [Config format](docs/config.md)
- [Remote stripe server, shell, and protocol](docs/remote-stripe.md)
- [Archive binary and archive format](docs/archive.md)
- [ubitop: realtime throughput monitoring tool](docs/ubitop.md)

## vhost-backend

The `vhost-backend` binary launches a vhost-user-blk backend based on a TOML
configuration file.

```bash
vhost-backend --config <CONFIG_TOML>
```

| Flag | Short | Required | Description |
|------|-------|----------|-------------|
| `--config` | `-f` | yes | Path to the backend TOML configuration file |

**Example:**
```bash
vhost-backend --config config.toml
```

## ublk-backend

The `ublk-backend` binary exposes the backend through the Linux ublk driver.

**Note:** Treat this backend as experimental. It hasn't been tested as
extensively as `vhost-backend`.

```bash
ublk-backend --config <CONFIG_TOML> [--device-symlink <PATH>]
```

| Flag | Short | Required | Description |
|------|-------|----------|-------------|
| `--config` | `-f` | yes | Path to the backend TOML configuration file |
| `--device-symlink` | — | no | Create a symlink pointing to the created `/dev/ublkbN` device |

**Notes:**
- Requires a Linux kernel with `CONFIG_BLK_DEV_UBLK` enabled and access to
  `/dev/ublk-control` (typically root or a udev rule).
- Uses the same configuration file as `vhost-backend`. The `vhost_socket` value
  is ignored for ublk since it does not create a vhost-user socket.

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

When `rpc_socket` is provided, the backend listens for newline-delimited
JSON commands on the specified Unix socket. The following commands are
supported:

- `{"command": "version"}` – returns the backend version string.
- `{"command": "status"}` – returns the background worker status report or
  `null` when no background worker is active.
- `{"command": "queues"}` – returns an array of I/O activity snapshots for
  each queue.
- `{"command": "stats"}` – returns cumulative bytes and operation counts per
  queue.

Example using socat to query the status and pretty-print the response:

```bash
$ echo '{"command": "status"}' | nc -U -q 0 /path/to/rpc.sock | jq .
{
  "status": {
    "stripes": {
      "fetched": 265,
      "source": 3584,
      "total": 40960
    }
  }
}
```

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

## init-metadata

Initialises the metadata file required when running the backend in lazy stripe
fetch mode. The tool creates the binary metadata at `metadata_path` using the
`UbiMetadata` layout, which stores a magic identifier, version fields, and a
byte per stripe containing fetched, written, and has-source flags. This file
is loaded by the backend on startup.

```bash
init-metadata --config <CONFIG_TOML> [--stripe-sector-count-shift <SHIFT>]
```

| Flag | Short | Required | Description |
|------|-------|----------|-------------|
| `--config` | `-f` | yes | Path to the backend configuration file |
| `--stripe-sector-count-shift` | `-s` | no | Stripe size as a power of two sectors (default: 11) |

## Developer Tools

#### dump-metadata

`dump-metadata` inspects the metadata file referenced by a backend configuration
and prints a summary of fetched, written, and has-source stripes. Provide the
same configuration file that the backend uses.

```bash
dump-metadata --config <CONFIG_TOML>
```

| Flag | Short | Required | Description |
|------|-------|----------|-------------|
| `--config` | `-f` | yes | Path to the backend configuration file |

#### xts

`xts` encodes or decodes AES-XTS encrypted data files using the same
configuration format as the backend. The tool reads keys from the configuration
file and processes sectors from an input file into an output file.

```bash
xts --config <CONFIG_TOML> [options] <INPUT> <OUTPUT>
```

| Flag | Short | Required | Description |
|------|-------|----------|-------------|
| `--config` | `-f` | yes | Path to the configuration TOML file |
| `--start` | — | no | Starting sector offset |
| `--len` | — | no | Number of sectors to process |
| `--action` | — | no | `encode` or `decode` (default: `decode`) |

## License

This project is licensed under the GNU Affero General Public License v3.0
(**AGPL-3.0-only**), unless otherwise stated.

Some portions of the code are derived from third-party projects, and retain
their original licenses. See comments in source files and the `LICENSES`
directory for details.
