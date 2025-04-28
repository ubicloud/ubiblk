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

The `vhost-frontend` utility is a command-line tool that connects to a vhost-user-blk backend and provides various functionalities for interacting with virtualized block devices.

### Usage

```
vhost-frontend --socket <SOCKET_PATH> [--output <OUTPUT_FILE>] [--stage <STAGE>]
```

### Arguments

- `-s, --socket <SOCKET_PATH>`: Path to the vhost-user socket (required)
- `-o, --output <OUTPUT_FILE>`: Path to the output file (required for the copy stage)
- `--stage <STAGE>`: Execution stage to run (default: "4")

### Stages

The `--stage` argument allows for running the vhost-frontend at different execution stages:

| Value | Name       | Description                                      |
|-------|------------|--------------------------------------------------|
| 0     | setup      | Connect to the socket and set up basic frontend  |
| 1     | config     | Read and display device configuration            |
| 2     | memory     | Allocate and set up device memory                |
| 3     | virtqueue  | Set up the virtqueue for device communication    |
| 4     | copy       | Copy data from the device to the output file     |

You can specify the stage by number or name: `--stage 2` or `--stage memory`.

### Examples

Connect to a vhost-user socket and display device configuration:
```
vhost-frontend --socket /tmp/vhost.sock --stage config
```

Copy data from a block device to a file:
```
vhost-frontend --socket /tmp/vhost.sock --output disk.img
```

Set up the virtqueue without copying data:
```
vhost-frontend --socket /tmp/vhost.sock --stage virtqueue
```

## vhost-backend

The `vhost-backend` utility launches a vhost-user-blk backend based on a YAML config.

Usage:
```bash
vhost-backend --config <CONFIG_YAML>
```

Arguments:
- `-f, --config <CONFIG_YAML>` Path to the backend configuration YAML file.

Examples:
```bash
vhost-backend --config config.yaml
```

## Configuration File Format

The backend configuration YAML must match the `Options` struct fields:

```yaml
path: "/path/to/block-device.raw"        # String: base disk image path
image_path: "/path/to/ubi-image.raw"     # Optional String: UBI image for lazy fetch
socket: "/tmp/vhost.sock"                # String: vhost‐user socket path
num_queues: 4                            # Integer: number of virtqueues
queue_size: 256                          # Integer: size of each virtqueue
seg_size_max: 4096                       # Integer: max IO segment size (bytes)
seg_count_max: 1                         # Integer: max segments per IO
poll_queue_timeout_us: 500               # Integer: poll timeout in microseconds
encryption_key:                          # Optional: AES‐XTS keys (hex strings)
  - "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
  - "fedcba9876543210fedcba9876543210fedcba9876543210fedcba9876543210"
```
