# ublk-backend

This utility launches a ublk userspace block device using a YAML
configuration file. It relies on the [`libublk`](https://crates.io/crates/libublk)
crate and the block device implementations already present in `ubiblk`.

## Building

```bash
cargo build --bin ublk-backend
```

## Example configuration

Create `config.yaml` with the following minimal options:

```yaml
path: /path/to/backing/file
socket: /dev/null # required by the existing schema but unused
queue_size: 64
num_queues: 1
seg_size_max: 65536
seg_count_max: 4
direct_io: true
sync_io: false
```

`path` points to a regular file or block device that backs the exported
ublk device. The `socket` field is ignored but required to satisfy the
existing configuration schema.

## Running

Load the kernel module and start the backend:

```bash
sudo modprobe ublk_drv
sudo target/debug/ublk-backend --config config.yaml
```

A new device `/dev/ublkbN` will appear once the backend starts. Replace
`target/debug` with `target/release` after building with `--release`.
