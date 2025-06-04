# vhost-frontend

The `vhost-frontend` utility connects to a vhost-user-blk backend and provides various
operations for interacting with the block device. It can run a single stage or the
whole sequence of steps involved in setting up a frontend and copying data from
the device.

## Usage

```bash
vhost-frontend --socket <SOCKET_PATH> [--output <OUTPUT_FILE>] [--stage <STAGE>]
```

## Arguments

- `-s, --socket <SOCKET_PATH>`: Path to the vhost-user socket (required).
- `-o, --output <OUTPUT_FILE>`: Path to the output file (required for the `copy` stage).
- `--stage <STAGE>`: Execution stage to run (default: `4`).

## Stages

The `--stage` argument selects a stage in the frontend initialisation process:

| Value | Name      | Description                                   |
|-------|-----------|-----------------------------------------------|
| 0     | setup     | Connect to the socket and perform setup       |
| 1     | config    | Read and display device configuration         |
| 2     | memory    | Allocate and set up device memory             |
| 3     | virtqueue | Set up the virtqueue for device communication |
| 4     | copy      | Copy data from the device to the output file  |

`--stage` accepts either the numeric value or the name of the stage.

## Examples

Connect to a vhost-user socket and display the device configuration:

```bash
vhost-frontend --socket /tmp/vhost.sock --stage config
```

Copy data from a block device to a file:

```bash
vhost-frontend --socket /tmp/vhost.sock --output disk.img
```

Set up the virtqueue without copying data:

```bash
vhost-frontend --socket /tmp/vhost.sock --stage virtqueue
```
