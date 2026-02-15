# ubitop

Real-time per-queue throughput monitor for ubiblk devices.

## Prerequisites

- Python 3
- `pip install rich`

## Usage

```bash
scripts/ubitop --socket <SOCKET_PATH> [--interval <SECONDS>]
```

| Flag | Short | Required | Description |
|------|-------|----------|-------------|
| `--socket` | — | yes | Path to the ubiblk RPC Unix socket |
| `--interval` | — | no | Poll interval in seconds (default: 1) |

## Enabling the RPC socket

Set `rpc_socket` in the device configuration:

```toml
[device]
rpc_socket = "/run/ubiblk/mydev.sock"
```

## RPC protocol

ubitop communicates over a Unix domain socket using newline-delimited JSON.

**Request:**

```json
{"command": "stats"}
```

**Response:**

```json
{
  "stats": {
    "queues": [
      {
        "bytes_read": 4096,
        "bytes_written": 8192,
        "read_ops": 1,
        "write_ops": 1,
        "flush_ops": 1
      }
    ]
  }
}
```

Each queue reports cumulative counters. ubitop computes throughput rates by
diffing consecutive snapshots.
