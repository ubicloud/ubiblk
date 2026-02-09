# ubitop

Real-time per-queue throughput monitor for ubiblk devices.

## Prerequisites

- Python 3
- `pip install rich`

## Usage

```
scripts/ubitop --socket /path/to/rpc.sock [--interval 1]
```

| Flag | Description |
|------|-------------|
| `--socket PATH` | Path to the ubiblk RPC Unix socket (required) |
| `--interval SECS` | Poll interval in seconds (default: 1) |

## Enabling the RPC socket

Set `rpc_socket_path` in the device configuration:

```yaml
rpc_socket_path: "/run/ubiblk/mydev.sock"
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
