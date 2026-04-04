# RPC Commands

When `rpc_socket` is configured, the backend accepts newline-delimited JSON
requests on the Unix socket and returns one JSON object per line.

## Request format

All requests use the same shape:

```json
{"command": "<name>"}
```

## `version`

Returns the backend version.

**Request**

```json
{"command": "version"}
```

**Output spec**

- Top-level object with:
  - `version` (string): backend version string.

**Example response**

```json
{"version":"0.1.0"}
```

## `status`

Returns the background worker status report.

**Request**

```json
{"command": "status"}
```

**Output spec**

- Top-level object with:
  - `status` (object or `null`):
    - `null` when no background worker is active.
    - Otherwise, a status object from the backend reporter.

**Example response**

```json
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

## `queues`

Returns a per-queue snapshot of recently observed I/O activity.

**Request**

```json
{"command": "queues"}
```

**Output spec**

- Top-level object with:
  - `queues` (array): one entry per queue.
    - Each queue entry is an array of I/O events.
    - Event shapes:
      - `["read", offset, length]`
      - `["write", offset, length]`
      - `["flush"]`

**Example response**

```json
{
  "queues": [
    [
      ["read", 0, 4096],
      ["write", 8192, 4096],
      ["flush"]
    ],
    [
      ["read", 16384, 4096]
    ]
  ]
}
```

## `stats`

Returns cumulative counters for each queue.

**Request**

```json
{"command": "stats"}
```

**Output spec**

- Top-level object with:
  - `stats` (object):
    - `queues` (array): one object per queue, each containing:
      - `bytes_read` (u64)
      - `bytes_written` (u64)
      - `read_ops` (u64)
      - `write_ops` (u64)
      - `flush_ops` (u64)

**Example response**

```json
{
  "stats": {
    "queues": [
      {
        "bytes_read": 4096,
        "bytes_written": 8192,
        "read_ops": 1,
        "write_ops": 2,
        "flush_ops": 1
      }
    ]
  }
}
```

## Unknown command handling

If `command` is not recognized, the backend returns an error object.

**Example response**

```json
{"error":"unknown command: destroy_world"}
```
