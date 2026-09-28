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

## `start_autofetch`

Turns on background stripe fetching for a lazily fetched device that was
started with `autofetch = false`. The background worker queues every stripe
the source has. Stripes already fetched are skipped, so the request is safe
on a device that has been serving reads on demand, and repeating it is a
no-op. This lets a device start without catch-up competing with the guest for
the disk, and turn catch-up on once the workload is up.

The response only confirms that the request reached the background worker.
Track progress with `status`.

**Request**

```json
{"command": "start_autofetch"}
```

**Output spec**

- Top-level object with:
  - `autofetch` (string): `"requested"` once the request has been handed to
    the background worker.
- On failure, an error object with:
  - `error` (string): the device has no background worker (no stripe source
    is configured), or the worker has already stopped.

**Example response**

```json
{"autofetch":"requested"}
```

**Example error responses**

```json
{"error":"no background worker (no stripe source)"}
```

```json
{"error":"background worker is not running"}
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
