# Remote Stripe Server

The remote stripe tooling lets a ubiblk backend fetch stripes from a remote
server over TCP.

## Components

### `remote-stripe-server`

Serves stripes from a local ubiblk block device and responds to requests from
remote clients.

```bash
remote-stripe-server --config <CONFIG_TOML> --listen-config <LISTEN_CONFIG_TOML>
```

| Flag | Short | Required | Description |
|------|-------|----------|-------------|
| `--config` | `-f` | yes | Path to the ubiblk config TOML (see [config.md](config.md)) |
| `--listen-config` | — | yes | Path to the server/listen config TOML |

The server requires that all source stripes have been fetched before it will
start (verified via metadata).

### `remote-stripe-shell`

An interactive client for exploring a remote stripe server.

```bash
remote-stripe-shell --server-config <SERVER_CONFIG_TOML>
```

| Flag | Short | Required | Description |
|------|-------|----------|-------------|
| `--server-config` | — | yes | Path to the server config TOML |

**Shell commands:**

| Command | Description |
|---------|-------------|
| `help` | Show command list |
| `exit` / `quit` | Exit the shell |
| `stripe_header <stripe_index>` | Display the header byte and written status |
| `fetch_stripe <stripe_index>` | Fetch the stripe from the server and cache it locally |
| `dump_stripe <stripe_index> <offset> <length>` | Print hex data from a cached stripe |

`dump_stripe` behaviour for edge cases:
- **Unwritten stripe:** returns zero bytes for the requested range.
- **Written but not yet fetched:** returns `NOT_FETCHED_FROM_REMOTE`.
- **Out of range:** returns `INVALID_STRIPE` or `INVALID_RANGE`.

## Server/Listen Config Reference

Both `remote-stripe-server` (`--listen-config`) and `remote-stripe-shell`
(`--server-config`) load the same config format via
`RemoteStripeServerConfig::load`. It supports the include system (see
[config.md](config.md#include-system)).

### Sections

| Section | Required | Description |
|---------|----------|-------------|
| `[server]` | yes | Remote connection settings |
| `[secrets.*]` | no | Named secret definitions |
| `[danger_zone]` | no | Safety overrides |

No other top-level keys are allowed.

### `[server]`

```toml
[server]
address = "127.0.0.1:4555"
autofetch = false

[server.psk]
identity = "client1"
secret.ref = "remote-psk"

[secrets.remote-psk]
source.env = "UBIBLK_REMOTE_PSK"
```

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `address` | string | yes | — | Listen/connect address (`host:port`) |
| `autofetch` | boolean | no | false | Fetch stripes in the background |
| `psk.identity` | string | yes* | — | TLS-PSK identity string |
| `psk.secret.ref` | string | yes* | — | Reference to a PSK secret (must be at least 16 bytes) |

\* PSK is required unless both `danger_zone.enabled = true` and
`danger_zone.allow_unencrypted_connection = true` are set:

```toml
[danger_zone]
enabled = true
allow_unencrypted_connection = true
```

This is a deliberate design choice to avoid accidental unencrypted connections.

### `[secrets.*]` and `[danger_zone]`

These sections use the same format as the main ubiblk config. See
[config.md](config.md#secrets) and [config.md](config.md#danger_zone) for
details.

## Remote Stripe Protocol

The protocol is a simple request/response exchange over TCP. The server only
handles one command at a time on a connection. All multi-byte integers are
little-endian.

### Optional TLS-PSK

If PSK credentials are supplied, the connection is wrapped in TLS using the
`PSK-AES256-GCM-SHA384` cipher suite.

### Metadata Request

**Client -> Server**

| Field | Size | Description |
|-------|------|-------------|
| opcode | 1 byte | `0x00` (`METADATA_CMD`) |

**Server -> Client**

| Field | Size | Description |
|-------|------|-------------|
| status | 1 byte | `0x00` (`STATUS_OK`) or error status |
| metadata_size | 8 bytes | Size of metadata blob in bytes |
| metadata | N bytes | Serialized `UbiMetadata` blob |

The client must request metadata before issuing stripe reads.

### Stripe Read Request

**Client -> Server**

| Field | Size | Description |
|-------|------|-------------|
| opcode | 1 byte | `0x01` (`READ_STRIPE_CMD`) |
| stripe_index | 8 bytes | Stripe index (u64) |

**Server -> Client (success)**

| Field | Size | Description |
|-------|------|-------------|
| status | 1 byte | `0x00` (`STATUS_OK`) |
| stripe_size | 8 bytes | Stripe size in bytes |
| stripe_data | N bytes | Stripe payload |

**Server -> Client (error)**

| Status byte | Meaning |
|-------------|---------|
| `0x01` (`STATUS_INVALID_STRIPE`) | Stripe index is out of range |
| `0x02` (`STATUS_NO_DATA`) | Stripe exists but does not contain data |
| `0x03` (`STATUS_NOT_FETCHED`) | Stripe exists in source but has not been fetched yet |
| `0xFE` (`STATUS_INVALID_COMMAND`) | Unknown opcode |
| `0xFF` (`STATUS_SERVER_ERROR`) | Internal server error |

The server determines whether a stripe has data by inspecting the metadata
header bits. Stripes that do not contain data return `STATUS_NO_DATA` and no
payload. Stripes that exist in the source but have not been fetched yet return
`STATUS_NOT_FETCHED` and no payload.
