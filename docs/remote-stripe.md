# Remote stripe server and protocol

The remote stripe tooling lets a ubiblk backend fetch stripes from a remote
server over TCP.

## Components

### `remote-stripe-server`

`remote-stripe-server` serves stripes from a local ubiblk block device and
responds to requests from remote clients.

**Usage:**
```bash
remote-stripe-server --config <CONFIG_YAML> --listen-config <LISTEN_CONFIG_YAML> \
  [--kek <KEK_PATH>] [--allow-regular-file-as-kek]
```

**Notes:**
- `--listen-config` supplies the bind address and optional PSK credentials.

### `remote-stripe-shell`

`remote-stripe-shell` is an interactive client for exploring a remote stripe
server.

**Usage:**
```bash
remote-stripe-shell --server-config <SERVER_CONFIG_YAML> \
  [--kek <KEK_PATH>] [--allow-regular-file-as-kek]
```

It's recommended to use a named pipe or `/dev/stdin` for KEK path. Regular files
are disallowed by default to prevent accidental exposure of KEK material.

### Listen/Server config format

The listen and server config YAML files use the same fields as the
`stripe_source: remote` configuration, but without the `source` key. Secrets
are encrypted using the KEK if provided.

```yaml
address: "127.0.0.1:4555"
psk_identity: "client1"
psk_secret: "<base64-encoded-secret>" # Optional: KEK-encrypted PSK secret
allow_insecure: false                 # Required to be true for unencrypted connections (default: false)
```

`psk_identity` and `psk_secret` must be set together to enable TLS-PSK. If
allow_insecure is false (the default), then `psk_identity` and `psk_secret` must
be provided.

This is a deliberate design choice to avoid accidental unencrypted connections.

**Commands:**
- `help` – show command list.
- `exit | quit` – exit the shell.
- `stripe_header <stripe_index>` – display the header byte and written status.
- `fetch_stripe <stripe_index>` – fetch the stripe from the server and cache it.
- `dump_stripe <stripe_index> <offset> <length>` – print hex data from the
  cached stripe. If the stripe is unwritten, the shell returns zero bytes for
  the requested range. For written stripes that have not been fetched, the shell
  returns `NOT_FETCHED_FROM_REMOTE`.

## Remote stripe protocol

The protocol is a simple request/response exchange over TCP. The server only
handles one command at a time on a connection. All multi-byte integers are
little-endian.

### Optional TLS-PSK

If PSK credentials are supplied, the connection is wrapped in TLS using the
`PSK-AES256-GCM-SHA384` cipher suite.

### Metadata request

**Client → Server**

| Field | Size | Description |
| --- | --- | --- |
| opcode | 1 byte | `0x00` (`METADATA_CMD`) |

**Server → Client**

| Field | Size | Description |
| --- | --- | --- |
| status | 1 byte | `0x00` (`STATUS_OK`) or error status |
| metadata_size | 8 bytes | Size of metadata blob in bytes |
| metadata | N bytes | Serialized `UbiMetadata` blob |

The client must request metadata before issuing stripe reads.

### Stripe read request

**Client → Server**

| Field | Size | Description |
| --- | --- | --- |
| opcode | 1 byte | `0x01` (`READ_STRIPE_CMD`) |
| stripe_index | 8 bytes | Stripe index (u64) |

**Server → Client (success)**

| Field | Size | Description |
| --- | --- | --- |
| status | 1 byte | `0x00` (`STATUS_OK`) |
| stripe_size | 8 bytes | Stripe size in bytes |
| stripe_data | N bytes | Stripe payload |

**Server → Client (error)**

| Status byte | Meaning |
| --- | --- |
| `0x01` (`STATUS_INVALID_STRIPE`) | Stripe index is out of range. |
| `0x02` (`STATUS_NO_DATA`) | Stripe exists but does not contain data. |
| `0x03` (`STATUS_NOT_FETCHED`) | Stripe also exists in source, but has not been fetched yet. |
| `0xFE` (`STATUS_INVALID_COMMAND`) | Unknown opcode. |
| `0xFF` (`STATUS_SERVER_ERROR`) | Internal server error. |

The server determines whether a stripe has data by inspecting the metadata
header bits. Stripes that do not contain data return `STATUS_NO_DATA` and no payload. Stripes that exist in the source but have not been fetched yet return `STATUS_NOT_FETCHED` and no payload.
