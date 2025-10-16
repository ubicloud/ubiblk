# Remote Block Device Protocol

When a client connects, the server sends the image metadata. Then the client
can request stripes. For each stripe request, the server responds with a
status byte followed by the stripe data if the request was successful. If
TLS/PSK is enabled the handshake is completed before the metadata preamble is
transmitted.

## Metadata exchange

Immediately after the transport is ready (plain TCP or a successful TLS
handshake) the server sends the image metadata:

```
struct MetadataPreamble {
    metadata_len: u32,              // little-endian
    metadata_bytes: [u8; metadata_len]
}
```

`metadata_bytes` is the byte-for-byte serialisation produced by
`UbiMetadata::write_to_buf`. Among other fields, this contains information about
stripe size, and stripe headers.

## Stripe read request

The client only issues read requests that align to stripe boundaries and span
exactly one stripe.  Each request has the following layout:

```
struct StripeReadRequest {
    opcode: u8 = 0x01,
    stripe_id: u64,                 // little-endian
}
```

### Responses

The server answers each request with a single status byte followed by the
stripe payload when the request succeeded:

```
struct StripeReadResponse {
    status: u8,
    payload: [u8; stripe_size_bytes]? // present only when status == 0x00
}
```

Status codes:

* `0x00` – success; `payload` holds `stripe_size_bytes` bytes.
* `0x01` – invalid stripe identifier; no payload is sent.
* `0x02` – stripe not marked as written in the metadata; no payload is sent.
* `0xFF` – internal server error.

The client treats any non-zero status as an I/O error.

## Typical exchange

1. Client connects and receives metadata (`MetadataPreamble`).
2. Client validates the metadata and caches it.
3. For each read aligned to a stripe boundary:
   1. Check the metadata.  If the stripe is not marked as written, return a
      zeroed buffer without using the network.
   2. Otherwise send `StripeReadRequest` and wait for the response.
   3. On status `0x00`, copy the payload into the caller's buffer.  Any other
      status terminates the request with an error.
4. The connection is closed when the client drops the I/O channel.

