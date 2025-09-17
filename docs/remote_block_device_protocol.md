# Remote Block Device Protocol

This document specifies the lightweight protocol used by the read-only
network block device backend introduced in this repository.  The protocol is
intentionally minimal and optimised for fetching whole stripes, which matches
how the client block device operates.

## Transport

* Transport: TCP
* Character encoding: binary (little-endian integer encoding)
* The client initiates the TCP connection.

Every connection is independent.  The server replays the metadata at the start
of each connection so that clients can validate that they are operating against
the expected image.  The client caches the metadata from the first connection
and compares subsequent copies to detect changes.

## Metadata exchange

Immediately after the TCP connection is established the server sends the image
metadata:

```
struct MetadataPreamble {
    metadata_len: u32,              // little-endian
    metadata_bytes: [u8; metadata_len]
}
```

`metadata_bytes` is the byte-for-byte serialisation produced by
`UbiMetadata::write_to_buf`.  The payload uses the same layout as the local
UBI-style metadata:

* `magic` must equal `BDEV_UBI\0`.
* `version_major` and `version_minor` allow the layout to evolve.
* `stripe_sector_count_shift` defines the number of sectors per stripe as
  `1 << shift`.
* `stripe_headers` is one byte per stripe.  Bit 0 indicates whether the stripe
  has been fetched and bit 1 indicates whether the stripe contains valid data.

The client parses the metadata and computes the total sector count and stripe
size.  If the metadata is invalid or does not match what the client already
knows it aborts the connection.

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

## Client behaviour

The read-only block device consults the cached metadata before contacting the
remote server.  When bit 1 of the targeted stripe header is not set the client
skips the network request entirely and returns a zero-filled buffer.  This
behaviour mirrors the lazy-fetch logic used locally for sparse images while
ensuring that unwritten stripes are never requested from the server.

When bit 1 is set the client sends a `StripeReadRequest` and expects exactly
`stripe_size_bytes` bytes in response.  Any deviation (wrong status code,
short read, or I/O error) causes the read request to fail.

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

This protocol keeps the server simple while allowing clients to avoid needless
network round-trips for sparse regions of the image.
