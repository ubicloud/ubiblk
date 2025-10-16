# Remote block device TLS setup

The remote block device server and clients can optionally protect traffic with
TLS 1.3 using a pre-shared key (PSK). This mode avoids certificate management
and relies on an out-of-band trusted channel to distribute the PSK.

## Generate a PSK

Keys are provided as hexadecimal strings with no whitespace. The server and all
clients must share the same key and identity. Generate a 32-byte random key and
store it in a file:

```bash
head -c 32 /dev/urandom | xxd -p -c 32 > tls-psk.hex
```

* The resulting file must contain only hexadecimal characters (upper- or
  lower-case) and must be at least 64 characters (32 bytes) long.
* Keep the file secret. Distribute it to trusted clients alongside the PSK
  identity string.

Choose an ASCII PSK identity (for example, `ubiblk-prod`) without embedded NUL
bytes.

## Server configuration

Start `remote-bdev-server` with the new TLS options:

```bash
remote-bdev-server \
    --bind 0.0.0.0:4555 \
    --config /path/to/ubiblk.yaml \
    --tls-psk-identity ubiblk-prod \
    --tls-psk-key /path/to/tls-psk.hex
```

The configuration file must reference the metadata and data files that the
server will expose and omit `image_path`.

If `--tls-psk-identity`/`--tls-psk-key` are omitted the server continues to use
plain TCP.

## vhost-user backend configuration

Add the new fields to the YAML configuration used by `ubiblk-vhost-backend`:

```yaml
remote-image-address: 203.0.113.42:4555
remote-tls-psk-identity: ubiblk-prod
remote-tls-psk-key-path: /path/to/tls-psk.hex
```

`remote-tls-psk-identity` and `remote-tls-psk-key-path` must either both be
present or both omitted. The key path must point to the same hex-encoded file
that the server uses.

## remote-shell

`remote-shell` understands the same TLS options:

```bash
remote-shell 203.0.113.42:4555 \
    --tls-psk-identity ubiblk-prod \
    --tls-psk-key /path/to/tls-psk.hex
```

When the options are omitted the shell connects over plain TCP.

## Notes

* TLS uses only IP addresses, no DNS names or certificates.
* Handshakes require the identity and PSK to match exactly; otherwise the
  connection is rejected.
* Keys are read once during start-up. Restart the server and clients after
  rotating the PSK.
