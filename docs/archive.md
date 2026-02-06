# Archive tooling and format

The `archive` binary captures stripes from a ubiblk block device and stores them
in either a local directory or an S3-compatible object store.

**Usage:**
```bash
archive --config <CONFIG_YAML> --target-config <TARGET_CONFIG_YAML> [options]
```

**Required inputs:**
- `--config` (`-f`): ubiblk configuration YAML.
- `--target-config`: Archive target configuration YAML (filesystem or S3).

**Options:**
- `--kek` (`-k`): Path to the key encryption key file. It's recommended to use a
  named pipe or `/dev/stdin` for this. Regular files are disallowed by default
  to prevent accidental exposure of KEK material.
- `--allow-regular-file-as-kek`: Allow reading the KEK from a regular file.
- `--encrypt` (`-e`): Encrypt archived stripes with a random AES-XTS key.
- `--compression`: Compression algorithm (`none`, `snappy`, or `zstd`). Defaults to `none`.
- `--zstd-level`: Zstd compression level. Defaults to `3`.

**Target config format:**
```yaml
type: filesystem
path: "/var/ubiblk/archive"
archive_kek:
  method: "aes256-gcm"
  key: "wHKSFBsRXW/VPLsJKl/mnsMs7X3Pt8NWjzZkch8Ku60="
  auth_data: "dm0zamdlejhfMA=="
```

```yaml
type: s3
bucket: "my-bucket"
prefix: "ubiblk"                       # Optional: prefix inside the bucket
endpoint: "https://s3.example.com"     # Optional: custom S3 endpoint
region: "auto"                         # Optional: AWS region
profile: "r2"                          # Optional: aws-cli profile name
credentials:                           # Optional: KEK-encrypted credentials
  access_key_id: "BASE64-ENCODED-ACCESS-KEY-ID"
  secret_access_key: "BASE64-ENCODED-SECRET-ACCESS-KEY"
connections: 16                        # Optional: number of connections
archive_kek:
  method: "aes256-gcm"
  key: "wHKSFBsRXW/VPLsJKl/mnsMs7X3Pt8NWjzZkch8Ku60="
  auth_data: "dm0zamdlejhfMA=="
```

> **Note:** KEK-encrypted values must use the current format:
> `[12-byte nonce || ciphertext || 16-byte tag]`. Older ciphertexts that omit
> the nonce prefix are not supported.

**Examples:**
```bash
# Archive to a local directory
archive -f config.yaml --target-config archive_target.yaml

# Archive to S3 with a prefix
archive -f config.yaml --target-config archive_target.yaml

# Archive with zstd compression (level 3)
archive -f config.yaml --target-config archive_target.yaml --compression zstd --zstd-level 3
```

## Archive format

Archives consist of a `metadata.json` file, a `stripe-mapping` mapping
file, and one data object per unique stripe payload. Only stripes which contain
data are archived. That is:

- Either the stripe had data written to it.
- Or the stripe had data in the disk's stripe source.

### `metadata.json`

The metadata file stores the stripe layout and, optionally, encrypted keys for
encrypted archives. It also includes a required format version that readers use
to validate compatibility.

```json
{
  "format_version": 1,
  "stripe_sector_count": 2048,
  "encryption_key": [
    "<BASE64-ENCODED-KEY-1>",
    "<BASE64-ENCODED-KEY-2>"
  ],
  "compression": {
    "zstd": {
      "level": 3
    }
  },
  "hmac_key": "<BASE64-ENCODED-ENCRYPTED-HMAC-KEY>"
}
```

`stripe_sector_count` indicates the number of 512-byte sectors per stripe. When
`--encrypt` is enabled, the two keys stored in `encryption_key` are encrypted
with the KEK (if provided) before being base64 encoded; otherwise,
`encryption_key` is `null`. The `compression` field records the algorithm used
to store stripe payloads. For `none` and `snappy`, this is a string value.
For zstd, this is an object containing the configured compression level.
The `level` field is required when `compression` is `zstd`.
`hmac_key` stores a KEK-encrypted HMAC key used to authenticate
`stripe-mapping`.

### `stripe-mapping`

The stripe mapping stores a content descriptor for every archived stripe index.
Stripe indices that are not archived are absent from the map. These include
stripes that don't exist in the stripe source and are never written to.

The mapping is encoded as CBOR. Each stripe entry is either `Zero` (an all-zero
stripe, with no stripe object stored) or `Some`, containing a 32-byte SHA-256
digest of the **stored stripe bytes** (computed after compression and optional
encryption).

The CBOR mapping is padded to a 512-byte sector size and stored together with
the original plaintext length. When archive encryption is enabled, the padded
bytes are encrypted using AES-XTS before storage; when encryption is disabled,
the stored bytes are the padded plaintext.

An HMAC tag is included with the file and verified on read. The HMAC is computed
over:

```
domain || version || plaintext_len || ciphertext
```

where:
- `domain` is a fixed ASCII string identifying the archive stripe-mapping HMAC;
- `version` is encoded as a 4-byte little-endian unsigned integer (`u32`);
- `plaintext_len` is encoded as an 8-byte little-endian unsigned integer (`u64`);
- `ciphertext` is the full encrypted (or, if encryption is disabled, padded plaintext) CBOR mapping bytes.

This authenticates the stripe mapping and detects any corruption or tampering
before the mapping is parsed or trusted.

### Stripe objects

Each archived stripe payload is stored as its own object under
`data/<sha256 hash>`. The SHA-256 hash is computed on the stored stripe bytes
(after compression and optional encryption). Consumers verify the hash before
decrypting (if needed) and decompressing (if needed) before returning the
stripe.
