# Archive

The `archive` binary captures stripes from a ubiblk block device and stores them
in either a local directory or an S3-compatible object store.

## Usage

```bash
archive --config <CONFIG_TOML> --target-config <TARGET_CONFIG_TOML> [options]
```

| Flag | Short | Required | Description |
|------|-------|----------|-------------|
| `--config` | `-f` | yes | Path to the ubiblk config TOML (see [config.md](config.md)) |
| `--target-config` | — | yes | Path to the archive target config TOML |
| `--encrypt` | `-e` | no | Encrypt archived stripes with a random AES-XTS key |
| `--compression` | — | no | Compression algorithm: `none` (default) or `zstd` |
| `--zstd-level` | — | no | Zstd compression level, 1–22 (default: 3) |

The ubiblk config (`--config`) must include a `metadata_path` in `[device]`.

**Examples:**
```bash
# Archive to a local directory
archive -f config.toml --target-config archive_target.toml

# Archive with encryption
archive -f config.toml --target-config archive_target.toml --encrypt

# Archive with zstd compression (level 5)
archive -f config.toml --target-config archive_target.toml --compression zstd --zstd-level 5
```

## Target Config Reference

The target config is a standalone Config v2 TOML file loaded by
`ArchiveTargetConfig::load`. It supports the include system (see
[config.md](config.md#include-system)).

### Sections

| Section | Required | Description |
|---------|----------|-------------|
| `[target]` | yes | Archive storage backend |
| `[secrets.*]` | no | Named secret definitions |
| `[danger_zone]` | no | Safety overrides |

No other top-level keys are allowed.

### `[target]` — Filesystem

A local directory as the archive backend. Discriminated by `storage = "filesystem"`.

```toml
[target]
storage = "filesystem"
path = "/var/ubiblk/archive"
archive_kek.ref = "archive-kek"

[secrets.archive-kek]
source.env = "UBIBLK_ARCHIVE_KEK"
```

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `storage` | string | yes | Must be `"filesystem"` |
| `path` | path | yes | Directory to store archive objects |
| `archive_kek.ref` | string | no | Reference to a 32-byte AES-256-GCM KEK secret |
| `autofetch` | boolean | no | Fetch stripes in the background (default: false) |

### `[target]` — S3

An S3-compatible object store. Discriminated by `storage = "s3"`.

```toml
[target]
storage = "s3"
bucket = "my-bucket"
prefix = "ubiblk/"
region = "auto"
endpoint = "https://s3.example.com"
connections = 16
access_key_id.ref = "s3-access-key-id"
secret_access_key.ref = "s3-secret-access-key"
session_token.ref = "s3-session-token"      # optional
archive_kek.ref = "archive-kek"

[secrets.s3-access-key-id]
source.env = "UBIBLK_S3_ACCESS_KEY_ID"

[secrets.s3-secret-access-key]
source.env = "UBIBLK_S3_SECRET_ACCESS_KEY"

[secrets.archive-kek]
source.env = "UBIBLK_ARCHIVE_KEK"
```

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `storage` | string | yes | — | Must be `"s3"` |
| `bucket` | string | yes | — | S3 bucket name |
| `prefix` | string | no | — | Key prefix (must not contain `.` or `..` path components) |
| `region` | string | no | — | AWS region |
| `endpoint` | string | no | — | Custom S3 endpoint URL |
| `connections` | integer | no | 16 | Number of S3 connections (must be > 0) |
| `access_key_id.ref` | string | yes | — | Reference to AWS access key ID secret |
| `secret_access_key.ref` | string | yes | — | Reference to AWS secret access key secret |
| `session_token.ref` | string | no | — | Reference to AWS session token secret (for temporary credentials) |
| `archive_kek.ref` | string | no | — | Reference to a 32-byte AES-256-GCM KEK secret |
| `autofetch` | boolean | no | false | Fetch stripes in the background |

### `[secrets.*]` and `[danger_zone]`

These sections use the same format as the main ubiblk config. See
[config.md](config.md#secrets) and [config.md](config.md#danger_zone) for
details.

> **Note:** The archive KEK must be exactly 32 bytes. KEK-encrypted values use
> AES-256-GCM with AAD set to the fixed ASCII string `"ubiblk_archive"`, and
> ciphertext is encoded as `[12-byte nonce || ciphertext || 16-byte GCM tag]`.

## Archive Format

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
  "encryption_key": "<BASE64-ENCODED-64-BYTE-XTS-KEY>",
  "compression": {
    "zstd": {
      "level": 3
    }
  },
  "hmac_key": "<BASE64-ENCODED-ENCRYPTED-HMAC-KEY>",
  "metadata_hmac": "<BASE64-ENCODED-HMAC-TAG>"
}
```

`stripe_sector_count` indicates the number of 512-byte sectors per stripe. When
`--encrypt` is enabled, the 64-byte XTS key stored in `encryption_key` is
encrypted with the archive KEK before being base64 encoded; otherwise,
`encryption_key` is `null`. The `compression` field records the algorithm used
to store stripe payloads. For `none`, this is a string value.
For zstd, this is an object containing the configured compression level.
The `level` field is required when `compression` is `zstd`.
`hmac_key` stores a KEK-encrypted HMAC key used to authenticate
`stripe-mapping`. `metadata_hmac` stores a 32-byte HMAC-SHA256 tag that
authenticates selected metadata fields (`format_version`,
`stripe_sector_count`, `encryption_key`, and `compression`) using a domain-
separated input (`ARCHIVE_METADATA_HMAC_V1`).

Before trusting any metadata fields, readers verify `metadata_hmac` using
`hmac_key`. This prevents tampering with archive parameters such as the stripe
layout, compression mode, or encrypted archive key.

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

### Stripe Objects

Each archived stripe payload is stored as its own object under
`data/<sha256 hash>`. The SHA-256 hash is computed on the stored stripe bytes
(after compression and optional encryption). Consumers verify the hash before
decrypting (if needed) and decompressing (if needed) before returning the
stripe.
