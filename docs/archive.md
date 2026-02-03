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
- `--kek` (`-k`): Path to the key encryption key file.
- `--unlink-kek` (`-u`): Delete the KEK file after use.
- `--encrypt` (`-e`): Encrypt archived stripes with a random AES-XTS key.
- `--compress` (`-c`): Compress archived stripes with Snappy before optional encryption.

**Target config format:**
```yaml
type: filesystem
path: "/var/ubiblk/archive"
archive_kek:
  method: "aes256-gcm"
  key: "wHKSFBsRXW/VPLsJKl/mnsMs7X3Pt8NWjzZkch8Ku60="
  init_vector: "UEt+wI+Ldq1UgQ/P"
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
  init_vector: "UEt+wI+Ldq1UgQ/P"
  auth_data: "dm0zamdlejhfMA=="
```

**Examples:**
```bash
# Archive to a local directory
archive -f config.yaml --target-config archive_target.yaml

# Archive to S3 with a prefix
archive -f config.yaml --target-config archive_target.yaml
```

## Archive format

Archives consist of a `metadata.json` file, a `stripe-hashes.json` mapping
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
  "compression": "snappy"
}
```

`stripe_sector_count` indicates the number of 512-byte sectors per stripe. When
`--encrypt` is enabled, the two keys stored in `encryption_key` are encrypted
with the KEK (if provided) before being base64 encoded; otherwise,
`encryption_key` is `null`. The `compression` field records the algorithm used
to store stripe payloads.

### `stripe-hashes.json`

The stripe hash map stores the SHA-256 hash for every archived stripe index.
Stripe indices that were skipped are absent from the map.

```json
{
  "0": "7ab2d7cbb0c4e0e1e8fe2a5f7a8f1b5b56c2b7f8d4022ec3e6f4c3e8b1f66f33",
  "5": "7ab2d7cbb0c4e0e1e8fe2a5f7a8f1b5b56c2b7f8d4022ec3e6f4c3e8b1f66f33",
  "7": "2f1c5d6c2cceaa1c6bbd2a0e8a3bb5b5b3dd44cb1a25d2f11f0e0a533b7e3f7c"
}
```


### Stripe objects

Each archived stripe payload is stored as its own object with the following key
format:

```
data/<sha256 hash>
```

The content is the raw stripe payload, optionally compressed, then optionally
encrypted. The SHA-256 hash is computed on the stored bytes (after compression
and encryption). Consumers verify the hash, decrypt if needed, and then
decompress if needed before returning the stripe.
