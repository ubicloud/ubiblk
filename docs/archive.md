# Archive tooling and format

The `archive` binary captures stripes from a ubiblk block device and stores them
in either a local directory or an S3-compatible object store.

**Usage:**
```bash
archive --config <CONFIG_YAML> --target <PATH|S3_URI> [options]
```

**Required inputs:**
- `--config` (`-f`): ubiblk configuration YAML.
- `--target` (`-t`): Local path or `s3://bucket[/prefix]` destination.

**Options:**
- `--kek` (`-k`): Path to the key encryption key file.
- `--unlink-kek` (`-u`): Delete the KEK file after use.
- `--encrypt` (`-e`): Encrypt archived stripes with a random AES-XTS key.
- `--endpoint`: Custom S3 endpoint (e.g. Cloudflare R2).
- `--access-key-id` / `--secret-access-key`: Base64-encoded (possibly KEK-
  encrypted) credentials for S3 access. Both must be provided together.
- `--region`: S3 region string (for example `auto`).
- `--profile`: AWS profile name to use for credentials.

**Examples:**
```bash
# Archive to a local directory
archive -f config.yaml -t /var/ubiblk/archive

# Archive to S3 with a prefix
archive -f config.yaml -t s3://my-bucket/ubiblk

# Archive to Cloudflare R2 with a custom endpoint
archive -f config.yaml -t s3://my-r2-bucket/ubiblk --profile r2 \
  --endpoint https://<account>.r2.cloudflarestorage.com
```

## Archive format

Archives consist of a `metadata.yaml` file and one object per stripe. Only
stripes which contain data are archived. That is:

- Either the stripe had data written to it.
- Or the stripe had data in the disk's stripe source.

### `metadata.yaml`

The metadata file stores the stripe layout and, optionally, encrypted keys for
encrypted archives.

```yaml
stripe_sector_count: 2048
# When encryption is enabled, two KEK-encrypted AES-XTS keys are recorded as
# base64 strings. When disabled, this field is null.
encryption_key:
  - <BASE64-ENCODED-KEY-1>
  - <BASE64-ENCODED-KEY-2>
```

`stripe_sector_count` indicates the number of 512-byte sectors per stripe. When
`--encrypt` is enabled, the two keys stored in `encryption_key` are encrypted
with the KEK (if provided) before being base64 encoded.

### Stripe objects

Each archived stripe is stored as its own object with the following key
format:

```
stripe_<10-digit stripe index>_<sha256 hash>
```

For example:
```
stripe_0000000042_7ab2d7cbb0c4e0e1e8fe2a5f7a8f1b5b56c2b7f8d4022ec3e6f4c3e8b1f66f33
```

The content is the raw stripe payload. When encryption is enabled, the bytes
are AES-XTS encrypted per sector before being written, and the hash is computed
on the encrypted payload. Consumers verify the SHA-256 hash before decrypting
and returning the stripe.
