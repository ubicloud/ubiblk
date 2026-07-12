# S3 integration tests

End-to-end tests that archive a ubiblk device to a **real** S3-compatible bucket
and read it back, exercising a variety of error conditions along the way. They
are written as shell scripts that drive the `archive`, `export-archive`, and
`init-metadata` binaries — nothing here is a Rust `cargo test`.

Fault injection (throttles, 5xx, latency) is done with
[r2proxy](https://github.com/ubicloud/r2proxy), a MITM proxy placed in front of
the bucket: the launcher starts it on a loopback port, the tests point at it, and
it forwards to (and re-signs for) the real store.

## What is covered

| Case | What it checks |
|------|----------------|
| `archive_export_roundtrip_plain` | Archive a device, export it, bytes match. |
| `archive_export_roundtrip_encrypted_zstd` | Same, with `--encrypt` + zstd. |
| `rate_limited_retry_retries_429_default_does_not` | The default client drops R2's 429; `rate_limited_retry` retries it after a delay (asserted via timing). |
| `transient_500_fails_then_recovers` | A persistent 500 fails the archive; once cleared, a re-run round-trips. |
| `transient_errors_recovered_by_retries` | Errors that clear within the retry budget (fail twice per object, then succeed) do not fail a single archive. |
| `access_denied_fails_fast` | A non-retryable 403 fails without a long backoff. |
| `latency_injection_still_round_trips` | Injected latency does not break the round-trip. |
| `get_object_error_fails_export` | A 500 on `GetObject` fails the export. |

## Files

- `run-all.sh` — launcher. Builds the binaries, starts r2proxy in front of your
  bucket, points the tests at it, runs `cases.sh`, and deletes the run's objects
  on exit (pass, fail, or cancel).
- `cases.sh` — the test cases themselves. Builds a device fixture with
  `scripts/ubiblk-init`, then archives/exports and injects faults.

## Running locally

Provide the **real** store's endpoint, bucket, and keys and run the launcher; it
takes care of the proxy, the config, and cleanup:

```sh
S3_INTEGRATION_TESTS_ENDPOINT=https://<account>.r2.cloudflarestorage.com \
S3_INTEGRATION_TESTS_BUCKET=my-test-bucket \
S3_INTEGRATION_TESTS_ACCESS_KEY_ID=... \
S3_INTEGRATION_TESTS_SECRET_ACCESS_KEY=... \
  tests/s3-integration/run-all.sh
```

Optional: `S3_INTEGRATION_TESTS_REGION` (default `auto`), and `R2PROXY_BIN` if
the `r2proxy` binary is not on your `PATH`.

### Requirements

- `r2proxy` built and on `PATH` (or pointed to via `R2PROXY_BIN`) — build it with
  `go build` from <https://github.com/ubicloud/r2proxy>.
- `cargo`, `curl`, `python3`, and the `aws` CLI (used only for bucket cleanup).

Every object is written under a unique `s3-integration-tests/<run-id>/` prefix
that is deleted from the bucket when the launcher exits, so nothing is left
behind — even if a run is cancelled.

## CI

`.github/workflows/s3-integration.yaml` runs the same launcher on pushes to
`main`, pull requests, and manual dispatch. It reads the store credentials from
repository secrets of the same names (`S3_INTEGRATION_TESTS_ENDPOINT`,
`S3_INTEGRATION_TESTS_BUCKET`, `S3_INTEGRATION_TESTS_ACCESS_KEY_ID`,
`S3_INTEGRATION_TESTS_SECRET_ACCESS_KEY`, optional `S3_INTEGRATION_TESTS_REGION`).
When those secrets are absent (for example on fork PRs) the job skips cleanly.
