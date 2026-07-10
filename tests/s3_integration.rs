//! Integration tests that exercise the archive/export pipeline against a real
//! S3-compatible endpoint, with fault injection driven through the
//! [r2proxy](https://github.com/pykello/r2proxy) admin API.
//!
//! These tests are a **no-op unless `S3_INTEGRATION_TESTS_ENDPOINT` is set**.
//!
//! **To run them, use `scripts/s3-integration-tests.sh`** (both CI and local
//! runs go through it). You supply only the real store's endpoint, bucket, and
//! keys; the script starts r2proxy in front of that bucket and sets the
//! variables below to point the tests at the proxy. See the script header for
//! the exact invocation. The same script is what the CI workflow
//! (`.github/workflows/s3-integration.yaml`) runs.
//!
//! The variables the tests themselves read (populated by that script) are
//! all-or-nothing: when the endpoint is set, every other one is expected to be
//! set too (a missing one panics rather than silently skips).
//!
//! | Variable | Meaning |
//! |----------|---------|
//! | `S3_INTEGRATION_TESTS_ENDPOINT` | r2proxy data-plane URL, e.g. `http://127.0.0.1:8080`. Must be an IP host so the AWS SDK uses path-style addressing (r2proxy requires it). |
//! | `S3_INTEGRATION_TESTS_BUCKET` | Bucket name on the upstream store. |
//! | `S3_INTEGRATION_TESTS_ACCESS_KEY_ID` | Proxy access key (client-facing; the proxy re-signs to the real store). |
//! | `S3_INTEGRATION_TESTS_SECRET_ACCESS_KEY` | Proxy secret key. |
//! | `S3_INTEGRATION_TESTS_REGION` | Optional; defaults to `auto`. |
//! | `S3_INTEGRATION_TESTS_ADMIN` | r2proxy admin API URL, e.g. `http://127.0.0.1:8081`. |
//! | `S3_INTEGRATION_TESTS_ADMIN_TOKEN` | r2proxy admin token. |
//! | `S3_INTEGRATION_TESTS_PREFIX` | Base key prefix for the run; every object is written under it. The script sets a unique one and deletes it on exit. |
//!
//! Every object is written under `S3_INTEGRATION_TESTS_PREFIX`, and the runner
//! script deletes that prefix on exit (pass, fail, or cancel) via the ignored
//! [`cleanup`] test, so the bucket is left clean.
//!
//! The tests share one global lock because injected fault rules are proxy-wide,
//! so they run effectively serially even though `cargo test` spawns them on
//! separate threads.

use std::fs::{self, File};
use std::path::PathBuf;
use std::process::Command;
use std::sync::{Mutex, MutexGuard};
use std::time::{Duration, Instant, SystemTime};

const ARCHIVE_BIN: &str = env!("CARGO_BIN_EXE_archive");
const EXPORT_BIN: &str = env!("CARGO_BIN_EXE_export-archive");
const INIT_BIN: &str = env!("CARGO_BIN_EXE_init-metadata");

/// 1 MiB stripes; a 4 MiB device is four data stripes plus metadata/mapping.
const STRIPE_SHIFT: u8 = 11;
const DEVICE_BYTES: usize = 4 * 1024 * 1024;
/// A fixed 32-byte archive KEK, provided inline (test-only).
const ARCHIVE_KEK: &str = "0123456789abcdef0123456789abcdef";

/// Fault rules are proxy-wide, so only one test may touch the proxy at a time.
static SERIAL: Mutex<()> = Mutex::new(());

fn serial() -> MutexGuard<'static, ()> {
    // Tolerate poisoning: a panicking test still leaves the proxy usable once we
    // clear rules at the start of the next test.
    SERIAL.lock().unwrap_or_else(|e| e.into_inner())
}

struct TestS3 {
    endpoint: String,
    bucket: String,
    region: String,
    admin: String,
    admin_token: String,
}

fn required(key: &str) -> String {
    std::env::var(key)
        .unwrap_or_else(|_| panic!("{key} must be set when S3_INTEGRATION_TESTS_ENDPOINT is set"))
}

/// Reads the environment, or returns `None` (test skips) when the endpoint gate
/// is unset.
fn test_env() -> Option<TestS3> {
    let endpoint = std::env::var("S3_INTEGRATION_TESTS_ENDPOINT").ok()?;
    Some(TestS3 {
        endpoint,
        bucket: required("S3_INTEGRATION_TESTS_BUCKET"),
        region: std::env::var("S3_INTEGRATION_TESTS_REGION").unwrap_or_else(|_| "auto".to_string()),
        admin: required("S3_INTEGRATION_TESTS_ADMIN"),
        admin_token: required("S3_INTEGRATION_TESTS_ADMIN_TOKEN"),
    })
}

impl TestS3 {
    fn admin_curl(&self, args: &[&str]) -> std::process::Output {
        let auth = format!("Authorization: Bearer {}", self.admin_token);
        let mut full = vec!["-s", "-m", "15", "-H", &auth];
        full.extend_from_slice(args);
        Command::new("curl")
            .args(&full)
            .output()
            .expect("run curl against r2proxy admin")
    }

    /// Delete every injection rule (best-effort clean slate).
    fn clear_rules(&self) {
        self.admin_curl(&["-X", "DELETE", &format!("{}/api/rules", self.admin)]);
    }

    /// Inject a persistent rule (fires on every matching request until cleared).
    fn inject_rule(&self, body: &str) {
        let out = self.admin_curl(&[
            "-X",
            "POST",
            "-H",
            "Content-Type: application/json",
            "-d",
            body,
            &format!("{}/api/rules", self.admin),
        ]);
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(
            out.status.success() && stdout.contains("\"id\""),
            "failed to inject rule {body}: {stdout}"
        );
    }
}

/// Prepare a test: skip cleanly when unconfigured, otherwise take the serial
/// lock (fault rules are proxy-wide), clear any leftover rules, and build a fresh
/// source device. Returns the environment, the fixture, and the held lock; a test
/// that gets `None` should just return.
fn s3_setup() -> Option<(TestS3, Fixture, MutexGuard<'static, ()>)> {
    let Some(env) = test_env() else {
        eprintln!("skipping: S3_INTEGRATION_TESTS_ENDPOINT not set");
        return None;
    };
    let guard = serial();
    env.clear_rules();
    Some((env, setup_fixture(), guard))
}

/// A deterministic, per-stripe-varying, all-non-zero payload so every stripe is
/// archived as a distinct data object (rather than skipped as zero).
fn device_payload() -> Vec<u8> {
    (0..DEVICE_BYTES)
        .map(|i| {
            let stripe = (i >> 20) as u64;
            let v = (i as u64)
                .wrapping_mul(2_654_435_761)
                .wrapping_add(stripe.wrapping_mul(0x9E37));
            ((v >> 13) as u8) | 1
        })
        .collect()
}

fn unique(tag: &str) -> String {
    let nanos = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    format!("{tag}-{}-{:x}", std::process::id(), nanos)
}

/// A store key prefix nested under the run's base prefix
/// (`S3_INTEGRATION_TESTS_PREFIX`, set by the runner script so it can delete the
/// whole run afterwards). Falls back to a bare unique prefix when run without
/// the script (objects then are not auto-cleaned).
fn store_prefix(tag: &str) -> String {
    let base = std::env::var("S3_INTEGRATION_TESTS_PREFIX").unwrap_or_default();
    format!("{base}{}", unique(tag))
}

/// A source device (base image + overlay + initialized metadata) under
/// `CARGO_TARGET_TMPDIR` (a real filesystem, required for the O_DIRECT opens).
struct Fixture {
    dir: PathBuf,
    config: PathBuf,
    payload: Vec<u8>,
}

fn setup_fixture() -> Fixture {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(unique("fix"));
    fs::create_dir_all(&dir).expect("create fixture dir");

    let payload = device_payload();
    fs::write(dir.join("base.raw"), &payload).expect("write base image");

    let disk = File::create(dir.join("disk.raw")).expect("create disk overlay");
    disk.set_len(DEVICE_BYTES as u64)
        .expect("size disk overlay");

    let config = dir.join("config.toml");
    fs::write(
        &config,
        format!(
            r#"[device]
data_path = "{disk}"
metadata_path = "{meta}"

[stripe_source]
type = "raw"
image_path = "{base}"

[tuning]
io_engine = "sync"

[danger_zone]
enabled = true
allow_unencrypted_disk = true
"#,
            disk = dir.join("disk.raw").display(),
            meta = dir.join("metadata").display(),
            base = dir.join("base.raw").display(),
        ),
    )
    .expect("write source config");

    let out = Command::new(INIT_BIN)
        .args([
            "-f",
            config.to_str().unwrap(),
            "-s",
            &STRIPE_SHIFT.to_string(),
        ])
        .output()
        .expect("run init-metadata");
    assert!(
        out.status.success(),
        "init-metadata failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    Fixture {
        dir,
        config,
        payload,
    }
}

/// Writes an S3 archive-store config. `section` is `target` (archive) or
/// `archive` (export); they share the same field schema. `retry` enables
/// `rate_limited_retry` with `(min_delay_ms, jitter_ms)`.
fn write_store_config(
    fx: &Fixture,
    env: &TestS3,
    section: &str,
    prefix: &str,
    retry: Option<(u64, u64)>,
) -> PathBuf {
    let rlr = match retry {
        Some((min, jitter)) => format!(
            "\n[{section}.rate_limited_retry]\nenabled = true\nmin_delay_ms = {min}\njitter_ms = {jitter}\n"
        ),
        None => String::new(),
    };
    let path = fx.dir.join(format!("{section}-{}.toml", unique("cfg")));
    let kek = ARCHIVE_KEK;
    fs::write(
        &path,
        format!(
            r#"[{section}]
storage = "s3"
bucket = "{bucket}"
prefix = "{prefix}"
region = "{region}"
endpoint = "{endpoint}"
connections = 4
max_attempts = 3
access_key_id.ref = "s3-access-key-id"
secret_access_key.ref = "s3-secret-access-key"
archive_kek.ref = "archive-kek"
{rlr}
[secrets.s3-access-key-id]
source.env = "S3_INTEGRATION_TESTS_ACCESS_KEY_ID"

[secrets.s3-secret-access-key]
source.env = "S3_INTEGRATION_TESTS_SECRET_ACCESS_KEY"

[secrets.archive-kek]
source.inline = "{kek}"

[danger_zone]
enabled = true
allow_env_secrets = true
allow_inline_plaintext_secrets = true
"#,
            bucket = env.bucket,
            region = env.region,
            endpoint = env.endpoint,
        ),
    )
    .expect("write store config");
    path
}

struct RunResult {
    ok: bool,
    elapsed: Duration,
    stderr: String,
}

impl RunResult {
    /// Assert the run succeeded, surfacing its stderr on failure.
    fn assert_ok(&self, what: &str) {
        assert!(self.ok, "{what} failed: {}", self.stderr);
    }
}

fn run_bin(bin: &str, args: &[&str]) -> RunResult {
    let start = Instant::now();
    let out = Command::new(bin).args(args).output().expect("spawn binary");
    RunResult {
        ok: out.status.success(),
        elapsed: start.elapsed(),
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
    }
}

/// Archives the fixture to `prefix`. `retry` optionally enables
/// `rate_limited_retry`; `extra` passes extra `archive` CLI flags.
fn archive(
    fx: &Fixture,
    env: &TestS3,
    prefix: &str,
    retry: Option<(u64, u64)>,
    extra: &[&str],
) -> RunResult {
    let target = write_store_config(fx, env, "target", prefix, retry);
    let mut args = vec![
        "-f",
        fx.config.to_str().unwrap(),
        "--target-config",
        target.to_str().unwrap(),
    ];
    args.extend_from_slice(extra);
    run_bin(ARCHIVE_BIN, &args)
}

/// Exports the archive at `prefix` to a fresh raw image and returns its path.
fn export(fx: &Fixture, env: &TestS3, prefix: &str) -> (RunResult, PathBuf) {
    let source = write_store_config(fx, env, "archive", prefix, None);
    let out = fx.dir.join(format!("{}.raw", unique("export")));
    let result = run_bin(
        EXPORT_BIN,
        &[
            "--source",
            source.to_str().unwrap(),
            "--target",
            out.to_str().unwrap(),
        ],
    );
    (result, out)
}

/// Archive to `prefix` (with optional extra `archive` flags), export it back,
/// and assert the reconstructed image matches the source device byte for byte.
fn roundtrip(fx: &Fixture, env: &TestS3, prefix: &str, extra: &[&str]) {
    archive(fx, env, prefix, None, extra).assert_ok("archive");
    let (result, out) = export(fx, env, prefix);
    result.assert_ok("export");

    let got = fs::read(&out).expect("read exported image");
    assert!(
        got == fx.payload,
        "exported image ({} bytes) differs from source ({} bytes)",
        got.len(),
        fx.payload.len(),
    );
}

// --- Tests -------------------------------------------------------------------

/// Happy path: archive a device, export it back, bytes match.
#[test]
fn archive_export_roundtrip_plain() {
    let Some((env, fx, _g)) = s3_setup() else {
        return;
    };
    roundtrip(&fx, &env, &store_prefix("plain"), &[]);
}

/// Same, but with encryption and zstd compression enabled.
#[test]
fn archive_export_roundtrip_encrypted_zstd() {
    let Some((env, fx, _g)) = s3_setup() else {
        return;
    };
    let extra = ["--encrypt", "--compression", "zstd", "--zstd-level", "1"];
    roundtrip(&fx, &env, &store_prefix("enc-zstd"), &extra);
}

/// The default client does not retry R2's 429 (ServiceUnavailable), so it fails
/// fast; with `rate_limited_retry` enabled the same 429 is retried after the
/// configured delay, so the (still-failing, because the rule is persistent) run
/// takes measurably longer. This is the core behavior of the retry feature.
#[test]
fn rate_limited_retry_retries_429_default_does_not() {
    let Some((env, fx, _g)) = s3_setup() else {
        return;
    };
    env.inject_rule(r#"{"op":"PutObject","status":429}"#);

    let default = archive(&fx, &env, &store_prefix("t429-default"), None, &[]);
    let retried = archive(&fx, &env, &store_prefix("t429-rlr"), Some((1000, 0)), &[]);
    env.clear_rules();

    assert!(
        !default.ok,
        "expected the default client to fail on the 429"
    );
    assert!(
        !retried.ok,
        "expected the persistent 429 to fail even with retries"
    );
    // 3 attempts with a 1s floor add ~2s of delay the default run never spends.
    assert!(
        retried.elapsed >= default.elapsed + Duration::from_millis(1200),
        "rate_limited_retry should retry with delay: default={:?} rate_limited_retry={:?}",
        default.elapsed,
        retried.elapsed,
    );
}

/// A persistent transient error (500) fails the archive; once cleared, a re-run
/// succeeds and the export round-trips. Exercises error propagation + recovery.
#[test]
fn transient_500_fails_then_recovers() {
    let Some((env, fx, _g)) = s3_setup() else {
        return;
    };
    let prefix = store_prefix("t500");

    env.inject_rule(r#"{"op":"PutObject","status":500}"#);
    let failed = archive(&fx, &env, &prefix, None, &[]);
    assert!(!failed.ok, "expected archive to fail while 500 is injected");

    env.clear_rules();
    roundtrip(&fx, &env, &prefix, &[]);
}

/// A non-retryable error (403 AccessDenied) fails without burning the retry
/// budget, so the archive returns quickly.
#[test]
fn access_denied_fails_fast() {
    let Some((env, fx, _g)) = s3_setup() else {
        return;
    };
    env.inject_rule(r#"{"op":"PutObject","status":403,"code":"AccessDenied"}"#);

    let r = archive(&fx, &env, &store_prefix("t403"), None, &[]);
    env.clear_rules();

    assert!(!r.ok, "expected archive to fail on AccessDenied");
    assert!(
        r.elapsed < Duration::from_secs(10),
        "AccessDenied should not be retried into a long backoff (took {:?})",
        r.elapsed
    );
}

/// Injected latency on every operation should not break the round-trip; the
/// client tolerates slow responses within its operation timeout.
#[test]
fn latency_injection_still_round_trips() {
    let Some((env, fx, _g)) = s3_setup() else {
        return;
    };
    let prefix = store_prefix("latency");

    env.inject_rule(r#"{"op":"*","delay_ms":200}"#);
    roundtrip(&fx, &env, &prefix, &[]);
    env.clear_rules();
}

/// A read-path error surfaces: archive succeeds, then a persistent 500 on
/// GetObject makes the export fail.
#[test]
fn get_object_error_fails_export() {
    let Some((env, fx, _g)) = s3_setup() else {
        return;
    };
    let prefix = store_prefix("get-err");

    archive(&fx, &env, &prefix, None, &[]).assert_ok("archive");

    env.inject_rule(r#"{"op":"GetObject","status":500}"#);
    let (e, _out) = export(&fx, &env, &prefix);
    env.clear_rules();
    assert!(!e.ok, "expected export to fail while GetObject returns 500");
}

/// Deletes every object the run wrote, straight from the real store (not through
/// the proxy, so it works even if the proxy is gone). Ignored so it never runs
/// in the normal suite; the runner script invokes it on exit — pass, fail, or
/// cancel — with the real credentials and the run's base prefix.
#[test]
#[ignore = "cleanup helper invoked by scripts/s3-integration-tests.sh"]
fn cleanup() {
    use aws_sdk_s3::types::{Delete, ObjectIdentifier};
    use ubiblk::utils::s3::{build_s3_client, create_runtime, S3ClientTuning};

    let Ok(endpoint) = std::env::var("S3_INTEGRATION_TESTS_ENDPOINT") else {
        eprintln!("cleanup: S3_INTEGRATION_TESTS_ENDPOINT not set; nothing to do");
        return;
    };
    let prefix = std::env::var("S3_INTEGRATION_TESTS_PREFIX").unwrap_or_default();
    // Never mass-delete a bucket root: require an explicit run prefix.
    if prefix.is_empty() {
        eprintln!("cleanup: S3_INTEGRATION_TESTS_PREFIX not set; refusing to delete");
        return;
    }
    let bucket = required("S3_INTEGRATION_TESTS_BUCKET");
    let region =
        std::env::var("S3_INTEGRATION_TESTS_REGION").unwrap_or_else(|_| "auto".to_string());
    let credentials = aws_sdk_s3::config::Credentials::builder()
        .access_key_id(required("S3_INTEGRATION_TESTS_ACCESS_KEY_ID"))
        .secret_access_key(required("S3_INTEGRATION_TESTS_SECRET_ACCESS_KEY"))
        .provider_name("s3-it-cleanup")
        .build();

    let runtime = create_runtime().expect("tokio runtime");
    let client = build_s3_client(
        &runtime,
        None,
        Some(&endpoint),
        Some(&region),
        Some(credentials),
        S3ClientTuning {
            connect_timeout_ms: 10_000,
            operation_attempt_timeout_ms: 30_000,
            max_attempts: 3,
            rate_limited_retry: None,
        },
    )
    .expect("s3 client");

    let deleted = runtime.block_on(async {
        let mut token: Option<String> = None;
        let mut total = 0usize;
        loop {
            let mut req = client.list_objects_v2().bucket(&bucket).prefix(&prefix);
            if let Some(t) = &token {
                req = req.continuation_token(t);
            }
            let resp = req.send().await.expect("list objects");
            let ids: Vec<ObjectIdentifier> = resp
                .contents()
                .iter()
                .filter_map(|o| o.key())
                .map(|k| ObjectIdentifier::builder().key(k).build().unwrap())
                .collect();
            if !ids.is_empty() {
                total += ids.len();
                client
                    .delete_objects()
                    .bucket(&bucket)
                    .delete(Delete::builder().set_objects(Some(ids)).build().unwrap())
                    .send()
                    .await
                    .expect("delete objects");
            }
            if resp.is_truncated() == Some(true) {
                token = resp.next_continuation_token().map(str::to_string);
            } else {
                break;
            }
        }
        total
    });
    eprintln!("cleanup: deleted {deleted} object(s) under {prefix}");
}
