"""S3 integration test cases, in Python.

Archives a ubiblk device to the S3 endpoint in the environment and reads it
back, injecting faults through the r2proxy admin API. Normally run via
run_all.py (the launcher), which starts r2proxy and points these variables at
it. It reads (all set by that launcher):

    S3_INTEGRATION_TESTS_ENDPOINT      S3 data-plane URL (the proxy)
    S3_INTEGRATION_TESTS_BUCKET        bucket name
    S3_INTEGRATION_TESTS_ACCESS_KEY_ID / _SECRET_ACCESS_KEY   (read by `archive`)
    S3_INTEGRATION_TESTS_REGION        optional, default "auto"
    S3_INTEGRATION_TESTS_ADMIN         r2proxy admin API URL
    S3_INTEGRATION_TESTS_ADMIN_TOKEN   r2proxy admin token
    S3_INTEGRATION_TESTS_PREFIX        base key prefix for the run

Binaries default to target/debug; override with ARCHIVE_BIN / EXPORT_BIN.
``Cases().run()`` returns a non-zero exit code if any case fails.
"""

import json
import os
import pathlib
import random
import subprocess
import tempfile
import time

from util import http, r, toml_dump

ROOT = pathlib.Path(__file__).resolve().parents[2]
BIN_DIR = ROOT / "target" / "debug"
ARCHIVE = os.environ.get("ARCHIVE_BIN", str(BIN_DIR / "archive"))
EXPORT = os.environ.get("EXPORT_BIN", str(BIN_DIR / "export-archive"))

DEVICE_MB = 4  # with 128K stripes -> 32 stripes (32 data objects)
STRIPE_SIZE = "128K"
ARCHIVE_KEK = "0123456789abcdef0123456789abcdef"


class Cases:
    def __init__(self):
        env = os.environ
        self.endpoint = env["S3_INTEGRATION_TESTS_ENDPOINT"]
        self.bucket = env["S3_INTEGRATION_TESTS_BUCKET"]
        self.region = env.get("S3_INTEGRATION_TESTS_REGION", "auto")
        self.admin = env["S3_INTEGRATION_TESTS_ADMIN"]
        self.token = env["S3_INTEGRATION_TESTS_ADMIN_TOKEN"]
        self.prefix = env.get("S3_INTEGRATION_TESTS_PREFIX", "")
        # Work on a real filesystem: the binaries open image files with O_DIRECT,
        # which tmpfs (/tmp on many systems) rejects. target/ is on the repo's fs.
        self.work = pathlib.Path(tempfile.mkdtemp(prefix="s3-it-", dir=str(ROOT / "target")))
        self.results = []
        self._n = 0

    # --- reporting -----------------------------------------------------------

    def ok(self, name):
        print(f"ok   - {name}")
        self.results.append(True)

    def notok(self, name, detail):
        print(f"FAIL - {name} ({detail})")
        self.results.append(False)

    def uid(self, tag):
        self._n += 1
        return f"{tag}-{self._n}-{random.randrange(1 << 24)}"

    def store_prefix(self, tag):
        return f"{self.prefix}{self.uid(tag)}"

    # --- device fixture (built once, reused with a fresh prefix per case) -----

    def make_fixture(self):
        """Reuse the project's own initializer to write config.toml, disk.raw,
        and the metadata, with a random image as the raw stripe source. This
        keeps the device-config format in sync with real usage."""
        (self.work / "base.raw").write_bytes(os.urandom(DEVICE_MB * 1024 * 1024))
        # ubiblk-init shells out to init-metadata by name; make our build findable.
        env = {**os.environ, "PATH": str(BIN_DIR) + os.pathsep + os.environ["PATH"]}
        r(
            "python3", str(ROOT / "scripts" / "ubiblk-init"),
            "--size", f"{DEVICE_MB}M", "--dir", str(self.work),
            "--base", str(self.work / "base.raw"), "--stripe-size", STRIPE_SIZE,
            "--io-engine", "io_uring", "--force",
            env=env,
        )

    # --- config + archive/export drivers -------------------------------------

    def write_store_config(self, section, prefix, retry=None):
        """Write an S3 store config. ``section`` is "target" (archive) or
        "archive" (export). ``retry`` is None or ``(min_delay_ms, jitter_ms)``."""
        tables = [
            (section, {
                "storage": "s3",
                "bucket": self.bucket,
                "prefix": prefix,
                "region": self.region,
                "endpoint": self.endpoint,
                "connections": 4,
                "max_attempts": 3,
                "access_key_id.ref": "ak",
                "secret_access_key.ref": "sk",
                "archive_kek.ref": "kek",
            }),
        ]
        if retry is not None:
            min_ms, jitter_ms = retry
            tables.append((f"{section}.rate_limited_retry",
                           {"enabled": True, "min_delay_ms": min_ms, "jitter_ms": jitter_ms}))
        tables += [
            ("secrets.ak", {"source.env": "S3_INTEGRATION_TESTS_ACCESS_KEY_ID"}),
            ("secrets.sk", {"source.env": "S3_INTEGRATION_TESTS_SECRET_ACCESS_KEY"}),
            ("secrets.kek", {"source.inline": ARCHIVE_KEK}),
            ("danger_zone", {
                "enabled": True,
                "allow_env_secrets": True,
                "allow_inline_plaintext_secrets": True,
            }),
        ]
        path = self.work / f"{section}-{self.uid('cfg')}.toml"
        path.write_text(toml_dump(tables))
        return str(path)

    def _timed(self, *command):
        """Run a command, returning (ok, elapsed_seconds)."""
        start = time.monotonic()
        p = subprocess.run(command, capture_output=True, text=True)
        return p.returncode == 0, time.monotonic() - start

    def archive(self, prefix, retry=None, extra=()):
        cfg = self.write_store_config("target", prefix, retry)
        return self._timed(ARCHIVE, "-f", str(self.work / "config.toml"), "--target-config", cfg, *extra)

    def export(self, prefix):
        cfg = self.write_store_config("archive", prefix)
        out = self.work / f"export-{self.uid('raw')}.raw"
        ok, _ = self._timed(EXPORT, "--source", cfg, "--target", str(out))
        return ok, out

    def roundtrip(self, name, prefix, extra=()):
        """Archive to ``prefix``, export it back, and assert bytes match."""
        ok, _ = self.archive(prefix, extra=extra)
        if not ok:
            self.notok(name, "archive failed")
            return False
        ok, out = self.export(prefix)
        if not ok:
            self.notok(name, "export failed")
            return False
        if out.read_bytes() != (self.work / "base.raw").read_bytes():
            self.notok(name, "exported bytes differ from source")
            return False
        self.ok(name)
        return True

    # --- r2proxy fault injection (persistent rules) --------------------------

    def inject_rule(self, rule):
        body = http("POST", f"{self.admin}/api/rules", token=self.token, body=rule)
        try:
            stored = json.loads(body)
        except json.JSONDecodeError:
            stored = None
        if not isinstance(stored, dict) or "id" not in stored:
            raise RuntimeError(f"failed to inject rule {rule}: {body}")

    def clear_rules(self):
        http("DELETE", f"{self.admin}/api/rules", token=self.token)

    # --- cases ---------------------------------------------------------------

    def case_roundtrip_plain(self):
        self.clear_rules()
        self.roundtrip("archive_export_roundtrip_plain", self.store_prefix("plain"))

    def case_roundtrip_encrypted_zstd(self):
        self.roundtrip(
            "archive_export_roundtrip_encrypted_zstd",
            self.store_prefix("enc-zstd"),
            extra=["--encrypt", "--compression", "zstd", "--zstd-level", "1"],
        )

    def case_rate_limited_retry_429(self):
        # A 429 isn't retried by default, so the default run fails fast;
        # rate_limited_retry does two 3s retries, ~6s slower. Require +4s margin.
        self.clear_rules()
        self.inject_rule({"op": "PutObject", "status": 429})
        default_ok, default_s = self.archive(self.store_prefix("t429-default"))
        retry_ok, retry_s = self.archive(self.store_prefix("t429-rlr"), retry=(3000, 0))
        self.clear_rules()
        name = "rate_limited_retry_retries_429_default_does_not"
        if not default_ok and not retry_ok and retry_s >= default_s + 4:
            self.ok(name)
        else:
            self.notok(name, f"default ok={default_ok} ({default_s:.2f}s), retry ok={retry_ok} ({retry_s:.2f}s)")

    def case_transient_500_recovers(self):
        # A persistent 500 fails the archive; once cleared, a re-run round-trips.
        self.clear_rules()
        prefix = self.store_prefix("t500")
        self.inject_rule({"op": "PutObject", "status": 500})
        ok, _ = self.archive(prefix)
        if ok:
            self.notok("transient_500_fails_then_recovers", "archive unexpectedly succeeded under 500")
            return
        self.clear_rules()
        self.roundtrip("transient_500_fails_then_recovers", prefix)

    def case_access_denied_fails_fast(self):
        # A non-retryable 403 fails fast (not retried into a long backoff).
        self.clear_rules()
        self.inject_rule({"op": "PutObject", "status": 403, "code": "AccessDenied"})
        ok, elapsed = self.archive(self.store_prefix("t403"))
        self.clear_rules()
        name = "access_denied_fails_fast"
        if not ok and elapsed < 10:
            self.ok(name)
        else:
            self.notok(name, f"ok={ok}, elapsed={elapsed:.2f}s")

    def case_latency_round_trips(self):
        # Injected latency should not break the round-trip.
        self.clear_rules()
        self.inject_rule({"op": "*", "delay_ms": 200})
        self.roundtrip("latency_injection_still_round_trips", self.store_prefix("latency"))
        self.clear_rules()

    CASES = [
        case_roundtrip_plain,
        case_roundtrip_encrypted_zstd,
        case_rate_limited_retry_429,
        case_transient_500_recovers,
        case_access_denied_fails_fast,
        case_latency_round_trips,
    ]

    def run(self):
        self.make_fixture()
        for case in self.CASES:
            try:
                case(self)
            except Exception as e:  # a case that raises counts as a failure
                self.notok(case.__name__, f"raised {type(e).__name__}: {e}")
        passed = sum(self.results)
        failed = len(self.results) - passed
        print(f"\n# {passed} passed, {failed} failed")
        return 1 if failed else 0
