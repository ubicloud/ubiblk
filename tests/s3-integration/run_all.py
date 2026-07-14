#!/usr/bin/env python3
"""Run the S3 integration tests (cases.py) against a real S3-compatible bucket.

Checks for ubiblk binaries, starts an r2proxy MITM in front of the bucket on a
loopback port, points the tests at the proxy so they can inject faults, and
tears it down afterwards. Every object is written under a unique run prefix,
which is deleted from the bucket on exit -- whether the tests pass, fail, or the
run is cancelled -- so the bucket is left clean.

You provide only the real store's endpoint, bucket, and keys:

    S3_INTEGRATION_TESTS_ENDPOINT=https://<account>.r2.cloudflarestorage.com \\
    S3_INTEGRATION_TESTS_BUCKET=my-test-bucket \\
    S3_INTEGRATION_TESTS_ACCESS_KEY_ID=... \\
    S3_INTEGRATION_TESTS_SECRET_ACCESS_KEY=... \\
      python3 tests/s3-integration/run_all.py

Optional: S3_INTEGRATION_TESTS_REGION (default "auto"), and R2PROXY_BIN if the
r2proxy binary is not on PATH. The ubiblk binaries must already be built (e.g.
cargo build --bin archive --bin export-archive --bin init-metadata); also needs
r2proxy (https://github.com/ubicloud/r2proxy), python3, and the aws CLI (cleanup).
"""

import json
import os
import pathlib
import secrets
import subprocess
import sys
import tempfile

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "common"))

from util import CommandFail, http, r
from harness import free_port, install_exit_handler, wait_for

ROOT = pathlib.Path(__file__).resolve().parents[2]


def require(name):
    value = os.environ.get(name)
    if not value:
        sys.exit(f"{name} must be set")
    return value


def check_binaries():
    bin_dir = ROOT / "target" / "debug"
    required = [
        os.environ.get("ARCHIVE_BIN", str(bin_dir / "archive")),
        os.environ.get("EXPORT_BIN", str(bin_dir / "export-archive")),
        str(bin_dir / "init-metadata"),
    ]
    missing = [path for path in required if not os.path.exists(path)]
    if missing:
        sys.exit(
            "missing binaries: " + ", ".join(missing) + "\n"
            "build them first: cargo build --bin archive --bin export-archive "
            "--bin init-metadata"
        )


def main():
    real_endpoint = require("S3_INTEGRATION_TESTS_ENDPOINT")
    bucket = require("S3_INTEGRATION_TESTS_BUCKET")
    real_access_key = require("S3_INTEGRATION_TESTS_ACCESS_KEY_ID")
    real_secret_key = require("S3_INTEGRATION_TESTS_SECRET_ACCESS_KEY")
    region = os.environ.get("S3_INTEGRATION_TESTS_REGION", "auto")
    r2proxy_bin = os.environ.get("R2PROXY_BIN", "r2proxy")
    check_binaries()

    run_prefix = f"s3-integration-tests/{secrets.token_hex(8)}/"
    tmp = pathlib.Path(tempfile.mkdtemp(prefix="r2proxy-"))
    token = secrets.token_hex(16)
    state = {"proc": None}

    def cleanup():
        # Delete everything this run wrote, straight from the real bucket (does
        # not depend on the proxy still being alive). Best-effort.
        try:
            r(
                "aws", "s3", "rm", "--recursive", "--endpoint-url", real_endpoint,
                f"s3://{bucket}/{run_prefix}",
                env={
                    **os.environ,
                    "AWS_ACCESS_KEY_ID": real_access_key,
                    "AWS_SECRET_ACCESS_KEY": real_secret_key,
                    "AWS_DEFAULT_REGION": region,
                },
            )
        except CommandFail as e:
            print(f"warning: cleanup failed:\n{e.stderr}", file=sys.stderr)
        except FileNotFoundError:
            print(f"warning: aws CLI not found; objects under {run_prefix} not cleaned", file=sys.stderr)
        proc = state["proc"]
        if proc and proc.poll() is None:
            proc.terminate()
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()

    install_exit_handler(cleanup)

    # Start r2proxy in front of the real bucket, on loopback. The IP host makes
    # the AWS SDK use path-style addressing, which r2proxy requires.
    data_port, admin_port = free_port(), free_port()
    proxy_env = {
        **os.environ,
        "R2PROXY_ENDPOINT": real_endpoint,
        "R2PROXY_ACCESS_KEY": real_access_key,
        "R2PROXY_SECRET_KEY": real_secret_key,
        "R2PROXY_REGION": region,
        "R2PROXY_LISTEN": f"127.0.0.1:{data_port}",
        "R2PROXY_ADMIN_LISTEN": f"127.0.0.1:{admin_port}",
        "R2PROXY_ADMIN_TOKEN": token,
        "R2PROXY_CONFIG": str(tmp / "r2proxy.json"),
    }
    # The child keeps its own dup of the fd, so closing our handle after spawn is
    # fine and keeps the log open for the proxy's lifetime.
    with open(tmp / "r2proxy.log", "w") as log:
        state["proc"] = subprocess.Popen([r2proxy_bin, "serve"], env=proxy_env, stdout=log, stderr=log)

    admin = f"http://127.0.0.1:{admin_port}"
    wait_for(lambda: http("GET", f"{admin}/api/serverinfo"), "r2proxy", attempts=40, delay=0.5)

    # The proxy mints its own client-facing credentials; read them back and point
    # the tests at the proxy (the real credentials stay with the proxy).
    info = json.loads(http("GET", f"{admin}/api/info", token=token))
    os.environ.update({
        "S3_INTEGRATION_TESTS_ENDPOINT": f"http://127.0.0.1:{data_port}",
        "S3_INTEGRATION_TESTS_ADMIN": admin,
        "S3_INTEGRATION_TESTS_ADMIN_TOKEN": token,
        "S3_INTEGRATION_TESTS_REGION": region,
        "S3_INTEGRATION_TESTS_BUCKET": bucket,
        "S3_INTEGRATION_TESTS_ACCESS_KEY_ID": info["proxy_access_key"],
        "S3_INTEGRATION_TESTS_SECRET_ACCESS_KEY": info["proxy_secret_key"],
        "S3_INTEGRATION_TESTS_PREFIX": run_prefix,
    })

    from cases import Cases

    sys.exit(Cases().run())


if __name__ == "__main__":
    main()
