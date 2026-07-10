#!/usr/bin/env bash
#
# Run the S3 integration tests (tests/s3_integration.rs) against a real
# S3-compatible bucket. This starts an r2proxy MITM in front of the bucket on a
# loopback port, points the tests at the proxy so they can inject faults, and
# tears it down afterwards.
#
# Every object is written under a unique run prefix, which is deleted from the
# bucket on exit — whether the tests pass, fail, or the run is cancelled — so the
# bucket is left clean.
#
# You provide only the real store's endpoint, bucket, and keys:
#
#   S3_INTEGRATION_TESTS_ENDPOINT=https://<account>.r2.cloudflarestorage.com \
#   S3_INTEGRATION_TESTS_BUCKET=my-test-bucket \
#   S3_INTEGRATION_TESTS_ACCESS_KEY_ID=... \
#   S3_INTEGRATION_TESTS_SECRET_ACCESS_KEY=... \
#     scripts/s3-integration-tests.sh
#
# Optional:
#   S3_INTEGRATION_TESTS_REGION   defaults to "auto"
#   R2PROXY_BIN                   path to the r2proxy binary (default: "r2proxy" on PATH)
#
# Any extra arguments are forwarded to `cargo test` (e.g. -- --nocapture).
#
# Requires r2proxy (https://github.com/pykello/r2proxy) built and available, and
# curl + python3.
set -euo pipefail

: "${S3_INTEGRATION_TESTS_ENDPOINT:?set the real store endpoint}"
: "${S3_INTEGRATION_TESTS_BUCKET:?set the bucket}"
: "${S3_INTEGRATION_TESTS_ACCESS_KEY_ID:?set the access key id}"
: "${S3_INTEGRATION_TESTS_SECRET_ACCESS_KEY:?set the secret access key}"
REGION="${S3_INTEGRATION_TESTS_REGION:-auto}"
R2PROXY_BIN="${R2PROXY_BIN:-r2proxy}"

# Keep the real store coordinates; the test variables get pointed at the proxy
# below, but cleanup deletes from the real bucket directly.
REAL_ENDPOINT="$S3_INTEGRATION_TESTS_ENDPOINT"
REAL_ACCESS_KEY_ID="$S3_INTEGRATION_TESTS_ACCESS_KEY_ID"
REAL_SECRET_ACCESS_KEY="$S3_INTEGRATION_TESTS_SECRET_ACCESS_KEY"
BUCKET="$S3_INTEGRATION_TESTS_BUCKET"

RUN_ID="$(head -c8 /dev/urandom | od -An -tx1 | tr -d ' \n')"
RUN_PREFIX="s3-integration-tests/${RUN_ID}/"

TMP="$(mktemp -d)"
TOKEN="s3-it-$(head -c16 /dev/urandom | od -An -tx1 | tr -d ' \n')"
PROXY_PID=""

cleanup() {
  # Delete everything this run wrote, straight from the real bucket (does not
  # depend on the proxy still being alive). Best-effort.
  S3_INTEGRATION_TESTS_ENDPOINT="$REAL_ENDPOINT" \
  S3_INTEGRATION_TESTS_ACCESS_KEY_ID="$REAL_ACCESS_KEY_ID" \
  S3_INTEGRATION_TESTS_SECRET_ACCESS_KEY="$REAL_SECRET_ACCESS_KEY" \
  S3_INTEGRATION_TESTS_BUCKET="$BUCKET" \
  S3_INTEGRATION_TESTS_REGION="$REGION" \
  S3_INTEGRATION_TESTS_PREFIX="$RUN_PREFIX" \
    cargo test --test s3_integration -- --ignored --exact cleanup --nocapture \
    >>"$TMP/cleanup.log" 2>&1 || echo "warning: cleanup pass failed; see $TMP/cleanup.log" >&2

  [ -n "$PROXY_PID" ] && kill "$PROXY_PID" 2>/dev/null || true
  rm -rf "$TMP"
}
# Turn signals into a normal exit so the EXIT trap (cleanup) always runs.
trap 'exit 130' INT
trap 'exit 143' TERM
trap cleanup EXIT

# Two free loopback ports (data plane + admin API).
read -r DATA_PORT ADMIN_PORT < <(python3 - <<'PY'
import socket
s = [socket.socket() for _ in range(2)]
for x in s:
    x.bind(("127.0.0.1", 0))
print(*[x.getsockname()[1] for x in s])
for x in s:
    x.close()
PY
)

# Start r2proxy in front of the real bucket, on loopback. The IP host makes the
# AWS SDK use path-style addressing, which r2proxy requires.
R2PROXY_ENDPOINT="$REAL_ENDPOINT" \
R2PROXY_ACCESS_KEY="$REAL_ACCESS_KEY_ID" \
R2PROXY_SECRET_KEY="$REAL_SECRET_ACCESS_KEY" \
R2PROXY_REGION="$REGION" \
R2PROXY_LISTEN="127.0.0.1:${DATA_PORT}" \
R2PROXY_ADMIN_LISTEN="127.0.0.1:${ADMIN_PORT}" \
R2PROXY_ADMIN_TOKEN="$TOKEN" \
R2PROXY_CONFIG="$TMP/r2proxy.json" \
  "$R2PROXY_BIN" serve >"$TMP/r2proxy.log" 2>&1 &
PROXY_PID=$!

# Wait for the admin API to come up.
for _ in $(seq 1 40); do
  curl -sf -m2 "http://127.0.0.1:${ADMIN_PORT}/api/serverinfo" >/dev/null 2>&1 && break
  sleep 0.5
done
if ! curl -sf -m2 "http://127.0.0.1:${ADMIN_PORT}/api/serverinfo" >/dev/null 2>&1; then
  echo "r2proxy did not start; log:" >&2
  cat "$TMP/r2proxy.log" >&2 || true
  exit 1
fi

# The proxy mints its own client-facing credentials; read them back and point
# the tests at the proxy (the real credentials stay with the proxy).
info="$(curl -s -m10 -H "Authorization: Bearer $TOKEN" "http://127.0.0.1:${ADMIN_PORT}/api/info")"
field() { printf '%s' "$info" | python3 -c "import json,sys;print(json.load(sys.stdin)['$1'])"; }

export S3_INTEGRATION_TESTS_ENDPOINT="http://127.0.0.1:${DATA_PORT}"
export S3_INTEGRATION_TESTS_ADMIN="http://127.0.0.1:${ADMIN_PORT}"
export S3_INTEGRATION_TESTS_ADMIN_TOKEN="$TOKEN"
export S3_INTEGRATION_TESTS_REGION="$REGION"
export S3_INTEGRATION_TESTS_ACCESS_KEY_ID="$(field proxy_access_key)"
export S3_INTEGRATION_TESTS_SECRET_ACCESS_KEY="$(field proxy_secret_key)"
export S3_INTEGRATION_TESTS_PREFIX="$RUN_PREFIX"
# S3_INTEGRATION_TESTS_BUCKET is passed through unchanged.

cargo test --test s3_integration "$@"
