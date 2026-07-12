#!/usr/bin/env bash
#
# S3 integration test cases, in shell. Archives a ubiblk device to the S3
# endpoint in the environment and reads it back, injecting faults through the
# r2proxy admin API.
#
# Normally run via run-all.sh (the launcher), which starts r2proxy and points
# these variables at it. It reads (all set by that launcher):
#
#   S3_INTEGRATION_TESTS_ENDPOINT      S3 data-plane URL (the proxy)
#   S3_INTEGRATION_TESTS_BUCKET        bucket name
#   S3_INTEGRATION_TESTS_ACCESS_KEY_ID / _SECRET_ACCESS_KEY   (read by `archive`)
#   S3_INTEGRATION_TESTS_REGION        optional, default "auto"
#   S3_INTEGRATION_TESTS_ADMIN         r2proxy admin API URL
#   S3_INTEGRATION_TESTS_ADMIN_TOKEN   r2proxy admin token
#   S3_INTEGRATION_TESTS_PREFIX        base key prefix for the run
#
# Binaries default to target/debug; override with ARCHIVE_BIN/EXPORT_BIN/INIT_BIN.
# Exits non-zero if any case fails.
set -uo pipefail

ENDPOINT="${S3_INTEGRATION_TESTS_ENDPOINT:?set S3_INTEGRATION_TESTS_ENDPOINT}"
BUCKET="${S3_INTEGRATION_TESTS_BUCKET:?}"
REGION="${S3_INTEGRATION_TESTS_REGION:-auto}"
ADMIN="${S3_INTEGRATION_TESTS_ADMIN:?}"
TOKEN="${S3_INTEGRATION_TESTS_ADMIN_TOKEN:?}"
PREFIX="${S3_INTEGRATION_TESTS_PREFIX:-}"
: "${S3_INTEGRATION_TESTS_ACCESS_KEY_ID:?}"     # consumed by the archive binary
: "${S3_INTEGRATION_TESTS_SECRET_ACCESS_KEY:?}"

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
ARCHIVE="${ARCHIVE_BIN:-$ROOT/target/debug/archive}"
EXPORT="${EXPORT_BIN:-$ROOT/target/debug/export-archive}"
INIT="${INIT_BIN:-$ROOT/target/debug/init-metadata}"
# ubiblk-init shells out to init-metadata by name; make our build findable.
INIT_DIR="$(dirname "$INIT")"
export PATH="$INIT_DIR:$PATH"

DEVICE_MB=4        # with 128K stripes below -> 32 stripes (32 data objects)
STRIPE_SIZE="128K" # ubiblk-init --stripe-size choice
ARCHIVE_KEK="0123456789abcdef0123456789abcdef"

# Work on a real filesystem: the binaries open image files with O_DIRECT, which
# tmpfs (/tmp on many systems) rejects. target/ is on the repo's filesystem.
WORK="$(mktemp -d "$ROOT/target/s3-it-XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

pass=0
fail=0
ok() { echo "ok   - $1"; pass=$((pass + 1)); }
notok() {
  echo "FAIL - $1 ($2)"
  fail=$((fail + 1))
}

seq_n=0
uid() {
  seq_n=$((seq_n + 1))
  echo "$seq_n-$RANDOM"
}
store_prefix() { echo "${PREFIX}$1-$(uid)"; }
now() { date +%s.%N; }
since() { awk -v a="$1" -v b="$(date +%s.%N)" 'BEGIN { printf "%.3f", b - a }'; }

# --- device fixture (built once, reused with a fresh prefix per case) ---------

# Reuse the project's own initializer to write config.toml, disk.raw, and the
# metadata, with our random image as the raw stripe source. This keeps the
# device-config format in sync with real usage instead of duplicating it here.
make_fixture() {
  head -c "$((DEVICE_MB * 1024 * 1024))" /dev/urandom >"$WORK/base.raw"
  python3 "$ROOT/scripts/ubiblk-init" --size "${DEVICE_MB}M" --dir "$WORK" \
    --base "$WORK/base.raw" --stripe-size "$STRIPE_SIZE" --io-engine io_uring --force >/dev/null 2>&1
}

# --- config + archive/export drivers -----------------------------------------

# write_store_config SECTION PREFIX RETRY -> prints the config path. SECTION is
# "target" (archive) or "archive" (export). RETRY is "" or "min_ms,jitter_ms".
write_store_config() {
  local section="$1" prefix="$2" retry="$3" file rlr=""
  file="$WORK/$section-$(uid).toml"
  if [ -n "$retry" ]; then
    rlr=$'\n'"[$section.rate_limited_retry]"$'\n'"enabled = true"
    rlr+=$'\n'"min_delay_ms = ${retry%,*}"$'\n'"jitter_ms = ${retry#*,}"$'\n'
  fi
  cat >"$file" <<EOF
[$section]
storage = "s3"
bucket = "$BUCKET"
prefix = "$prefix"
region = "$REGION"
endpoint = "$ENDPOINT"
connections = 4
max_attempts = 3
access_key_id.ref = "ak"
secret_access_key.ref = "sk"
archive_kek.ref = "kek"
$rlr
[secrets.ak]
source.env = "S3_INTEGRATION_TESTS_ACCESS_KEY_ID"

[secrets.sk]
source.env = "S3_INTEGRATION_TESTS_SECRET_ACCESS_KEY"

[secrets.kek]
source.inline = "$ARCHIVE_KEK"

[danger_zone]
enabled = true
allow_env_secrets = true
allow_inline_plaintext_secrets = true
EOF
  echo "$file"
}

# do_archive PREFIX RETRY [extra archive flags...] -> exit code
do_archive() {
  local prefix="$1" retry="$2" cfg
  shift 2
  cfg="$(write_store_config target "$prefix" "$retry")"
  "$ARCHIVE" -f "$WORK/config.toml" --target-config "$cfg" "$@" >/dev/null 2>&1
}

# do_export PREFIX OUT -> exit code
do_export() {
  local cfg
  cfg="$(write_store_config archive "$1" "")"
  "$EXPORT" --source "$cfg" --target "$2" >/dev/null 2>&1
}

# roundtrip NAME PREFIX [extra archive flags...]: archive, export, compare bytes.
roundtrip() {
  local name="$1" prefix="$2" out
  shift 2
  if ! do_archive "$prefix" "" "$@"; then
    notok "$name" "archive failed"
    return
  fi
  out="$WORK/export-$(uid).raw"
  if ! do_export "$prefix" "$out"; then
    notok "$name" "export failed"
    return
  fi
  if cmp -s "$out" "$WORK/base.raw"; then
    ok "$name"
  else
    notok "$name" "exported bytes differ from source"
  fi
}

# --- r2proxy fault injection (persistent rules) ------------------------------

admin() { curl -s -m15 -H "Authorization: Bearer $TOKEN" "$@"; }
inject_rule() { admin -H "Content-Type: application/json" -d "$1" "$ADMIN/api/rules" | grep -q '"id"'; }
clear_rules() { admin -X DELETE "$ADMIN/api/rules" >/dev/null; }

# --- cases -------------------------------------------------------------------

make_fixture

# Happy path.
clear_rules
roundtrip "archive_export_roundtrip_plain" "$(store_prefix plain)"

# With encryption + zstd compression.
roundtrip "archive_export_roundtrip_encrypted_zstd" "$(store_prefix enc-zstd)" \
  --encrypt --compression zstd --zstd-level 1

# The default client drops R2's 429; rate_limited_retry retries it after a delay,
# so the (still failing, rule is persistent) run takes measurably longer.
clear_rules
inject_rule '{"op":"PutObject","status":429}'
t=$(now)
do_archive "$(store_prefix t429-default)" ""
d_rc=$?
d=$(since "$t")
t=$(now)
do_archive "$(store_prefix t429-rlr)" "1000,0"
r_rc=$?
r=$(since "$t")
clear_rules
if [ "$d_rc" -ne 0 ] && [ "$r_rc" -ne 0 ] &&
  awk -v r="$r" -v d="$d" 'BEGIN { exit !(r >= d + 1.2) }'; then
  ok "rate_limited_retry_retries_429_default_does_not"
else
  notok "rate_limited_retry_retries_429_default_does_not" \
    "default rc=$d_rc (${d}s), rate_limited rc=$r_rc (${r}s)"
fi

# A persistent 500 fails the archive; once cleared, a re-run round-trips.
clear_rules
p="$(store_prefix t500)"
inject_rule '{"op":"PutObject","status":500}'
if do_archive "$p" ""; then
  notok "transient_500_fails_then_recovers" "archive unexpectedly succeeded under 500"
else
  clear_rules
  roundtrip "transient_500_fails_then_recovers" "$p"
fi

# Transient errors that clear within the retry budget must not fail the archive.
# Fail PutObject with probability 0.3, capped at 2 failures per object so every
# object still succeeds within max_attempts. Across ~34 objects that is a >99.99%
# chance of at least one retry (1 - 0.7^34), while staying fast -- far cheaper
# than failing every object.
clear_rules
inject_rule '{"op":"PutObject","status":500,"probability":0.3,"max_failures_per_object":2}'
roundtrip "transient_errors_recovered_by_retries" "$(store_prefix retry-heal)"
clear_rules

# A non-retryable 403 fails fast (not retried into a long backoff).
clear_rules
inject_rule '{"op":"PutObject","status":403,"code":"AccessDenied"}'
t=$(now)
do_archive "$(store_prefix t403)" ""
a_rc=$?
e=$(since "$t")
clear_rules
if [ "$a_rc" -ne 0 ] && awk -v e="$e" 'BEGIN { exit !(e < 10) }'; then
  ok "access_denied_fails_fast"
else
  notok "access_denied_fails_fast" "rc=$a_rc, elapsed=${e}s"
fi

# Injected latency should not break the round-trip.
clear_rules
inject_rule '{"op":"*","delay_ms":200}'
roundtrip "latency_injection_still_round_trips" "$(store_prefix latency)"
clear_rules

# A read-path error surfaces: archive succeeds, then a 500 on GetObject fails
# the export.
clear_rules
p="$(store_prefix get-err)"
if ! do_archive "$p" ""; then
  notok "get_object_error_fails_export" "archive failed"
else
  inject_rule '{"op":"GetObject","status":500}'
  if do_export "$p" "$WORK/get-err.raw"; then
    notok "get_object_error_fails_export" "export unexpectedly succeeded"
  else
    ok "get_object_error_fails_export"
  fi
  clear_rules
fi

echo
echo "# $pass passed, $fail failed"
[ "$fail" -eq 0 ]
