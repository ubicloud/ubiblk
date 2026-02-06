#!/usr/bin/env bash
#
# Validate an NDJSON trace file against the MetadataDurability TLA+ spec.
#
# Usage:
#   ./scripts/validate-trace.sh trace.ndjson
#
# Environment:
#   TLA2TOOLS_JAR  - path to tla2tools.jar (default: tla2tools.jar in current dir)
#   TLA_DIR        - path to TLA+ specs directory (default: tla/)
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TLA_DIR="${TLA_DIR:-tla}"
TLA2TOOLS_JAR="${TLA2TOOLS_JAR:-tla2tools.jar}"

TRACE_FILE="${1:-}"
if [ -z "$TRACE_FILE" ]; then
    echo "Usage: $0 <trace.ndjson>"
    exit 1
fi

if [ ! -f "$TRACE_FILE" ]; then
    echo "Error: trace file not found: $TRACE_FILE"
    exit 1
fi

TRACE_FILE="$(cd "$(dirname "$TRACE_FILE")" && pwd)/$(basename "$TRACE_FILE")"

echo "=== TLA+ Trace Validation ==="
echo "Trace file: $TRACE_FILE"
echo "TLA+ dir:   $TLA_DIR"
echo ""

# Step 1: Generate the trace validation spec
echo "--- Generating TraceValidation.tla ---"
python3 "$SCRIPT_DIR/trace2tla.py" "$TRACE_FILE" "$TLA_DIR"
echo ""

# Step 2: Run TLC
echo "--- Running TLC model checker ---"
cd "$TLA_DIR"
java -XX:+UseParallelGC -cp "$TLA2TOOLS_JAR" tlc2.TLC \
    -config TraceValidation.cfg \
    -nowarning \
    -workers 1 \
    TraceValidation.tla 2>&1

TLC_EXIT=$?
echo ""

if [ $TLC_EXIT -eq 0 ]; then
    echo "=== PASS: Trace is a valid behavior of MetadataDurability ==="
else
    echo "=== FAIL: Trace validation failed (exit code $TLC_EXIT) ==="
    exit 1
fi
