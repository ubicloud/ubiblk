#!/usr/bin/env bash
#
# Run TLC model checker on all TLA+ specs.
#
# Usage:
#   ./scripts/run-tla-checks.sh              # Fast configs (CI)
#   ./scripts/run-tla-checks.sh --nightly    # Large configs (nightly)
#   ./scripts/run-tla-checks.sh --list       # List all spec/config pairs
#
# Environment:
#   TLA2TOOLS_JAR  - path to tla2tools.jar (default: tla2tools.jar in current dir)
#   TLA_DIR        - path to TLA+ specs directory (default: tla/)
#
set -euo pipefail

TLA2TOOLS_JAR="${TLA2TOOLS_JAR:-tla2tools.jar}"
TLA_DIR="${TLA_DIR:-tla}"
MODE="fast"

for arg in "$@"; do
    case "$arg" in
        --nightly) MODE="nightly" ;;
        --list) MODE="list" ;;
        --help|-h)
            echo "Usage: $0 [--nightly|--list]"
            echo "  (default)  Run fast configs for CI"
            echo "  --nightly  Run large configs for nightly"
            echo "  --list     List all spec/config pairs"
            exit 0
            ;;
        *) echo "Unknown argument: $arg"; exit 1 ;;
    esac
done

# Spec -> fast config, full config, expected result
# Format: "SpecName:fast_config:full_config[:xfail]"
# Use "-" for full_config when there is no large config.
# Use "xfail" suffix for specs that model known bugs and are expected to fail.
SPECS=(
    "MetadataDurability:MetadataDurability.cfg:MetadataDurability_Large.cfg"
    "StripeStateTransitions:StripeStateTransitions.cfg:StripeStateTransitions_Large.cfg"
    "GuestFlushDurability:GuestFlushDurability.cfg:GuestFlushDurability_Large.cfg"
    "LivenessSpec:LivenessSpec.cfg:LivenessSpec_Large.cfg"
    "MetadataLiveness:MetadataLiveness_safety.cfg:MetadataLiveness_full.cfg"
    "LivenessMixed:LivenessMixed.cfg:-:xfail"
    "LivenessMixedFixed:LivenessMixedFixed.cfg:LivenessMixedFixed_Large.cfg"
)

if [ "$MODE" = "list" ]; then
    printf "%-25s %-35s %-35s %-8s\n" "SPEC" "FAST CONFIG" "FULL CONFIG" "XFAIL"
    printf "%-25s %-35s %-35s %-8s\n" "----" "-----------" "-----------" "-----"
    for entry in "${SPECS[@]}"; do
        IFS=: read -r spec fast full xfail <<< "$entry"
        printf "%-25s %-35s %-35s %-8s\n" "$spec" "$fast" "$full" "${xfail:-}"
    done
    exit 0
fi

# Verify tla2tools.jar exists
if [ ! -f "$TLA2TOOLS_JAR" ]; then
    echo "ERROR: tla2tools.jar not found at: $TLA2TOOLS_JAR"
    echo "Set TLA2TOOLS_JAR environment variable or place tla2tools.jar in current directory."
    exit 1
fi

# Verify TLA+ directory exists
if [ ! -d "$TLA_DIR" ]; then
    echo "ERROR: TLA+ directory not found at: $TLA_DIR"
    echo "Set TLA_DIR environment variable."
    exit 1
fi

FAILED=0
PASSED=0
SKIPPED=0
XFAILED=0
TOTAL=${#SPECS[@]}

echo "=== TLC Model Checking ($MODE mode) ==="
echo "TLA+ dir: $TLA_DIR"
echo "tla2tools: $TLA2TOOLS_JAR"
echo ""

for entry in "${SPECS[@]}"; do
    IFS=: read -r spec fast full xfail <<< "$entry"
    expect_fail="${xfail:-}"

    if [ "$MODE" = "nightly" ]; then
        cfg="$full"
    else
        cfg="$fast"
    fi

    # Skip if no config for this mode
    if [ "$cfg" = "-" ]; then
        echo "--- SKIP: $spec (no $MODE config)"
        SKIPPED=$((SKIPPED + 1))
        continue
    fi

    tla_file="$TLA_DIR/$spec.tla"
    cfg_file="$TLA_DIR/$cfg"

    if [ ! -f "$tla_file" ]; then
        echo "--- FAIL: $spec - spec file not found: $tla_file"
        FAILED=$((FAILED + 1))
        continue
    fi

    if [ ! -f "$cfg_file" ]; then
        echo "--- FAIL: $spec - config not found: $cfg_file"
        FAILED=$((FAILED + 1))
        continue
    fi

    if [ "$expect_fail" = "xfail" ]; then
        echo "--- RUN:  $spec ($cfg) [expected fail - models known bug]"
    else
        echo "--- RUN:  $spec ($cfg)"
    fi
    start_time=$(date +%s)

    # Run TLC with auto workers, no deadlock checking (liveness specs may terminate)
    if java -cp "$TLA2TOOLS_JAR" tlc2.TLC \
        -config "$cfg_file" \
        -workers auto \
        -deadlock \
        "$tla_file" 2>&1 | tee /tmp/tlc-$spec.log | tail -5; then
        elapsed=$(( $(date +%s) - start_time ))
        if [ "$expect_fail" = "xfail" ]; then
            echo "--- XPASS: $spec (${elapsed}s) [expected to fail but passed - update SPECS list!]"
            FAILED=$((FAILED + 1))
        else
            echo "--- PASS: $spec (${elapsed}s)"
            PASSED=$((PASSED + 1))
        fi
    else
        elapsed=$(( $(date +%s) - start_time ))
        if [ "$expect_fail" = "xfail" ]; then
            echo ""
            echo "--- XFAIL: $spec (${elapsed}s) [expected failure - models known bug]"
            XFAILED=$((XFAILED + 1))
        else
            echo ""
            echo "--- FAIL: $spec (${elapsed}s)"
            echo "Full output saved to /tmp/tlc-$spec.log"
            # Print the last 30 lines for context on failure
            echo "=== Last 30 lines of output ==="
            tail -30 /tmp/tlc-$spec.log
            echo "=== End of output ==="
            FAILED=$((FAILED + 1))
        fi
    fi

    echo ""
done

echo "=== Results ==="
echo "Total: $TOTAL  Passed: $PASSED  Failed: $FAILED  Expected-fail: $XFAILED  Skipped: $SKIPPED"

if [ "$FAILED" -gt 0 ]; then
    echo "FAIL: $FAILED spec(s) failed model checking."
    exit 1
fi

echo "OK: All specs passed."
exit 0
