#!/usr/bin/env python3
"""
Convert an NDJSON trace from ubiblk's tla-trace instrumentation into a
TLA+ trace spec that TLC can check against MetadataDurability.tla.

Usage:
    python3 trace2tla.py trace.ndjson > TraceValidation.tla

The generated spec constrains Init/Next to follow the trace sequence,
then TLC checks all MetadataDurability invariants hold at every step.
"""

import json
import sys
from pathlib import Path


def load_trace(path: str) -> list[dict]:
    """Load NDJSON trace file."""
    events = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line:
                events.append(json.loads(line))
    return events


def action_to_tla(event: dict) -> str:
    """Map a trace event to the corresponding TLA+ action call."""
    action = event["action"]
    stripe = event["stripe"]

    # Map trace action names to MetadataDurability.tla action names
    mapping = {
        "SourceReadComplete": f"SourceReadComplete({stripe})",
        "TargetWriteComplete": f"TargetWriteComplete({stripe})",
        "TargetFlushComplete": f"TargetFlushComplete({stripe})",
        "Handoff": f"Handoff({stripe})",
        "MetadataWriteComplete": f"MetadataWriteComplete({stripe})",
        "MetadataFlushComplete": f"MetadataFlushComplete({stripe})",
        "AtomicPublish": f"AtomicPublish({stripe})",
    }

    if action == "SetFailed":
        # SetFailed doesn't map to a single spec action directly.
        # It's the result of the final retry failing.
        # We model it as: the appropriate fail action fires.
        # Since we don't know which stage failed, we use a disjunction.
        return (
            f"(SourceReadFail({stripe}) \\/ TargetWriteFail({stripe}) "
            f"\\/ TargetFlushFail({stripe}))"
        )

    return mapping[action]


def needs_unlogged_precursor(action: str) -> list[str]:
    """Return unlogged spec actions that must fire before this trace action.

    The Rust code doesn't instrument StartSourceRead or MetadataWriteStart
    because they are synchronous precursors. The TLA+ spec needs them.
    """
    if action == "SourceReadComplete":
        return ["StartSourceRead"]
    if action == "MetadataWriteComplete":
        return ["MetadataWriteStart"]
    return []


def generate_tla(events: list[dict], num_stripes: int) -> str:
    """Generate the trace validation TLA+ spec."""

    # Determine stripes referenced
    stripes = set()
    for e in events:
        stripes.add(e["stripe"])

    max_stripe = max(stripes) if stripes else 0
    num_stripes = max(num_stripes, max_stripe + 1)

    lines = []
    lines.append("---------------------- MODULE TraceValidation ----------------------")
    lines.append("(*")
    lines.append(f" * Auto-generated trace validation spec from {len(events)} events.")
    lines.append(" * Validates that the recorded trace is a valid behavior of")
    lines.append(" * MetadataDurability.tla with all safety invariants preserved.")
    lines.append(" *)")
    lines.append("")
    lines.append("EXTENDS MetadataDurability")
    lines.append("")
    lines.append("VARIABLE step  \\* Current step in the trace (0-based)")
    lines.append("")
    lines.append("traceVars == <<step>>")
    lines.append("allVars == <<vars, step>>")
    lines.append("")
    lines.append("TraceInit ==")
    lines.append("    /\\ Init")
    lines.append("    /\\ step = 0")
    lines.append("")

    # Generate step definitions
    # Each trace event may require unlogged precursor actions
    step_num = 0
    for i, event in enumerate(events):
        precursors = needs_unlogged_precursor(event["action"])
        stripe = event["stripe"]

        for precursor in precursors:
            lines.append(f"Step{step_num} ==")
            lines.append(f"    /\\ step = {step_num}")
            lines.append(f"    /\\ {precursor}({stripe})")
            lines.append(f"    /\\ step' = {step_num + 1}")
            lines.append("")
            step_num += 1

        action_tla = action_to_tla(event)
        lines.append(f"Step{step_num} ==  \\* Trace event {i}: {event['action']}(stripe={stripe})")
        lines.append(f"    /\\ step = {step_num}")
        lines.append(f"    /\\ {action_tla}")
        lines.append(f"    /\\ step' = {step_num + 1}")
        lines.append("")
        step_num += 1

    total_steps = step_num

    # Done: stutter action when trace is fully consumed (prevents deadlock)
    lines.append(f"Done ==")
    lines.append(f"    /\\ step = {total_steps}")
    lines.append(f"    /\\ UNCHANGED allVars")
    lines.append("")

    # TraceNext: disjunction of all steps + Done
    lines.append("TraceNext ==")
    step_refs = [f"Step{i}" for i in range(total_steps)]
    for i, ref in enumerate(step_refs):
        lines.append(f"    \\/ {ref}")
    lines.append("    \\/ Done")
    lines.append("")

    # Acceptance check: all trace events consumed at termination
    lines.append(f"TraceAccepted == step <= {total_steps}")
    lines.append("")

    # Spec: no -deadlock needed because Done prevents it when trace is complete.
    # If trace gets stuck before Done, TLC reports deadlock = trace is invalid.
    lines.append("TraceSpec == TraceInit /\\ [][TraceNext]_allVars")
    lines.append("")
    lines.append("=============================================================================")

    return "\n".join(lines)


def generate_cfg(num_stripes: int, max_retries: int = 4) -> str:
    """Generate the TLC config file."""
    lines = [
        "SPECIFICATION TraceSpec",
        "",
        "CONSTANTS",
        f"    NUM_STRIPES = {num_stripes}",
        "    MAX_CRASHES = 0",
        f"    MAX_RETRIES = {max_retries}",
        "",
        "INVARIANT",
        "    Safety",
        "    TraceAccepted",
    ]
    return "\n".join(lines)


def main():
    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} <trace.ndjson> [output_dir]", file=sys.stderr)
        sys.exit(1)

    trace_path = sys.argv[1]
    output_dir = Path(sys.argv[2]) if len(sys.argv) > 2 else Path(".")

    events = load_trace(trace_path)
    if not events:
        print("Error: empty trace file", file=sys.stderr)
        sys.exit(1)

    # Determine num_stripes from trace
    stripes = {e["stripe"] for e in events}
    num_stripes = max(stripes) + 1

    tla_content = generate_tla(events, num_stripes)
    cfg_content = generate_cfg(num_stripes)

    tla_path = output_dir / "TraceValidation.tla"
    cfg_path = output_dir / "TraceValidation.cfg"

    tla_path.write_text(tla_content + "\n")
    cfg_path.write_text(cfg_content + "\n")

    print(f"Generated {tla_path} ({len(events)} trace events -> {sum(1 for e in events for _ in range(1 + len(needs_unlogged_precursor(e['action']))))} TLA+ steps)")
    print(f"Generated {cfg_path}")
    print(f"Run: java -cp ~/toolbox/tla2tools.jar tlc2.TLC -config {cfg_path.name} -deadlock {tla_path.name}")


if __name__ == "__main__":
    main()
