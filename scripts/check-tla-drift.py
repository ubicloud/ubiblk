#!/usr/bin/env python3
"""
TLA+ Structural Drift Detection Tool

Detects when Rust code changes might invalidate TLA+ models by:
1. Checking constants in Rust code match declared TLA+ values
2. Checking enum/state values match declared TLA+ values
3. Checking memory ordering patterns are preserved
4. Detecting when modeled Rust files have changed (via git diff)

Usage:
    # Check for all drift (constants, enums, orderings, file changes)
    python3 scripts/check-tla-drift.py --repo ~/ubiblk

    # Check only constant/enum values (no git)
    python3 scripts/check-tla-drift.py --repo ~/ubiblk --values-only

    # Check only file changes against a base ref
    python3 scripts/check-tla-drift.py --repo ~/ubiblk --base-ref main

    # Machine-readable JSON output
    python3 scripts/check-tla-drift.py --repo ~/ubiblk --json

Exit codes:
    0 - No drift detected
    1 - Drift detected
    2 - Configuration or runtime error
"""

import argparse
import json
import os
import re
import subprocess
import sys
import tomllib
from dataclasses import dataclass, field
from pathlib import Path


@dataclass
class DriftIssue:
    category: str  # "constant", "enum", "ordering", "file_changed"
    severity: str  # "error" (value mismatch), "warning" (file changed)
    spec: str      # TLA+ spec affected
    message: str
    file: str = ""
    detail: str = ""


@dataclass
class DriftReport:
    issues: list[DriftIssue] = field(default_factory=list)

    @property
    def has_errors(self) -> bool:
        return any(i.severity == "error" for i in self.issues)

    @property
    def has_warnings(self) -> bool:
        return any(i.severity == "warning" for i in self.issues)

    @property
    def has_drift(self) -> bool:
        return len(self.issues) > 0

    def to_dict(self) -> dict:
        return {
            "drift_detected": self.has_drift,
            "errors": sum(1 for i in self.issues if i.severity == "error"),
            "warnings": sum(1 for i in self.issues if i.severity == "warning"),
            "issues": [
                {
                    "category": i.category,
                    "severity": i.severity,
                    "spec": i.spec,
                    "message": i.message,
                    "file": i.file,
                    "detail": i.detail,
                }
                for i in self.issues
            ],
        }


def load_manifest(manifest_path: Path) -> dict:
    with open(manifest_path, "rb") as f:
        return tomllib.load(f)


def read_file(path: Path) -> str:
    with open(path, "r") as f:
        return f.read()


def check_constants(manifest: dict, repo_root: Path, report: DriftReport):
    for const in manifest.get("constant", []):
        tla_name = const["tla_name"]
        tla_value = const["tla_value"]
        rust_file = repo_root / const["rust_file"]
        rust_pattern = const["rust_pattern"]
        specs = const.get("specs", [])

        if not rust_file.exists():
            for spec in specs:
                report.issues.append(DriftIssue(
                    category="constant",
                    severity="error",
                    spec=spec,
                    message=f"Rust file not found for constant {tla_name}",
                    file=str(const["rust_file"]),
                ))
            continue

        content = read_file(rust_file)
        match = re.search(rust_pattern, content)
        if not match:
            for spec in specs:
                report.issues.append(DriftIssue(
                    category="constant",
                    severity="error",
                    spec=spec,
                    message=f"Constant {tla_name} pattern not found in Rust code",
                    file=str(const["rust_file"]),
                    detail=f"Pattern: {rust_pattern}",
                ))
            continue

        rust_value = match.group(1)
        if rust_value != tla_value:
            for spec in specs:
                report.issues.append(DriftIssue(
                    category="constant",
                    severity="error",
                    spec=spec,
                    message=f"Constant {tla_name} mismatch: TLA+={tla_value}, Rust={rust_value}",
                    file=str(const["rust_file"]),
                    detail=f"Update TLA+ spec or Rust code to match",
                ))


def check_enums(manifest: dict, repo_root: Path, report: DriftReport):
    for enum in manifest.get("enum", []):
        name = enum["name"]
        tla_values = enum["tla_values"]
        rust_file = repo_root / enum["rust_file"]
        rust_patterns = enum["rust_patterns"]
        specs = enum.get("specs", [])

        if not rust_file.exists():
            for spec in specs:
                report.issues.append(DriftIssue(
                    category="enum",
                    severity="error",
                    spec=spec,
                    message=f"Rust file not found for enum {name}",
                    file=str(enum["rust_file"]),
                ))
            continue

        content = read_file(rust_file)

        for tla_val, rust_pat in zip(tla_values, rust_patterns):
            variant_name, expected_val = tla_val.split("=")
            match = re.search(rust_pat, content)

            if not match:
                for spec in specs:
                    report.issues.append(DriftIssue(
                        category="enum",
                        severity="error",
                        spec=spec,
                        message=f"Enum {name}.{variant_name} pattern not found",
                        file=str(enum["rust_file"]),
                        detail=f"Pattern: {rust_pat}",
                    ))
                continue

            rust_val = match.group(1)

            # Handle bit-shift patterns: the pattern captures the shift amount
            # e.g., FETCHED = 1 << 0 captures "0", but TLA+ value is "1"
            if "<<" in rust_pat:
                rust_val = str(1 << int(rust_val))

            if rust_val != expected_val:
                for spec in specs:
                    report.issues.append(DriftIssue(
                        category="enum",
                        severity="error",
                        spec=spec,
                        message=f"Enum {name}.{variant_name} mismatch: TLA+={expected_val}, Rust={rust_val}",
                        file=str(enum["rust_file"]),
                        detail=f"Update TLA+ spec or Rust code to match",
                    ))


def check_orderings(manifest: dict, repo_root: Path, report: DriftReport):
    for ordering in manifest.get("ordering", []):
        name = ordering["name"]
        rust_file = repo_root / ordering["rust_file"]
        rust_pattern = ordering["rust_pattern"]
        specs = ordering.get("specs", [])
        description = ordering.get("description", "")

        if not rust_file.exists():
            for spec in specs:
                report.issues.append(DriftIssue(
                    category="ordering",
                    severity="error",
                    spec=spec,
                    message=f"Rust file not found for ordering check {name}",
                    file=str(ordering["rust_file"]),
                ))
            continue

        content = read_file(rust_file)
        if not re.search(rust_pattern, content):
            for spec in specs:
                report.issues.append(DriftIssue(
                    category="ordering",
                    severity="error",
                    spec=spec,
                    message=f"Memory ordering pattern '{name}' not found",
                    file=str(ordering["rust_file"]),
                    detail=f"{description}. Pattern: {rust_pattern}",
                ))


def get_changed_files(repo_root: Path, base_ref: str) -> set[str]:
    try:
        result = subprocess.run(
            ["git", "diff", "--name-only", base_ref],
            cwd=repo_root,
            capture_output=True,
            text=True,
            timeout=10,
        )
        if result.returncode != 0:
            return set()
        return {line.strip() for line in result.stdout.splitlines() if line.strip()}
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return set()


def check_file_changes(manifest: dict, repo_root: Path, base_ref: str, report: DriftReport):
    changed = get_changed_files(repo_root, base_ref)
    if not changed:
        return

    tla_dir = Path(__file__).resolve().parent.parent / "tla"

    for mapping in manifest.get("mapping", []):
        tla_spec = mapping["tla_spec"]
        rust_files = mapping["rust_files"]
        description = mapping.get("description", "")

        changed_rust = [f for f in rust_files if f in changed]
        if not changed_rust:
            continue

        # Check if the TLA+ spec was also changed
        tla_changed = any(
            f"tla/{tla_spec}" in changed or tla_spec in changed
            for _ in [None]
        )

        if tla_changed:
            continue  # Spec was also updated, probably OK

        for rust_file in changed_rust:
            report.issues.append(DriftIssue(
                category="file_changed",
                severity="warning",
                spec=tla_spec,
                message=f"Modeled file changed without TLA+ spec update",
                file=rust_file,
                detail=f"Spec '{tla_spec}' ({description}) may need review",
            ))


def print_report(report: DriftReport, use_json: bool):
    if use_json:
        print(json.dumps(report.to_dict(), indent=2))
        return

    if not report.has_drift:
        print("No TLA+ drift detected.")
        return

    errors = [i for i in report.issues if i.severity == "error"]
    warnings = [i for i in report.issues if i.severity == "warning"]

    if errors:
        print(f"\n{'='*60}")
        print(f"  ERRORS: {len(errors)} value mismatch(es) detected")
        print(f"{'='*60}")
        for issue in errors:
            print(f"\n  [{issue.category}] {issue.message}")
            print(f"    Spec: {issue.spec}")
            if issue.file:
                print(f"    File: {issue.file}")
            if issue.detail:
                print(f"    {issue.detail}")

    if warnings:
        print(f"\n{'='*60}")
        print(f"  WARNINGS: {len(warnings)} file change(s) may affect TLA+ specs")
        print(f"{'='*60}")

        # Group by spec
        specs_affected: dict[str, list[DriftIssue]] = {}
        for issue in warnings:
            specs_affected.setdefault(issue.spec, []).append(issue)

        for spec, issues in specs_affected.items():
            print(f"\n  {spec}:")
            for issue in issues:
                print(f"    - {issue.file}")
            if issues[0].detail:
                print(f"    {issues[0].detail}")

    print(f"\nSummary: {len(errors)} error(s), {len(warnings)} warning(s)")


def main():
    parser = argparse.ArgumentParser(
        description="Detect structural drift between TLA+ specs and Rust code"
    )
    parser.add_argument(
        "--repo",
        type=Path,
        default=Path.home() / "ubiblk",
        help="Path to ubiblk repo root (default: ~/ubiblk)",
    )
    parser.add_argument(
        "--manifest",
        type=Path,
        default=None,
        help="Path to code-mapping.toml (default: tla/code-mapping.toml)",
    )
    parser.add_argument(
        "--base-ref",
        type=str,
        default="HEAD~1",
        help="Git ref to diff against for file change detection (default: HEAD~1)",
    )
    parser.add_argument(
        "--values-only",
        action="store_true",
        help="Only check constant/enum values, skip git file change detection",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output results as JSON",
    )
    args = parser.parse_args()

    # Resolve manifest path
    if args.manifest:
        manifest_path = args.manifest
    else:
        script_dir = Path(__file__).resolve().parent
        manifest_path = script_dir.parent / "tla" / "code-mapping.toml"

    if not manifest_path.exists():
        print(f"Error: manifest not found at {manifest_path}", file=sys.stderr)
        sys.exit(2)

    if not args.repo.exists():
        print(f"Error: repo not found at {args.repo}", file=sys.stderr)
        sys.exit(2)

    manifest = load_manifest(manifest_path)
    report = DriftReport()

    # Always check values
    check_constants(manifest, args.repo, report)
    check_enums(manifest, args.repo, report)
    check_orderings(manifest, args.repo, report)

    # Optionally check file changes
    if not args.values_only:
        check_file_changes(manifest, args.repo, args.base_ref, report)

    print_report(report, args.json)

    if report.has_errors:
        sys.exit(1)
    elif report.has_warnings:
        sys.exit(1)
    else:
        sys.exit(0)


if __name__ == "__main__":
    main()
