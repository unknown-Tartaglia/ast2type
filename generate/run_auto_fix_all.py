#!/usr/bin/env python3
"""Run conservative auto-fix over package copies and persist a run manifest."""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import sys
import time
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path


ROOT_DIR = Path(__file__).resolve().parent.parent
if str(ROOT_DIR) not in sys.path:
    sys.path.insert(0, str(ROOT_DIR))

from generate.auto_fix import AutoFixResult, AutoFixStatus, auto_fix_package
from generate.tsc_check import (
    COMMON_FLAGS,
    DECLARATION_FLAGS,
    compiler_path,
    compiler_version,
    discover_typescript_files,
)

DEFAULT_BASELINE_DIR = (
    ROOT_DIR.parent
    / "TypeWeaver"
    / "data"
    / "Pipeline-out"
    / "top1k-typed-nodeps-es6"
    / "baseline"
)


def discover_packages(baseline_dir: Path) -> list[str]:
    packages = []
    for entry in sorted(baseline_dir.iterdir(), key=lambda path: path.name):
        if not entry.is_dir():
            continue
        if entry.name.startswith("@"):
            for child in sorted(entry.iterdir(), key=lambda path: path.name):
                if child.is_dir() and discover_typescript_files(child):
                    packages.append(f"{entry.name}/{child.name}")
        elif discover_typescript_files(entry):
            packages.append(entry.name)
    return packages


def resolve_package(baseline_dir: Path, name: str) -> Path:
    relative = Path(name)
    if relative.is_absolute() or not relative.parts or ".." in relative.parts:
        raise ValueError(f"invalid package path: {name}")
    source = (baseline_dir / relative).resolve()
    try:
        source.relative_to(baseline_dir.resolve())
    except ValueError as error:
        raise ValueError(f"package escapes baseline: {name}") from error
    if not source.is_dir():
        raise FileNotFoundError(source)
    return source


def fingerprint_sources(package_dir: Path) -> dict:
    digest = hashlib.sha256()
    files = discover_typescript_files(package_dir)
    for filename in files:
        path = Path(filename)
        relative = path.relative_to(package_dir.resolve()).as_posix()
        digest.update(relative.encode("utf-8"))
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return {"file_count": len(files), "sha256": digest.hexdigest()}


def result_record(
    name: str,
    source: Path,
    target: Path,
    source_fingerprint: dict,
    result: AutoFixResult,
    elapsed: float,
) -> dict:
    target_root = target.resolve()
    modified = []
    for filename in result.modified_paths:
        path = Path(filename).resolve()
        try:
            modified.append(path.relative_to(target_root).as_posix())
        except ValueError:
            modified.append(str(path))
    return {
        "package": name,
        "source_dir": str(source),
        "target_dir": str(target),
        "status": result.status.value,
        "initial_status": result.initial_status.value,
        "total_files": result.total_files,
        "checks": result.checks,
        "fix_rounds": result.fix_rounds,
        "modified_files": result.modified_files,
        "replacements": result.replacements,
        "initial_diagnostics": result.initial_diagnostics,
        "final_diagnostics": result.final_diagnostics,
        "skipped_diagnostics": result.skipped_diagnostics,
        "modified_paths": modified,
        "source_fingerprint": source_fingerprint,
        "target_fingerprint": fingerprint_sources(target),
        "elapsed_seconds": round(elapsed, 6),
        "message": result.message[:4000],
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline-dir", type=Path, default=DEFAULT_BASELINE_DIR)
    parser.add_argument("--packages", help="comma-separated package paths")
    destination = parser.add_mutually_exclusive_group()
    destination.add_argument("--output-dir", type=Path)
    destination.add_argument(
        "--in-place",
        action="store_true",
        help="explicitly modify baseline packages instead of copying them",
    )
    parser.add_argument("--results", type=Path)
    parser.add_argument("--max-rounds", type=int, default=5)
    parser.add_argument("--timeout", type=int, default=120)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    baseline = args.baseline_dir.resolve()
    if not baseline.is_dir():
        parser.error(f"baseline directory does not exist: {baseline}")
    if args.max_rounds < 0 or args.timeout <= 0:
        parser.error("max-rounds must be >= 0 and timeout must be > 0")

    names = (
        [part.strip() for part in args.packages.split(",") if part.strip()]
        if args.packages
        else discover_packages(baseline)
    )
    if not names:
        parser.error("no TypeScript packages found")
    if len(names) != len(set(names)):
        parser.error("package list contains duplicates")
    try:
        sources = {name: resolve_package(baseline, name) for name in names}
    except (ValueError, FileNotFoundError) as error:
        parser.error(str(error))

    started_at = datetime.now(timezone.utc)
    if args.in_place:
        output_root = baseline
    else:
        output_root = (
            args.output_dir.resolve()
            if args.output_dir
            else baseline.with_name(f"{baseline.name}-fixed")
        )
        if output_root.exists():
            parser.error(f"output directory already exists: {output_root}")
        try:
            output_root.relative_to(baseline)
        except ValueError:
            pass
        else:
            parser.error("output directory must not be inside the baseline")

    if args.results:
        results_path = args.results.resolve()
    elif args.in_place:
        stamp = started_at.strftime("%Y%m%dT%H%M%SZ")
        results_path = baseline.parent / f"{baseline.name}-auto-fix-{stamp}.json"
    else:
        results_path = output_root / "auto-fix-results.json"
    # Refuse every output collision before copying or modifying a package.
    if results_path.exists():
        parser.error(f"results file already exists: {results_path}")
    try:
        results_path.relative_to(baseline)
    except ValueError:
        pass
    else:
        parser.error("results file must not be inside the baseline")

    targets = [
        source if args.in_place else (output_root / name).resolve()
        for name, source in sources.items()
    ]
    for target in targets:
        # Either direction is unsafe: the manifest could overwrite a source,
        # or become a file where copytree later needs a directory.
        if (results_path == target
                or target in results_path.parents
                or results_path in target.parents):
            parser.error(f"results file overlaps package output: {target}")

    if not args.in_place:
        output_root.mkdir(parents=True)

    records = []
    for index, name in enumerate(names, start=1):
        source = sources[name]
        target = source if args.in_place else output_root / name
        source_fingerprint = None
        started = time.monotonic()
        try:
            source_fingerprint = fingerprint_sources(source)
            if not args.in_place:
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copytree(
                    source,
                    target,
                    ignore=shutil.ignore_patterns("node_modules", ".git"),
                )
            result = auto_fix_package(
                target,
                max_rounds=args.max_rounds,
                timeout=args.timeout,
            )
            record = result_record(
                name,
                source,
                target,
                source_fingerprint,
                result,
                time.monotonic() - started,
            )
        except Exception as error:
            record = {
                "package": name,
                "source_dir": str(source),
                "target_dir": str(target),
                "status": "ERROR",
                "initial_status": None,
                "total_files": (
                    source_fingerprint["file_count"]
                    if source_fingerprint is not None
                    else 0
                ),
                "checks": 0,
                "fix_rounds": 0,
                "modified_files": 0,
                "replacements": 0,
                "initial_diagnostics": 0,
                "final_diagnostics": 0,
                "skipped_diagnostics": 0,
                "modified_paths": [],
                "source_fingerprint": source_fingerprint,
                "target_fingerprint": None,
                "elapsed_seconds": round(time.monotonic() - started, 6),
                "message": str(error),
            }
        records.append(record)
        print(
            f"[{index:3d}/{len(names)}] {name:<30} {record['status']:<10} "
            f"files={record.get('modified_files', 0)}/{record.get('total_files', 0)} "
            f"edits={record.get('replacements', 0)}",
            flush=True,
        )

    counts = Counter(record["status"] for record in records)
    finished_at = datetime.now(timezone.utc)
    manifest = {
        "schema": 1,
        "started_at": started_at.isoformat(),
        "finished_at": finished_at.isoformat(),
        "baseline_dir": str(baseline),
        "output_dir": str(output_root),
        "in_place": args.in_place,
        "packages": names,
        "max_rounds": args.max_rounds,
        "timeout": args.timeout,
        "compiler": {
            "path": str(compiler_path()),
            "version": compiler_version(),
            "flags": [*COMMON_FLAGS, *DECLARATION_FLAGS],
        },
        "status_counts": dict(sorted(counts.items())),
        "results": records,
    }
    results_path.parent.mkdir(parents=True, exist_ok=True)
    results_path.write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(f"results: {results_path}")

    if counts.get("TOOL_ERROR", 0) or counts.get("ERROR", 0):
        return 2
    if counts.get(AutoFixStatus.TYPE_ERROR.value, 0) or counts.get(AutoFixStatus.EMPTY.value, 0):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
