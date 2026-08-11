#!/usr/bin/env python3
"""Run Auto-fix with each migrated TS project's own compiler environment."""

from __future__ import annotations

import argparse
import json
import shutil
import sys
import time
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from generate.auto_fix import AutoFixStatus, auto_fix_package
from generate.run_auto_fix_all import fingerprint_sources, result_record
from generate.tsc_check import check_typescript_project, compiler_version
from generate.ts_project_env import project_compile_environment


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--experiment-root", type=Path, required=True)
    parser.add_argument("--packages", required=True)
    parser.add_argument("--source-variant", default="raw")
    parser.add_argument("--output-variant", default="fixed-project")
    parser.add_argument("--max-rounds", type=int, default=5)
    parser.add_argument("--timeout", type=int, default=300)
    args = parser.parse_args(argv)

    root = args.experiment_root.resolve()
    source_root = root / args.source_variant
    output_root = root / args.output_variant
    if output_root.exists():
        parser.error(f"output variant already exists: {output_root}")
    if args.max_rounds < 0 or args.timeout <= 0:
        parser.error("max-rounds must be >= 0 and timeout must be > 0")

    projects = [part.strip() for part in args.packages.split(",") if part.strip()]
    if not projects or len(projects) != len(set(projects)):
        parser.error("package list must be non-empty and contain no duplicates")
    output_root.mkdir(parents=True)

    records = []
    for index, project in enumerate(projects, start=1):
        source = source_root / project
        target = output_root / project
        dependencies = root / "groundtruth" / project
        started = time.monotonic()
        source_fingerprint = None
        try:
            if not source.is_dir() or not dependencies.is_dir():
                raise FileNotFoundError(source if not source.is_dir() else dependencies)
            source_fingerprint = fingerprint_sources(source)
            shutil.copytree(
                source,
                target,
                ignore=shutil.ignore_patterns("node_modules", ".git"),
            )
            with project_compile_environment(
                project, target, dependencies
            ) as profile:
                def project_check(_files, timeout):
                    return check_typescript_project(
                        target,
                        compiler=profile.compiler,
                        config=profile.config,
                        extra_args=profile.extra_args,
                        timeout=timeout,
                    )

                result = auto_fix_package(
                    target,
                    max_rounds=args.max_rounds,
                    timeout=args.timeout,
                    type_checker=project_check,
                )
                record = result_record(
                    project,
                    source,
                    target,
                    source_fingerprint,
                    result,
                    time.monotonic() - started,
                )
                record["compiler"] = str(profile.compiler)
                record["compiler_version"] = compiler_version(profile.compiler)
                record["compiler_config"] = str(profile.config)
                record["compiler_extra_args"] = list(profile.extra_args)
                record["environment"] = profile.environment
        except Exception as error:
            record = {
                "package": project,
                "source_dir": str(source),
                "target_dir": str(target),
                "status": "ERROR",
                "initial_status": None,
                "total_files": source_fingerprint["file_count"] if source_fingerprint else 0,
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
            f"[{index:2d}/{len(projects)}] {project:<12} {record['status']:<10} "
            f"errors={record['initial_diagnostics']}->{record['final_diagnostics']} "
            f"edits={record['replacements']}",
            flush=True,
        )

    counts = Counter(record["status"] for record in records)
    manifest = {
        "schema": 1,
        "contract": "project",
        "experiment_root": str(root),
        "source_variant": args.source_variant,
        "output_variant": args.output_variant,
        "packages": projects,
        "max_rounds": args.max_rounds,
        "timeout": args.timeout,
        "status_counts": dict(sorted(counts.items())),
        "results": records,
    }
    results_path = output_root / "auto-fix-results.json"
    results_path.write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(f"results: {results_path}")

    if counts.get("ERROR", 0) or counts.get(AutoFixStatus.TOOL_ERROR.value, 0):
        return 2
    if counts.get(AutoFixStatus.TYPE_ERROR.value, 0):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
