#!/usr/bin/env python3
"""Evaluate ground truth, raw inference, and auto-fixed TS projects."""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from generate.tsc_check import (
    COMMON_FLAGS,
    DECLARATION_FLAGS,
    check_typescript,
    check_typescript_project,
    compiler_path,
    compiler_version,
)
from generate.ts_project_env import project_compile_environment


TS_EXTENSIONS = (".ts", ".tsx", ".mts", ".ets")
DIAGNOSTIC_RE = re.compile(
    r"^(.+?)\((\d+),(\d+)\):\s*error\s+TS(\d+):\s*(.+)$",
    re.MULTILINE,
)
CODE_RE = re.compile(r"error\s+TS(\d+):")


def source_files(project: Path) -> list[str]:
    result = []
    for current, directories, filenames in os.walk(project):
        directories[:] = [name for name in directories if name not in ("node_modules", ".git")]
        for filename in filenames:
            if filename.endswith(TS_EXTENSIONS) and not filename.endswith(".d.ts"):
                result.append(str(Path(current) / filename))
    return sorted(result)


def _command_version(compiler: Path) -> str:
    return compiler_version(compiler)


def evaluate_uniform(
    project: str,
    variant: str,
    directory: Path,
    diagnostics_root: Path,
    timeout: int,
) -> dict:
    files = source_files(directory)
    result = check_typescript(files, timeout=timeout)
    return _result_summary(
        project,
        variant,
        files,
        result,
        diagnostics_root,
        "uniform",
        str(compiler_path()),
        compiler_version(),
        "uniform",
    )


def evaluate_project(
    project: str,
    variant: str,
    directory: Path,
    dependency_project: Path,
    diagnostics_root: Path,
    timeout: int,
) -> dict:
    files = source_files(directory)
    with project_compile_environment(
        project, directory, dependency_project
    ) as profile:
        result = check_typescript_project(
            directory,
            compiler=profile.compiler,
            config=profile.config,
            extra_args=profile.extra_args,
            timeout=timeout,
        )
    return _result_summary(
        project,
        variant,
        files,
        result,
        diagnostics_root,
        "project",
        str(profile.compiler),
        _command_version(profile.compiler),
        profile.environment,
    )


def _result_summary(
    project: str,
    variant: str,
    files: list[str],
    result,
    diagnostics_root: Path,
    contract: str,
    compiler: str,
    version: str,
    environment: str,
) -> dict:
    diagnostics = DIAGNOSTIC_RE.findall(result.output)
    codes: dict[str, int] = {}
    for code in CODE_RE.findall(result.output):
        codes[code] = codes.get(code, 0) + 1

    diagnostics_path = diagnostics_root / variant / f"{project}.txt"
    diagnostics_path.parent.mkdir(parents=True, exist_ok=True)
    diagnostics_path.write_text(result.output, encoding="utf-8")
    return {
        "project": project,
        "variant": variant,
        "contract": contract,
        "environment": environment,
        "compiler": compiler,
        "compiler_version": version,
        "command": list(result.command),
        "status": result.status.value,
        "source_files": len(files),
        "diagnostics": sum(codes.values()),
        "diagnostic_files": len({item[0] for item in diagnostics}),
        "missing_module": codes.get("2307", 0),
        "syntax_diagnostics": sum(count for code, count in codes.items() if int(code) < 2000),
        "top_codes": sorted(codes.items(), key=lambda item: (-item[1], item[0]))[:10],
        "diagnostics_file": str(diagnostics_path),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--experiment-root", type=Path, required=True)
    parser.add_argument("--packages", required=True)
    parser.add_argument(
        "--variants",
        default="groundtruth,raw,fixed",
        help="comma-separated variant directories below the experiment root",
    )
    parser.add_argument("--output-file", type=Path)
    parser.add_argument("--diagnostics-dir", type=Path)
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument(
        "--contract",
        choices=("uniform", "project"),
        default="uniform",
        help="uniform dataset flags or each project's compiler and tsconfig",
    )
    args = parser.parse_args()

    root = args.experiment_root.resolve()
    suffix = "" if args.contract == "uniform" else "-project"
    diagnostics_root = (
        args.diagnostics_dir.resolve()
        if args.diagnostics_dir
        else root / f"compile-diagnostics{suffix}"
    )
    variants = [part.strip() for part in args.variants.split(",") if part.strip()]
    if not variants or len(variants) != len(set(variants)):
        parser.error("variant list must be non-empty and contain no duplicates")
    results = []
    for project in [part.strip() for part in args.packages.split(",") if part.strip()]:
        for variant in variants:
            directory = root / variant / project
            if not directory.is_dir():
                raise FileNotFoundError(directory)
            if args.contract == "project":
                item = evaluate_project(
                    project,
                    variant,
                    directory,
                    root / "groundtruth" / project,
                    diagnostics_root,
                    args.timeout,
                )
            else:
                item = evaluate_uniform(
                    project, variant, directory, diagnostics_root, args.timeout
                )
            results.append(item)
            print(json.dumps(item, ensure_ascii=False), flush=True)

    summary = {
        "contract": args.contract,
        "compiler": str(compiler_path()) if args.contract == "uniform" else "per-project",
        "compiler_version": compiler_version() if args.contract == "uniform" else "per-project",
        "flags": [*COMMON_FLAGS, *DECLARATION_FLAGS] if args.contract == "uniform" else [],
        "variants": variants,
        "results": results,
    }
    output_file = (
        args.output_file.resolve()
        if args.output_file
        else root / f"compile-results{suffix}.json"
    )
    output_file.parent.mkdir(parents=True, exist_ok=True)
    output_file.write_text(
        json.dumps(summary, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
