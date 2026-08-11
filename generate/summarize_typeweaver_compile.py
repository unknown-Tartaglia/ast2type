#!/usr/bin/env python3
"""Summarize existing TypeWeaver baseline-checked compilation artifacts."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


DIAGNOSTIC_RE = re.compile(r"error TS(\d+):")
METHOD_PATHS = {
    "tsc": "tsc-out/{dataset}/baseline-checked",
    "DeepTyper": "DeepTyper-out/{dataset}/baseline-checked",
    "LambdaNet": "LambdaNet-out/{dataset}/baseline-checked",
    "InCoder": "InCoder-out/{dataset}/baseline-checked",
    "SantaCoder": "SantaCoder-out/{dataset}/baseline-checked",
    "LLM": "LLM-out/{dataset}/baseline-checked",
    "Pipeline-raw": "Pipeline-out/{dataset}-ablation-raw/baseline-checked",
    "Pipeline-fixed": "Pipeline-out/{dataset}-ablation-fixed/baseline-checked",
}


def read_records(directory: Path) -> dict[str, tuple[str, Path]]:
    records = {}
    for suffix, status in (
        (".out", "PASS"),
        (".err", "TYPE_ERROR"),
        (".tool-error", "TOOL_ERROR"),
    ):
        for path in directory.glob(f"*{suffix}"):
            records[path.name[: -len(suffix)]] = (status, path)
    return records


def summarize(method: str, records: dict[str, tuple[str, Path]], packages: set[str]) -> dict:
    pass_count = type_errors = tool_errors = diagnostics = 0
    codes: dict[str, int] = {}
    for package in packages:
        status, path = records[package]
        if status == "PASS":
            pass_count += 1
            continue
        if status == "TOOL_ERROR":
            tool_errors += 1
            continue
        type_errors += 1
        output = path.read_text(encoding="utf-8", errors="replace")
        for code in DIAGNOSTIC_RE.findall(output):
            diagnostics += 1
            codes[code] = codes.get(code, 0) + 1
    total = len(packages)
    return {
        "method": method,
        "packages": total,
        "pass": pass_count,
        "pass_rate": pass_count / total * 100 if total else None,
        "type_error_packages": type_errors,
        "tool_error_packages": tool_errors,
        "diagnostics": diagnostics,
        "diagnostics_per_failed_package": diagnostics / type_errors if type_errors else 0,
        "top_codes": sorted(codes.items(), key=lambda item: (-item[1], item[0]))[:10],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data-root", type=Path, required=True)
    parser.add_argument("--dataset", default="top1k-typed-nodeps-es6")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    data_root = args.data_root.resolve()
    directories = {
        method: data_root / template.format(dataset=args.dataset)
        for method, template in METHOD_PATHS.items()
    }
    missing = [str(path) for path in directories.values() if not path.is_dir()]
    if missing:
        raise FileNotFoundError(f"missing checked directories: {missing}")

    records = {method: read_records(path) for method, path in directories.items()}
    common_packages = set.intersection(*(set(items) for items in records.values()))
    available = [
        summarize(method, items, set(items))
        for method, items in records.items()
    ]
    common = [
        summarize(method, items, common_packages)
        for method, items in records.items()
    ]
    result = {
        "dataset": args.dataset,
        "source": "existing TypeWeaver baseline-checked artifacts",
        "common_package_count": len(common_packages),
        "available_results": available,
        "common_package_results": common,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
