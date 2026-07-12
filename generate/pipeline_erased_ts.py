#!/usr/bin/env python3
"""Run type erasure, inference, and annotation restoration on TS projects."""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from generate.weave_erased_ts import weave_project


TS_EXTENSIONS = {".ts", ".tsx", ".mts", ".cts", ".ets"}
INFERENCE_MANIFEST = "inference-manifest.json"


def _run(command: list[str], timeout: int) -> None:
    print("  cmd:", " ".join(command), flush=True)
    completed = subprocess.run(command, cwd=ROOT, timeout=timeout)
    if completed.returncode != 0:
        raise RuntimeError(f"command failed ({completed.returncode}): {' '.join(command)}")


def _assert_same_erased_sources(current: Path, previous: Path) -> None:
    current_files = {
        path.relative_to(current): path
        for path in current.rglob("*")
        if path.is_file() and path.suffix in TS_EXTENSIONS
    }
    previous_files = {
        path.relative_to(previous): path
        for path in previous.rglob("*")
        if path.is_file() and path.suffix in TS_EXTENSIONS
    }
    if current_files.keys() != previous_files.keys():
        raise RuntimeError("erased source file sets differ; inference cannot be reused")
    changed = [
        str(relpath)
        for relpath in current_files
        if current_files[relpath].read_bytes() != previous_files[relpath].read_bytes()
    ]
    if changed:
        raise RuntimeError(f"erased sources changed; inference cannot be reused: {changed[:5]}")


def _manifest(use_agent: bool) -> dict:
    return {
        "schema": 1,
        "agent": use_agent,
        "agentCandidateMode": "fair" if use_agent else None,
    }


def _write_manifest(inference: Path, use_agent: bool) -> None:
    (inference / INFERENCE_MANIFEST).write_text(
        json.dumps(_manifest(use_agent), indent=2),
        encoding="utf-8",
    )


def _assert_compatible_inference(inference: Path, use_agent: bool) -> None:
    manifest_path = inference / INFERENCE_MANIFEST
    if not manifest_path.is_file():
        raise RuntimeError(f"reused inference has no mode manifest: {manifest_path}")
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    if manifest != _manifest(use_agent):
        requested = "agent" if use_agent else "standard"
        previous = "agent" if manifest.get("agent") else "standard"
        raise RuntimeError(
            f"cannot reuse {previous} inference for a {requested} run"
        )


def _require_inference(inference: Path) -> None:
    required = [inference / "typegraph.json", inference / "typeinfo.json"]
    missing = [str(path) for path in required if not path.is_file()]
    if missing:
        raise RuntimeError(f"inference did not produce required artifacts: {missing}")


def run_project(
    source: Path,
    output_root: Path,
    use_agent: bool,
    timeout: int,
    reuse_inference_root: Path | None = None,
) -> dict:
    name = source.name
    work = output_root / "work" / name
    erased = work / "erased"
    ast_output = Path(str(erased) + "_output")
    inference = work / "inference"
    migrated = output_root / "raw" / name
    for path in (work, migrated):
        if path.exists():
            raise FileExistsError(f"refusing to overwrite existing output: {path}")
    work.mkdir(parents=True)

    print(f"\n{'=' * 72}\nTS pipeline: {name}\n{'=' * 72}", flush=True)
    _run([
        "node", "--max-old-space-size=40960", "-r", "ts-node/register",
        "eraseAnnotation.ts", "-i", str(source), "-o", str(erased),
    ], timeout)
    inference_source_dir = erased
    if reuse_inference_root is not None:
        previous_work = reuse_inference_root / "work" / name
        _assert_same_erased_sources(erased, previous_work / "erased")
        _assert_compatible_inference(previous_work / "inference", use_agent)
        shutil.copytree(previous_work / "inference", inference)
        inference_source_dir = previous_work / "erased"
        print(f"  reused inference after byte-identical erased-source check: {previous_work}", flush=True)
    else:
        _run([
            "node", "--max-old-space-size=40960", "-r", "ts-node/register",
            "code2ast.ts", "-i", str(erased),
        ], timeout)
        infer_command = [
            "node", "--max-old-space-size=40960", "-r", "ts-node/register",
            "ast2type.ts", "-i", str(ast_output),
            "-o", str(inference),
            "--sourcedir", str(erased),
        ]
        if use_agent:
            infer_command.append("--agent")
        # Ground truth is intentionally not passed to ast2type.
        _run(infer_command, timeout)
        _require_inference(inference)
        _write_manifest(inference, use_agent)

    _require_inference(inference)

    report = weave_project(
        source,
        erased,
        erased / "_groundtruth.json",
        inference / "typegraph.json",
        migrated,
        inference_source_dir,
    )
    summary = {"project": name, "mode": "agent" if use_agent else "standard", **report}
    (work / "summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print("  summary:", json.dumps(summary), flush=True)
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--projects-root", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--packages", required=True, help="comma-separated project directories")
    parser.add_argument("--agent", action="store_true")
    parser.add_argument("--timeout", type=int, default=1200)
    parser.add_argument(
        "--reuse-inference-root",
        type=Path,
        help="reuse <root>/work/<project>/inference after verifying erased sources are byte-identical",
    )
    args = parser.parse_args()

    output_root = args.output_root.resolve()
    output_root.mkdir(parents=True, exist_ok=True)
    summaries = []
    for name in [part.strip() for part in args.packages.split(",") if part.strip()]:
        source = (args.projects_root / name).resolve()
        if not source.is_dir():
            raise FileNotFoundError(source)
        summaries.append(run_project(
            source,
            output_root,
            args.agent,
            args.timeout,
            args.reuse_inference_root.resolve() if args.reuse_inference_root else None,
        ))
    (output_root / "summary.json").write_text(json.dumps(summaries, indent=2), encoding="utf-8")


if __name__ == "__main__":
    main()
