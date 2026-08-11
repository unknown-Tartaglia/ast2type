#!/usr/bin/env python3
"""Weave canonical typegraph function types into JavaScript using AST locations."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
LOCATOR = ROOT / "generate" / "weave_typegraph_ast.js"
REPORT_NAME = "ast2type-weave-report.json"
MANIFEST_NAME = "ast2type-weave-manifest.json"
# Keep this identical to code2ast's JS-only input contract. In particular,
# converting both index.js and index.cjs to index.ts would overwrite one file.
SOURCE_EXTENSIONS = {".js", ".mjs"}
IGNORED_DIRECTORIES = {"node_modules", ".git"}


class TypegraphWeaveError(RuntimeError):
    """Raised when the AST locator or materialization contract is violated."""


def _read_source(path: Path) -> str:
    with path.open("r", encoding="utf-8", newline="") as source:
        return source.read()


def _write_source(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as target:
        target.write(content)


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _parse_full_type(value: object) -> dict | None:
    if isinstance(value, dict):
        return value
    if not isinstance(value, str):
        return None
    try:
        parsed = json.loads(value)
    except json.JSONDecodeError:
        return None
    return parsed if isinstance(parsed, dict) else None


def canonical_function_targets(
    typegraph: dict,
    render_type=None,
) -> tuple[list[dict], dict]:
    """Keep declaration identity instead of collapsing functions by name."""
    if render_type is None:
        # Delay this import so pipeline_ts can import the integration API without
        # creating a module initialization cycle.
        from generate.pipeline_ts import _full_type_to_ts

        render_type = _full_type_to_ts
    targets = []
    stats = {
        "typegraph_nodes": 0,
        "function_nodes": 0,
        "canonical_targets": 0,
        "ignored_noncanonical": 0,
        "ignored_duplicate_canonical": 0,
        "ignored_malformed": 0,
    }
    nodes = typegraph.get("nodes", []) if isinstance(typegraph, dict) else []
    if not isinstance(nodes, list):
        raise TypegraphWeaveError("typegraph.nodes must be an array")
    stats["typegraph_nodes"] = len(nodes)

    canonical_keys = set()
    for node in nodes:
        if not isinstance(node, dict):
            stats["ignored_malformed"] += 1
            continue
        full_type = _parse_full_type(node.get("fullType"))
        if not full_type or full_type.get("kind") != "function":
            continue
        stats["function_nodes"] += 1
        node_id = node.get("id")
        full_type_id = full_type.get("id")
        if not isinstance(node_id, int) or not isinstance(full_type_id, int):
            stats["ignored_malformed"] += 1
            continue
        if node_id != full_type_id:
            stats["ignored_noncanonical"] += 1
            continue
        canonical_key = (str(node.get("file", "")), node_id)
        if canonical_key in canonical_keys:
            stats["ignored_duplicate_canonical"] += 1
            continue
        canonical_keys.add(canonical_key)

        parameters = full_type.get("params", [])
        if not isinstance(parameters, list):
            parameters = []
        targets.append({
            "id": node_id,
            "file": node.get("file"),
            "position": node.get("position"),
            "name": full_type.get("name", ""),
            "parameter_types": [
                render_type(parameter.get("type"))
                if isinstance(parameter, dict) else "any"
                for parameter in parameters
            ],
            "return_type": render_type(full_type.get("returnType")),
        })

    targets.sort(key=lambda item: (str(item.get("file", "")), item["id"]))
    stats["canonical_targets"] = len(targets)
    return targets, stats


def _run_locator(
    source_root: Path,
    targets: list[dict],
    *,
    node_bin: str = "node",
    locator: Path = LOCATOR,
    timeout: int = 120,
) -> dict:
    payload = {"source_root": str(source_root), "targets": targets}
    try:
        completed = subprocess.run(
            [node_bin, str(locator)],
            cwd=ROOT,
            input=json.dumps(payload, ensure_ascii=False),
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise TypegraphWeaveError(f"AST locator failed: {error}") from error
    if completed.returncode != 0:
        raise TypegraphWeaveError(
            f"AST locator exited {completed.returncode}: {completed.stderr.strip()}"
        )
    try:
        result = json.loads(completed.stdout)
    except json.JSONDecodeError as error:
        raise TypegraphWeaveError("AST locator returned invalid JSON") from error
    if not isinstance(result, dict) or not isinstance(result.get("edits"), list):
        raise TypegraphWeaveError("AST locator returned an invalid result")
    return result


def _utf16_boundaries(content: str) -> dict[int, int]:
    boundaries = {0: 0}
    units = 0
    for index, character in enumerate(content, start=1):
        units += 2 if ord(character) > 0xFFFF else 1
        boundaries[units] = index
    return boundaries


def _apply_edits(content: str, edits: Iterable[dict], relative_file: str) -> str:
    boundaries = _utf16_boundaries(content)
    replacements = []
    for edit in sorted(edits, key=lambda item: (item.get("start", -1), item.get("end", -1))):
        start_offset = edit.get("start")
        end_offset = edit.get("end")
        replacement = edit.get("replacement")
        if (not isinstance(start_offset, int) or not isinstance(end_offset, int)
                or not isinstance(replacement, str)
                or "\n" in replacement or "\r" in replacement):
            raise TypegraphWeaveError(f"invalid AST edit for {relative_file}: {edit}")
        start = boundaries.get(start_offset)
        end = boundaries.get(end_offset)
        if start is None or end is None or start > end:
            raise TypegraphWeaveError(
                f"AST edit splits a UTF-16 character in {relative_file}: {edit}"
            )
        if replacements and start < replacements[-1][1]:
            raise TypegraphWeaveError(f"overlapping AST edits in {relative_file}: {edit}")
        replacements.append((start, end, replacement))

    updated = content
    for start, end, replacement in reversed(replacements):
        updated = updated[:start] + replacement + updated[end:]
    return updated


def _output_relative(relative: Path) -> Path:
    suffix = relative.suffix.lower()
    if suffix in SOURCE_EXTENSIONS:
        return relative.with_suffix(".ts")
    return relative


def _source_files(source_root: Path) -> list[Path]:
    files = []
    for root, directories, names in os.walk(source_root):
        directories[:] = sorted(
            name for name in directories if name not in IGNORED_DIRECTORIES
        )
        for name in sorted(names):
            files.append(Path(root) / name)
    return files


def weave_typegraph_package(
    pkg_dir: Path,
    typegraph: dict,
    *,
    render_type=None,
    node_bin: str = "node",
    locator: Path = LOCATOR,
    timeout: int = 120,
) -> tuple[dict[str, str], dict]:
    """Return AST-woven JavaScript text keyed by its original relative path.

    This is the pipeline integration surface. It performs no filesystem writes;
    callers decide whether ``.js``/``.mjs`` keys become ``.ts`` paths.
    """
    source_root = Path(pkg_dir).resolve()
    if not source_root.is_dir():
        raise FileNotFoundError(source_root)
    targets, extraction = canonical_function_targets(typegraph, render_type=render_type)
    located = _run_locator(
        source_root,
        targets,
        node_bin=node_bin,
        locator=locator,
        timeout=timeout,
    )

    edits_by_file: dict[str, list[dict]] = {}
    for edit in located["edits"]:
        relative = edit.get("file")
        relative_path = Path(relative) if isinstance(relative, str) else None
        if (relative_path is None or relative_path.is_absolute()
                or ".." in relative_path.parts):
            raise TypegraphWeaveError(f"AST locator returned an unsafe path: {edit}")
        normalized = os.path.normpath(str(relative_path))
        edits_by_file.setdefault(normalized, []).append(edit)

    woven = {}
    modified_paths = []
    java_script_files = [
        path for path in _source_files(source_root)
        if path.suffix.lower() in SOURCE_EXTENSIONS
    ]
    for source in java_script_files:
        relative = os.path.normpath(str(source.relative_to(source_root)))
        content = _read_source(source)
        updated = _apply_edits(content, edits_by_file.get(relative, []), relative)
        woven[relative] = updated
        if updated != content:
            modified_paths.append(Path(relative).as_posix())

    unused_edit_files = sorted(set(edits_by_file) - set(woven))
    if unused_edit_files:
        raise TypegraphWeaveError(
            f"AST edits reference unsupported or missing source files: {unused_edit_files}"
        )

    report = {
        "schema_version": 1,
        **extraction,
        "located_targets": located.get("located_targets", 0),
        "woven_targets": located.get("woven_targets", 0),
        "edits": len(located["edits"]),
        "skipped_targets": len(located.get("skipped", [])),
        "skipped": located.get("skipped", []),
        "target_reports": located.get("target_reports", []),
        "source_files": len(java_script_files),
        "output_files": len(woven),
        "modified_files": len(modified_paths),
        "modified_paths": modified_paths,
    }
    return woven, report


def weave_project(
    source_root: Path,
    typegraph_path: Path,
    output_root: Path,
    *,
    node_bin: str = "node",
    locator: Path = LOCATOR,
    timeout: int = 120,
) -> dict:
    """Materialize an AST-positioned JS-to-TS project and audit artifacts."""
    source_root = source_root.resolve()
    typegraph_path = typegraph_path.resolve()
    output_root = output_root.resolve()
    if not source_root.is_dir():
        raise FileNotFoundError(source_root)
    if not typegraph_path.is_file():
        raise FileNotFoundError(typegraph_path)
    if output_root.exists():
        raise FileExistsError(f"output directory already exists: {output_root}")

    typegraph = json.loads(typegraph_path.read_text(encoding="utf-8"))
    woven, report = weave_typegraph_package(
        source_root,
        typegraph,
        node_bin=node_bin,
        locator=locator,
        timeout=timeout,
    )

    source_files = _source_files(source_root)
    outputs: dict[Path, Path] = {}
    for source in source_files:
        relative = source.relative_to(source_root)
        destination_relative = _output_relative(relative)
        if destination_relative in outputs:
            raise TypegraphWeaveError(
                f"multiple sources map to {destination_relative}: "
                f"{outputs[destination_relative]} and {source}"
            )
        outputs[destination_relative] = source

    temporary = output_root.parent / f".{output_root.name}.tmp-{os.getpid()}"
    if temporary.exists():
        raise FileExistsError(f"temporary output already exists: {temporary}")
    temporary.mkdir(parents=True)
    modified_files = []
    try:
        for destination_relative, source in sorted(
            outputs.items(), key=lambda item: item[0].as_posix()
        ):
            target = temporary / destination_relative
            target.parent.mkdir(parents=True, exist_ok=True)
            relative = os.path.normpath(str(source.relative_to(source_root)))
            if source.suffix.lower() in SOURCE_EXTENSIONS:
                _write_source(target, woven[relative])
                if Path(relative).as_posix() in report["modified_paths"]:
                    modified_files.append(destination_relative.as_posix())
            else:
                shutil.copy2(source, target)

        report = dict(report)
        report["project_files"] = len(source_files)
        report["materialized_files"] = len(outputs)
        report["materialized_modified_paths"] = modified_files
        manifest = {
            "schema_version": 1,
            "tool": "ast2type-typegraph-ast-weaver",
            "generated_at": datetime.now(timezone.utc).isoformat(),
            "source_root": str(source_root),
            "typegraph": {
                "path": str(typegraph_path),
                "sha256": _sha256(typegraph_path),
            },
            "output_root": str(output_root),
            "implementation": {
                "python": _sha256(Path(__file__).resolve()),
                "locator": _sha256(locator.resolve()),
            },
            "report": REPORT_NAME,
            "counts": {
                key: report[key]
                for key in (
                    "typegraph_nodes", "function_nodes", "canonical_targets",
                    "ignored_noncanonical", "ignored_duplicate_canonical",
                    "ignored_malformed",
                    "located_targets", "woven_targets", "edits", "skipped_targets",
                    "source_files", "output_files", "modified_files",
                )
            },
        }
        (temporary / REPORT_NAME).write_text(
            json.dumps(report, indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )
        (temporary / MANIFEST_NAME).write_text(
            json.dumps(manifest, indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )
        temporary.rename(output_root)
        return report
    except Exception:
        shutil.rmtree(temporary, ignore_errors=True)
        raise


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--typegraph", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--node-bin", default="node")
    parser.add_argument("--timeout", type=int, default=120)
    args = parser.parse_args()
    report = weave_project(
        args.source_root,
        args.typegraph,
        args.output_root,
        node_bin=args.node_bin,
        timeout=args.timeout,
    )
    print(json.dumps(report, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
