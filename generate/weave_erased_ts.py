#!/usr/bin/env python3
"""Restore inferred annotations into an erased TypeScript project."""

from __future__ import annotations

import argparse
import json
import os
import shutil
from collections import defaultdict
from pathlib import Path

from generate.pipeline_ts import _full_type_to_ts
from generate.weave import _sanitize_ts_type, _split_function_arrow


TS_EXTENSIONS = {".ts", ".tsx", ".mts", ".cts", ".ets"}


def _normal_path(value: str) -> str:
    return os.path.normpath(value.replace("^", os.sep).replace("/", os.sep))


def _load_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def _read_source(path: Path) -> str:
    # TypeScript offsets count CRLF as two characters. Path.read_text() uses
    # universal newline translation, which would invalidate every later span.
    with path.open("r", encoding="utf-8", newline="") as source:
        return source.read()


def _write_source(path: Path, content: str) -> None:
    with path.open("w", encoding="utf-8", newline="") as target:
        target.write(content)


def _index_typeinfo(typeinfo: list[dict]) -> dict[tuple, list[dict]]:
    indexed: dict[tuple, list[dict]] = defaultdict(list)
    for item in typeinfo:
        relpath = item.get("relapath")
        location = item.get("location")
        if not isinstance(relpath, str) or not isinstance(location, int):
            continue
        indexed[("offset", _normal_path(relpath), location)].append(item)
    return indexed


def _graph_relpath(file_value: object, erased_dir: Path) -> str | None:
    if not isinstance(file_value, str):
        return None
    try:
        source = Path(_normal_path(file_value)).resolve()
        return _normal_path(str(source.relative_to(erased_dir.resolve())))
    except (OSError, ValueError):
        return None


def _index_typegraph(typegraph: dict, erased_dir: Path) -> dict[tuple, list[dict]]:
    indexed: dict[tuple, list[dict]] = defaultdict(list)
    for node in typegraph.get("nodes", []):
        if not isinstance(node, dict) or node.get("fullType") is None:
            continue
        relpath = _graph_relpath(node.get("file"), erased_dir)
        start = (node.get("position") or {}).get("start") or {}
        line = start.get("line")
        col = start.get("character")
        if relpath is None or not isinstance(line, int) or not isinstance(col, int):
            continue
        full_type = node.get("fullType")
        if isinstance(full_type, str):
            try:
                full_type = json.loads(full_type)
            except json.JSONDecodeError:
                pass
        indexed[("position", relpath, line, col)].append({
            "exprText": node.get("text", node.get("label", "")),
            "fullType": full_type,
        })
    return indexed


def _load_inferred(path: Path, erased_dir: Path) -> dict[tuple, list[dict]]:
    payload = _load_json(path)
    if isinstance(payload, list):
        return _index_typeinfo(payload)
    if isinstance(payload, dict):
        return _index_typegraph(payload, erased_dir)
    raise ValueError(f"unsupported inference artifact: {path}")


def _render_full_type(full_type: object) -> str:
    # The graph stores source-token literals (for example "'text'"). Widen
    # them to their primitive type so reconstructed annotations remain useful.
    if isinstance(full_type, dict) and full_type.get("kind") == "literal":
        value = full_type.get("value")
        if isinstance(value, bool) or (isinstance(value, str) and value in {"true", "false"}):
            return "boolean"
        if isinstance(value, (int, float)):
            return "number"
        if isinstance(value, str):
            stripped = value.strip()
            if (len(stripped) >= 2 and stripped[0] == stripped[-1]
                    and stripped[0] in {"'", '"', "`"}):
                return "string"
            if stripped.endswith("n") and stripped[:-1].isdigit():
                return "bigint"
            try:
                float(stripped)
                return "number"
            except ValueError:
                return "string"
        return "any"
    return _sanitize_ts_type(_full_type_to_ts(full_type))


def _is_unknown_full_type(full_type: object) -> bool:
    return full_type == "unknown" or (
        isinstance(full_type, dict)
        and (
            full_type.get("kind") == "unknown"
            or (
                full_type.get("kind") == "primitive"
                and full_type.get("name") == "unknown"
            )
        )
    )


def _candidate_type(item: dict, kind: object) -> str | None:
    if "fullType" in item:
        full_type = item["fullType"]
        if kind == "return":
            if isinstance(full_type, dict) and full_type.get("kind") == "function":
                full_type = full_type.get("returnType")
            elif isinstance(full_type, str):
                split = _split_function_arrow(full_type)
                if split:
                    return _sanitize_ts_type(split[1])
                return None
            else:
                return None
        if _is_unknown_full_type(full_type):
            return None
        return _render_full_type(full_type)

    raw_type = str(item.get("type", "")).strip()
    if kind == "return":
        split = _split_function_arrow(raw_type)
        return _sanitize_ts_type(split[1]) if split else None
    constant = raw_type.removesuffix(" constant")
    if constant in {"string", "number", "boolean", "bigint", "symbol", "object"}:
        return constant
    return _sanitize_ts_type(raw_type) if raw_type else None


def _annotation_type(annotation: dict, candidates: list[dict]) -> tuple[str | None, bool]:
    identifier = annotation.get("identifier", "")
    kind = annotation.get("kind")
    if annotation.get("inferable", True):
        exact = [item for item in candidates if item.get("exprText") == identifier]
        pool = exact if annotation.get("matchText", True) else (exact or candidates)
    else:
        pool = []

    if kind == "index":
        for item in pool:
            inferred = _candidate_type(item, kind)
            if inferred in {"string", "number", "symbol"}:
                return inferred, True
        return "string", False

    if kind == "index-value":
        for item in pool:
            inferred = _candidate_type(item, kind)
            if inferred:
                return inferred, True
        return "any", False

    if kind == "property" and not pool:
        return "any", False

    for item in pool:
        inferred = _candidate_type(item, kind)
        if inferred:
            if kind == "return" and inferred == "PromiseConstructor":
                inferred = "Promise<any>"
            elif (kind == "return" and annotation.get("isAsync")
                  and not (inferred == "Promise" or inferred.startswith("Promise<"))):
                inferred = f"Promise<{inferred}>"
            return inferred, True
    return None, False


def _utf16_boundaries(content: str) -> dict[int, int]:
    """Map TypeScript UTF-16 offsets to Python string indices."""
    boundaries = {0: 0}
    units = 0
    for index, character in enumerate(content, start=1):
        units += 2 if ord(character) > 0xFFFF else 1
        boundaries[units] = index
    return boundaries


def _safe_target(output_dir: Path, relpath: str) -> Path | None:
    normalized = Path(_normal_path(relpath))
    if normalized.is_absolute() or ".." in normalized.parts:
        return None
    root = output_dir.resolve()
    target = (root / normalized).resolve()
    try:
        target.relative_to(root)
    except ValueError:
        return None
    return target


def _copy_project(base_project: Path, erased_dir: Path, output_dir: Path) -> None:
    if output_dir.exists():
        raise FileExistsError(f"output directory already exists: {output_dir}")
    shutil.copytree(
        base_project,
        output_dir,
        ignore=shutil.ignore_patterns("node_modules", ".git"),
    )
    for source in erased_dir.rglob("*"):
        if not source.is_file() or source.suffix not in TS_EXTENSIONS:
            continue
        target = output_dir / source.relative_to(erased_dir)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)


def weave_project(
    base_project: Path,
    erased_dir: Path,
    groundtruth_path: Path,
    inference_path: Path,
    output_dir: Path,
    inference_source_dir: Path | None = None,
) -> dict:
    _copy_project(base_project, erased_dir, output_dir)
    groundtruth = _load_json(groundtruth_path)
    inferred = _load_inferred(inference_path, inference_source_dir or erased_dir)
    report = {
        "annotations": 0,
        "inferred": 0,
        "unannotated": 0,
        "syntax_fallback": 0,
        "files": 0,
        "invalid_spans": [],
    }

    for relpath, annotations in groundtruth.items():
        normalized = _normal_path(relpath)
        target = _safe_target(output_dir, relpath)
        if target is None:
            report["invalid_spans"].append({"file": relpath, "reason": "path escapes output directory"})
            continue
        if not target.is_file():
            report["invalid_spans"].append({"file": relpath, "reason": "missing file"})
            continue
        content = _read_source(target)
        utf16_boundaries = _utf16_boundaries(content)
        replacements = []
        for annotation in annotations:
            report["annotations"] += 1
            start_offset = annotation.get("annotationStart")
            end_offset = annotation.get("annotationEnd")
            start = utf16_boundaries.get(start_offset) if isinstance(start_offset, int) else None
            end = utf16_boundaries.get(end_offset) if isinstance(end_offset, int) else None
            if start is None or end is None or not (0 <= start < end <= len(content)):
                report["invalid_spans"].append({"file": relpath, "identifier": annotation.get("identifier"), "reason": "invalid range"})
                continue
            if content[start:end].strip():
                report["invalid_spans"].append({"file": relpath, "identifier": annotation.get("identifier"), "reason": "range is not erased"})
                continue
            candidates = list(inferred.get((
                "position",
                normalized,
                annotation.get("line"),
                annotation.get("col"),
            ), []))
            candidates.extend(inferred.get((
                "offset",
                normalized,
                int(annotation.get("offset", -1)),
            ), []))
            inferred_type, matched = _annotation_type(annotation, candidates)
            if inferred_type is None:
                report["unannotated"] += 1
                replacements.append((start, end, " "))
                continue
            report["inferred" if matched else "syntax_fallback"] += 1
            replacements.append((start, end, f": {inferred_type}"))

        for start, end, replacement in sorted(replacements, reverse=True):
            content = content[:start] + replacement + content[end:]
        _write_source(target, content)
        report["files"] += 1

    (output_dir / "ast2type-weave-report.json").write_text(
        json.dumps(report, indent=2),
        encoding="utf-8",
    )
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base-project", type=Path, required=True)
    parser.add_argument("--erased-dir", type=Path, required=True)
    parser.add_argument("--groundtruth", type=Path, required=True)
    parser.add_argument(
        "--inference",
        "--typeinfo",
        dest="inference",
        type=Path,
        required=True,
        help="typegraph.json (preferred) or legacy typeinfo.json",
    )
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument(
        "--inference-source-dir",
        type=Path,
        help="source root recorded in a reused typegraph (default: erased-dir)",
    )
    args = parser.parse_args()

    report = weave_project(
        args.base_project.resolve(),
        args.erased_dir.resolve(),
        args.groundtruth.resolve(),
        args.inference.resolve(),
        args.output_dir.resolve(),
        args.inference_source_dir.resolve() if args.inference_source_dir else None,
    )
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
