#!/usr/bin/env python3
"""Conservatively widen diagnostic-related TypeScript declarations to any."""

from __future__ import annotations

import json
import os
import re
import subprocess
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Callable, Sequence

from generate.tsc_check import (
    ROOT_DIR,
    TSC_DIAGNOSTIC_RE,
    TSC_WORKING_DIRECTORY,
    TscResult,
    TscStatus,
    check_typescript,
    discover_typescript_files,
    is_typescript_source,
)


LOCATOR = ROOT_DIR / "generate" / "locate_auto_fix.js"
ERROR_RE = re.compile(
    r"^(.+?)\((\d+),(\d+)\):\s*error\s+TS(\d+):\s*(.+)$"
)


class AutoFixStatus(str, Enum):
    PASS = "PASS"
    TYPE_ERROR = "TYPE_ERROR"
    TOOL_ERROR = "TOOL_ERROR"
    EMPTY = "EMPTY"


@dataclass(frozen=True)
class TscError:
    filepath: str
    line: int
    col: int
    code: int
    message: str


@dataclass(frozen=True)
class AutoFixResult:
    status: AutoFixStatus
    initial_status: AutoFixStatus
    total_files: int
    checks: int
    fix_rounds: int
    modified_files: int
    replacements: int
    initial_diagnostics: int
    final_diagnostics: int
    skipped_diagnostics: int
    modified_paths: tuple[str, ...]
    message: str = ""

    @property
    def passed(self) -> bool:
        return self.status is AutoFixStatus.PASS


class AutoFixToolError(RuntimeError):
    pass


TypeChecker = Callable[[Sequence[str], int], TscResult]


def parse_tsc_errors(output: str) -> list[TscError]:
    errors = []
    for line in output.splitlines():
        match = ERROR_RE.match(line.strip())
        if not match:
            continue
        errors.append(TscError(
            filepath=match.group(1),
            line=int(match.group(2)),
            col=int(match.group(3)),
            code=int(match.group(4)),
            message=match.group(5),
        ))
    return errors


def _diagnostic_count(result: TscResult) -> int:
    return len(TSC_DIAGNOSTIC_RE.findall(result.output))


def _auto_status(status: TscStatus) -> AutoFixStatus:
    return AutoFixStatus(status.value)


def _resolve_diagnostic_file(
    diagnostic_path: str,
    source_files: Sequence[str],
    package_root: Path,
) -> str | None:
    known = {str(Path(source).resolve()) for source in source_files}
    raw = Path(diagnostic_path)
    candidates = []
    if raw.is_absolute():
        candidates.append(raw)
    else:
        candidates.extend((TSC_WORKING_DIRECTORY / raw, package_root / raw))
    for candidate in candidates:
        resolved = str(candidate.resolve())
        if resolved in known:
            return resolved

    normalized_parts = Path(os.path.normpath(diagnostic_path)).parts
    suffix_matches = [
        source
        for source in known
        if len(normalized_parts) > 1
        and Path(source).parts[-len(normalized_parts):] == normalized_parts
    ]
    if len(suffix_matches) == 1:
        return suffix_matches[0]
    if len(normalized_parts) == 1:
        basename_matches = [
            source for source in known if Path(source).name == normalized_parts[0]
        ]
        if len(basename_matches) == 1:
            return basename_matches[0]
    return None


def _locate_type_edits(
    source_files: Sequence[str],
    errors: Sequence[TscError],
    package_root: Path,
    timeout: int = 120,
) -> dict:
    diagnostics = []
    unresolved = []
    for error in errors:
        resolved = _resolve_diagnostic_file(
            error.filepath,
            source_files,
            package_root,
        )
        if resolved is None:
            unresolved.append({
                "file": error.filepath,
                "line": error.line,
                "col": error.col,
                "code": error.code,
                "message": error.message,
                "reason": "diagnostic file is not an editable source",
            })
            continue
        diagnostics.append({
            "file": resolved,
            "line": error.line,
            "col": error.col,
            "code": error.code,
            "message": error.message,
        })
    payload = {
        "files": list(source_files),
        "diagnostics": diagnostics,
    }
    try:
        completed = subprocess.run(
            ["node", str(LOCATOR)],
            cwd=ROOT_DIR,
            input=json.dumps(payload, ensure_ascii=False),
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise AutoFixToolError(f"type locator failed: {error}") from error
    if completed.returncode != 0:
        raise AutoFixToolError(
            f"type locator exited {completed.returncode}: {completed.stderr.strip()}"
        )
    try:
        result = json.loads(completed.stdout)
    except json.JSONDecodeError as error:
        raise AutoFixToolError("type locator returned invalid JSON") from error
    if not isinstance(result.get("edits"), list) or not isinstance(result.get("skipped"), list):
        raise AutoFixToolError("type locator returned an invalid result")
    result["skipped"] = unresolved + result["skipped"]
    return result


def _read_source(path: Path) -> str:
    with path.open("r", encoding="utf-8", newline="") as source:
        return source.read()


def _write_source(path: Path, content: str) -> None:
    with path.open("w", encoding="utf-8", newline="") as target:
        target.write(content)


def _utf16_boundaries(content: str) -> dict[int, int]:
    boundaries = {0: 0}
    offset = 0
    for index, character in enumerate(content, start=1):
        offset += 2 if ord(character) > 0xFFFF else 1
        boundaries[offset] = index
    return boundaries


def _apply_type_edits(
    source_files: Sequence[str],
    edits: Sequence[dict],
) -> tuple[set[str], int]:
    editable = {str(Path(source).resolve()) for source in source_files}
    by_file: dict[str, list[dict]] = {}
    for edit in edits:
        filepath = str(Path(edit.get("file", "")).resolve())
        start = edit.get("start")
        end = edit.get("end")
        replacement = edit.get("replacement")
        if (filepath not in editable
                or not isinstance(start, int)
                or not isinstance(end, int)
                or not isinstance(replacement, str)
                or any(newline in replacement for newline in "\r\n")
                or not 0 <= start <= end):
            raise AutoFixToolError(f"invalid type edit: {edit}")
        by_file.setdefault(filepath, []).append(edit)

    modified = set()
    applied = 0
    for filepath, file_edits in by_file.items():
        path = Path(filepath)
        content = _read_source(path)
        boundaries = _utf16_boundaries(content)
        replacements = []
        for edit in sorted(file_edits, key=lambda item: (item["start"], item["end"])):
            start = boundaries.get(edit["start"])
            end = boundaries.get(edit["end"])
            if start is None or end is None:
                raise AutoFixToolError(f"edit splits a UTF-16 character: {edit}")
            if replacements and start < replacements[-1][1]:
                raise AutoFixToolError(f"overlapping type edits: {edit}")
            replacements.append((start, end, edit["replacement"]))

        updated = content
        for start, end, replacement in reversed(replacements):
            updated = updated[:start] + replacement + updated[end:]
        if updated != content:
            _write_source(path, updated)
            modified.add(filepath)
            applied += len(replacements)
    return modified, applied


def _result(
    *,
    status: AutoFixStatus,
    initial_status: AutoFixStatus,
    source_files: Sequence[str],
    checks: int,
    fix_rounds: int,
    modified_paths: set[str],
    replacements: int,
    initial_diagnostics: int,
    final_diagnostics: int,
    skipped_diagnostics: int,
    message: str = "",
) -> AutoFixResult:
    return AutoFixResult(
        status=status,
        initial_status=initial_status,
        total_files=len(source_files),
        checks=checks,
        fix_rounds=fix_rounds,
        modified_files=len(modified_paths),
        replacements=replacements,
        initial_diagnostics=initial_diagnostics,
        final_diagnostics=final_diagnostics,
        skipped_diagnostics=skipped_diagnostics,
        modified_paths=tuple(sorted(modified_paths)),
        message=message,
    )


def _auto_fix_sources(
    source_files: Sequence[str],
    package_root: Path,
    max_rounds: int,
    timeout: int,
    type_checker: TypeChecker | None = None,
) -> AutoFixResult:
    files = sorted({
        str(Path(source).resolve())
        for source in source_files
        if is_typescript_source(source)
    })
    if not files:
        return _result(
            status=AutoFixStatus.EMPTY,
            initial_status=AutoFixStatus.EMPTY,
            source_files=files,
            checks=0,
            fix_rounds=0,
            modified_paths=set(),
            replacements=0,
            initial_diagnostics=0,
            final_diagnostics=0,
            skipped_diagnostics=0,
        )

    def run_check() -> TscResult:
        if type_checker is not None:
            return type_checker(files, timeout)
        return check_typescript(files, timeout=timeout)

    current = run_check()
    checks = 1
    initial_status = _auto_status(current.status)
    initial_diagnostics = _diagnostic_count(current)
    modified_paths: set[str] = set()
    replacements = 0
    skipped = 0
    fix_rounds = 0

    if current.status is TscStatus.PASS:
        return _result(
            status=AutoFixStatus.PASS,
            initial_status=initial_status,
            source_files=files,
            checks=checks,
            fix_rounds=fix_rounds,
            modified_paths=modified_paths,
            replacements=replacements,
            initial_diagnostics=initial_diagnostics,
            final_diagnostics=0,
            skipped_diagnostics=skipped,
        )
    if current.status is TscStatus.TOOL_ERROR:
        return _result(
            status=AutoFixStatus.TOOL_ERROR,
            initial_status=initial_status,
            source_files=files,
            checks=checks,
            fix_rounds=fix_rounds,
            modified_paths=modified_paths,
            replacements=replacements,
            initial_diagnostics=initial_diagnostics,
            final_diagnostics=initial_diagnostics,
            skipped_diagnostics=skipped,
            message=current.output,
        )

    try:
        for _ in range(max(0, max_rounds)):
            errors = parse_tsc_errors(current.output)
            located = _locate_type_edits(files, errors, package_root, timeout=timeout)
            skipped += len(located["skipped"])
            if not located["edits"]:
                break
            round_files, round_replacements = _apply_type_edits(
                files,
                located["edits"],
            )
            if not round_files or round_replacements == 0:
                break
            modified_paths.update(round_files)
            replacements += round_replacements
            fix_rounds += 1

            current = run_check()
            checks += 1
            if current.status is not TscStatus.TYPE_ERROR:
                break
    except AutoFixToolError as error:
        return _result(
            status=AutoFixStatus.TOOL_ERROR,
            initial_status=initial_status,
            source_files=files,
            checks=checks,
            fix_rounds=fix_rounds,
            modified_paths=modified_paths,
            replacements=replacements,
            initial_diagnostics=initial_diagnostics,
            final_diagnostics=_diagnostic_count(current),
            skipped_diagnostics=skipped,
            message=str(error),
        )

    return _result(
        status=_auto_status(current.status),
        initial_status=initial_status,
        source_files=files,
        checks=checks,
        fix_rounds=fix_rounds,
        modified_paths=modified_paths,
        replacements=replacements,
        initial_diagnostics=initial_diagnostics,
        final_diagnostics=_diagnostic_count(current),
        skipped_diagnostics=skipped,
        message=current.output if current.status is TscStatus.TOOL_ERROR else "",
    )


def auto_fix_file(
    ts_path: str | os.PathLike[str],
    max_rounds: int = 5,
    timeout: int = 120,
    type_checker: TypeChecker | None = None,
) -> AutoFixResult:
    path = Path(ts_path).resolve()
    files = [str(path)] if path.is_file() and is_typescript_source(path) else []
    return _auto_fix_sources(
        files, path.parent, max_rounds, timeout, type_checker
    )


def auto_fix_package(
    package_dir: str | os.PathLike[str],
    max_rounds: int = 5,
    timeout: int = 120,
    type_checker: TypeChecker | None = None,
) -> AutoFixResult:
    root = Path(package_dir).resolve()
    files = discover_typescript_files(root)
    return _auto_fix_sources(files, root, max_rounds, timeout, type_checker)
