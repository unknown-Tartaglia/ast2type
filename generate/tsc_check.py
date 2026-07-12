#!/usr/bin/env python3
"""Shared TypeScript compilation contract for auto-fix and evaluation."""

from __future__ import annotations

import argparse
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Sequence


ROOT_DIR = Path(__file__).resolve().parent.parent
TSC_WORKING_DIRECTORY = ROOT_DIR
DEFAULT_TSC = ROOT_DIR / "node_modules" / ".bin" / "tsc"

TS_SOURCE_EXTENSIONS = (".ts", ".tsx", ".mts", ".cts")
TS_DECLARATION_EXTENSIONS = (".d.ts", ".d.mts", ".d.cts")
IGNORED_DIRECTORIES = {"node_modules", ".git"}

COMMON_FLAGS = (
    "--pretty",
    "false",
    "--esModuleInterop",
    "--moduleResolution",
    "bundler",
    "--module",
    "es2015",
    "--target",
    "es6",
    "--lib",
    "es2021,dom",
    "--jsx",
    "preserve",
    "--skipLibCheck",
)

DECLARATION_FLAGS = (
    "--declaration",
    "--emitDeclarationOnly",
    "--noEmitOnError",
)

TOOL_ERROR_LINE_PREFIXES = (
    "Error: Debug Failure",
    "Debug Failure.",
    "FATAL ERROR",
    "JavaScript heap out of memory",
    "Segmentation fault",
    "RangeError: Maximum call stack size exceeded",
    "Internal error: ",
    "TSC_NOT_FOUND",
    "TSC_TIMEOUT",
)

TSC_DIAGNOSTIC_RE = re.compile(r"\berror TS\d+:")


class TscStatus(str, Enum):
    PASS = "PASS"
    TYPE_ERROR = "TYPE_ERROR"
    TOOL_ERROR = "TOOL_ERROR"


@dataclass(frozen=True)
class TscResult:
    status: TscStatus
    returncode: int
    output: str
    command: tuple[str, ...]


def compiler_path() -> Path:
    override = os.environ.get("AST2TYPE_TSC_BIN")
    if override:
        return Path(override).expanduser().resolve()
    return DEFAULT_TSC.resolve()


def compiler_version() -> str:
    compiler = compiler_path()
    try:
        completed = subprocess.run(
            [str(compiler), "--version"],
            cwd=TSC_WORKING_DIRECTORY,
            capture_output=True,
            text=True,
            timeout=30,
        )
    except (OSError, subprocess.SubprocessError):
        return "unavailable"
    if completed.returncode != 0:
        return "unavailable"
    output = (completed.stdout + completed.stderr).strip()
    return output.splitlines()[0] if output else "unavailable"


def _classify(returncode: int, output: str) -> TscStatus:
    if any(
        line.strip().startswith(TOOL_ERROR_LINE_PREFIXES)
        for line in output.splitlines()
    ):
        return TscStatus.TOOL_ERROR
    if returncode == 0:
        return (
            TscStatus.TOOL_ERROR
            if TSC_DIAGNOSTIC_RE.search(output)
            else TscStatus.PASS
        )
    if returncode < 0 or returncode > 2:
        return TscStatus.TOOL_ERROR
    if TSC_DIAGNOSTIC_RE.search(output):
        return TscStatus.TYPE_ERROR
    return TscStatus.TOOL_ERROR


def is_typescript_source(path: str | os.PathLike[str]) -> bool:
    name = Path(path).name
    return (
        name.endswith(TS_SOURCE_EXTENSIONS)
        and not name.endswith(TS_DECLARATION_EXTENSIONS)
    )


def discover_typescript_files(root: str | os.PathLike[str]) -> list[str]:
    """Return deterministic TS-family root files below ``root``."""
    root_path = Path(root)
    if root_path.is_file():
        return [str(root_path.resolve())] if is_typescript_source(root_path) else []
    if not root_path.is_dir():
        return []

    discovered = []
    for current, directories, filenames in os.walk(root_path):
        directories[:] = sorted(
            name for name in directories if name not in IGNORED_DIRECTORIES
        )
        for filename in sorted(filenames):
            source = Path(current) / filename
            if is_typescript_source(source):
                discovered.append(str(source.resolve()))
    return sorted(set(discovered))


def _normalize_source_files(
    ts_files: Sequence[str | os.PathLike[str]],
) -> list[str]:
    return sorted({
        str(Path(path).resolve())
        for path in ts_files
        if is_typescript_source(path)
    })


def _prepare_declaration_dir(
    declaration_dir: Path,
    source_files: Sequence[str] = (),
) -> None:
    # The directory is the output of one contract invocation. Replacing it
    # prevents a failed check from exposing declarations emitted by an older run.
    resolved = declaration_dir.resolve()
    if any(resolved == Path(source).resolve() or resolved in Path(source).resolve().parents
           for source in source_files):
        raise OSError("declaration directory contains a root source file")
    if declaration_dir.exists():
        if not declaration_dir.is_dir() or declaration_dir.is_symlink():
            raise NotADirectoryError(declaration_dir)
        unexpected = [
            path
            for path in declaration_dir.rglob("*")
            if path.is_symlink()
            or (path.is_file() and not path.name.endswith(TS_DECLARATION_EXTENSIONS))
        ]
        if unexpected:
            raise OSError(
                f"declaration directory contains non-output files: {unexpected[:3]}"
            )
        shutil.rmtree(declaration_dir)
    declaration_dir.mkdir(parents=True)


def _clear_failed_declarations(
    declaration_dir: Path,
    files: Sequence[str],
    status: TscStatus,
    returncode: int,
    output: str,
    command: tuple[str, ...],
) -> TscResult:
    try:
        _prepare_declaration_dir(declaration_dir, files)
    except OSError as error:
        output += f"\nTSC_OUTPUT_ERROR: {declaration_dir}: {error}\n"
        status = TscStatus.TOOL_ERROR
    return TscResult(status, returncode, output, command)


def _run_check(
    ts_files: Sequence[str | os.PathLike[str]],
    declaration_dir: Path,
    timeout: int,
) -> TscResult:
    files = _normalize_source_files(ts_files)
    compiler = compiler_path()
    command = (
        str(compiler),
        *COMMON_FLAGS,
        *DECLARATION_FLAGS,
        "--declarationDir",
        str(declaration_dir.resolve()),
        *files,
    )
    try:
        _prepare_declaration_dir(declaration_dir, files)
    except OSError as error:
        output = f"TSC_OUTPUT_ERROR: {declaration_dir}: {error}\n"
        return TscResult(TscStatus.TOOL_ERROR, -1, output, command)
    if not files:
        return TscResult(TscStatus.PASS, 0, "", command)

    try:
        completed = subprocess.run(
            command,
            cwd=TSC_WORKING_DIRECTORY,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        output = completed.stdout + completed.stderr
        status = _classify(completed.returncode, output)
        if status is TscStatus.PASS:
            return TscResult(status, completed.returncode, output, command)
        return _clear_failed_declarations(
            declaration_dir,
            files,
            status,
            completed.returncode,
            output,
            command,
        )
    except subprocess.TimeoutExpired as error:
        stdout = error.stdout.decode() if isinstance(error.stdout, bytes) else (error.stdout or "")
        stderr = error.stderr.decode() if isinstance(error.stderr, bytes) else (error.stderr or "")
        output = f"{stdout}{stderr}\nTSC_TIMEOUT after {timeout}s\n"
        return _clear_failed_declarations(
            declaration_dir,
            files,
            TscStatus.TOOL_ERROR,
            -1,
            output,
            command,
        )
    except OSError as error:
        output = f"TSC_NOT_FOUND: {compiler}: {error}\n"
        return _clear_failed_declarations(
            declaration_dir,
            files,
            TscStatus.TOOL_ERROR,
            -1,
            output,
            command,
        )


def check_typescript(
    ts_files: Sequence[str | os.PathLike[str]],
    declaration_dir: str | os.PathLike[str] | None = None,
    timeout: int = 120,
) -> TscResult:
    """Compile root files using the declaration-emission evaluation contract.

    An empty normalized root set is a vacuous PASS after clearing the output.
    Dataset evaluators remain responsible for reporting a missing-input sample.
    """
    if declaration_dir is not None:
        return _run_check(ts_files, Path(declaration_dir), timeout)
    with tempfile.TemporaryDirectory(prefix="ast2type-tsc-") as temporary:
        return _run_check(ts_files, Path(temporary), timeout)


def write_text(path: str | None, content: str) -> None:
    if not path:
        return
    output = Path(path)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(content, encoding="utf-8")


def config_value(field: str) -> str:
    values = {
        "compiler": str(compiler_path()),
        "cwd": str(TSC_WORKING_DIRECTORY),
        "flags": shlex.join(COMMON_FLAGS),
        "declaration-flags": shlex.join(DECLARATION_FLAGS),
    }
    if field == "version":
        return compiler_version()
    return values[field]


def config_command(args: argparse.Namespace) -> int:
    print(config_value(args.field))
    return 0


def check_command(args: argparse.Namespace) -> int:
    result = check_typescript(
        args.files,
        declaration_dir=args.declaration_dir,
        timeout=args.timeout,
    )
    write_text(args.diagnostics_file, result.output)
    write_text(args.status_file, result.status.value + "\n")
    if result.status is TscStatus.PASS:
        return 0
    if result.status is TscStatus.TYPE_ERROR:
        return 1
    return 2


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    config = subparsers.add_parser("config", help="print one contract value")
    config.add_argument(
        "--field",
        choices=("compiler", "cwd", "version", "flags", "declaration-flags"),
        required=True,
    )
    config.set_defaults(handler=config_command)

    check = subparsers.add_parser("check", help="compile TypeScript and emit declarations")
    check.add_argument("--declaration-dir", required=True)
    check.add_argument("--diagnostics-file")
    check.add_argument("--status-file")
    check.add_argument("--timeout", type=int, default=120)
    check.add_argument("files", nargs="*")
    check.set_defaults(handler=check_command)
    return parser


def main() -> int:
    args = build_parser().parse_args()
    return args.handler(args)


if __name__ == "__main__":
    sys.exit(main())
