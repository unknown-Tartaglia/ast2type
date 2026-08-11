#!/usr/bin/env python3
"""Run type erasure, inference, and annotation restoration on TS projects."""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from generate.weave_erased_ts import weave_project


TS_EXTENSIONS = {".ts", ".tsx", ".mts", ".cts", ".ets"}
INFERENCE_MANIFEST = "inference-manifest.json"
# Keep these defaults synchronized with agent/net.ts so manifests record the
# exact API configuration used by ast2type.
AGENT_DEFAULT_MODELS = {
    "deepseek": "deepseek-chat",
    "openai": "gpt-4.1-mini",
}
AGENT_DEFAULT_BASE_URLS = {
    "deepseek": "https://api.deepseek.com/v1",
    "openai": "https://api.openai.com/v1",
}


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


def _resolve_agent_identity(
    use_agent: bool,
    agent_provider: str | None = None,
    agent_model: str | None = None,
    agent_base_url: str | None = None,
) -> tuple[str | None, str | None, str | None]:
    if not use_agent:
        return None, None, None
    provider = (agent_provider or "deepseek").strip().lower()
    if provider not in AGENT_DEFAULT_MODELS:
        raise ValueError(f"unsupported agent provider: {provider}")
    return (
        provider,
        agent_model or AGENT_DEFAULT_MODELS[provider],
        (agent_base_url or AGENT_DEFAULT_BASE_URLS[provider]).strip().rstrip("/"),
    )


def _manifest(
    use_agent: bool,
    agent_provider: str | None = None,
    agent_model: str | None = None,
    agent_base_url: str | None = None,
) -> dict:
    provider, model, base_url = _resolve_agent_identity(
        use_agent, agent_provider, agent_model, agent_base_url
    )
    return {
        "schema": 2,
        "agent": use_agent,
        "agentCandidateMode": "fair" if use_agent else None,
        "agentProvider": provider,
        "agentModel": model,
        "agentBaseUrl": base_url,
    }


def _write_manifest(
    inference: Path,
    use_agent: bool,
    agent_provider: str | None = None,
    agent_model: str | None = None,
    agent_base_url: str | None = None,
) -> None:
    (inference / INFERENCE_MANIFEST).write_text(
        json.dumps(
            _manifest(use_agent, agent_provider, agent_model, agent_base_url),
            indent=2,
        ),
        encoding="utf-8",
    )


def _assert_compatible_inference(
    inference: Path,
    use_agent: bool,
    agent_provider: str | None = None,
    agent_model: str | None = None,
    agent_base_url: str | None = None,
) -> None:
    manifest_path = inference / INFERENCE_MANIFEST
    if not manifest_path.is_file():
        raise RuntimeError(f"reused inference has no mode manifest: {manifest_path}")
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    requested_manifest = _manifest(
        use_agent, agent_provider, agent_model, agent_base_url
    )
    if manifest != requested_manifest:
        requested = "agent" if use_agent else "standard"
        previous = "agent" if manifest.get("agent") else "standard"
        if requested == previous == "agent":
            raise RuntimeError(
                "cannot reuse agent inference with different API configuration: "
                f"requested {requested_manifest['agentProvider']}/"
                f"{requested_manifest['agentModel']} at "
                f"{requested_manifest['agentBaseUrl']}, found "
                f"{manifest.get('agentProvider')}/{manifest.get('agentModel')} at "
                f"{manifest.get('agentBaseUrl')}"
            )
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
    agent_provider: str | None = None,
    agent_model: str | None = None,
    agent_base_url: str | None = None,
) -> dict:
    resolved_provider, resolved_model, resolved_base_url = _resolve_agent_identity(
        use_agent, agent_provider, agent_model, agent_base_url
    )
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
        _assert_compatible_inference(
            previous_work / "inference",
            use_agent,
            resolved_provider,
            resolved_model,
            resolved_base_url,
        )
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
            assert resolved_provider and resolved_model and resolved_base_url
            infer_command.extend([
                "--agent",
                "--agent-provider", resolved_provider,
                "--agent-model", resolved_model,
                "--agent-base-url", resolved_base_url,
            ])
        # Ground truth is intentionally not passed to ast2type.
        _run(infer_command, timeout)
        _require_inference(inference)
        _write_manifest(
            inference,
            use_agent,
            resolved_provider,
            resolved_model,
            resolved_base_url,
        )

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
    if use_agent:
        summary.update({
            "agentProvider": resolved_provider,
            "agentModel": resolved_model,
            "agentBaseUrl": resolved_base_url,
        })
    (work / "summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print("  summary:", json.dumps(summary), flush=True)
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--projects-root", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--packages", required=True, help="comma-separated project directories")
    parser.add_argument("--agent", action="store_true")
    parser.add_argument("--agent-provider", choices=sorted(AGENT_DEFAULT_MODELS))
    parser.add_argument("--agent-model")
    parser.add_argument("--agent-base-url")
    parser.add_argument("--timeout", type=int, default=1200)
    parser.add_argument(
        "--reuse-inference-root",
        type=Path,
        help="reuse <root>/work/<project>/inference after verifying erased sources are byte-identical",
    )
    args = parser.parse_args()

    output_root = args.output_root.resolve()
    output_root.mkdir(parents=True, exist_ok=True)
    agent_provider = args.agent_provider or os.environ.get("AGENT_PROVIDER")
    provider_for_env = (agent_provider or "deepseek").upper()
    agent_model = (
        args.agent_model
        or os.environ.get("AGENT_MODEL")
        or os.environ.get(f"{provider_for_env}_MODEL")
    )
    agent_base_url = (
        args.agent_base_url
        or os.environ.get("AGENT_BASE_URL")
        or os.environ.get(f"{provider_for_env}_BASE_URL")
    )
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
            agent_provider,
            agent_model,
            agent_base_url,
        ))
    (output_root / "summary.json").write_text(json.dumps(summaries, indent=2), encoding="utf-8")


if __name__ == "__main__":
    main()
