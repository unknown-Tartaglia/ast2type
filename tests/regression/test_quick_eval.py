import csv
import hashlib
import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path


AST2TYPE_ROOT = Path(__file__).resolve().parents[2]
AOT_ROOT = AST2TYPE_ROOT.parent
TYPEWEAVER_ROOT = AOT_ROOT / "TypeWeaver"
QUICK_EVAL = TYPEWEAVER_ROOT / "quick_eval.sh"
TSC = (AST2TYPE_ROOT / "node_modules" / ".bin" / "tsc").resolve()


class QuickEvalFixture:
    def __init__(self, root: Path, dataset: str = "regression"):
        self.data_root = root
        self.dataset = dataset
        self.experiment = root / "Pipeline-out" / dataset
        self.source = self.experiment / "source"
        self.baseline = self.experiment / "baseline"
        self.groundtruth = root / "groundtruth"
        self.packages = []

    def add_package(self, name: str, js_source: str, ts_source: str, declaration: str):
        self.packages.append(name)
        source_dir = self.source / name
        baseline_dir = self.baseline / name
        truth_dir = self.groundtruth / name
        source_dir.mkdir(parents=True, exist_ok=True)
        baseline_dir.mkdir(parents=True, exist_ok=True)
        truth_dir.mkdir(parents=True, exist_ok=True)
        (source_dir / "index.js").write_text(js_source, encoding="utf-8")
        (baseline_dir / "index.ts").write_text(ts_source, encoding="utf-8")
        (truth_dir / "index.d.ts").write_text(declaration, encoding="utf-8")

    def finish(self):
        self.experiment.mkdir(parents=True, exist_ok=True)
        (self.experiment / "conf").write_text(
            "".join(f"{package}\n" for package in self.packages), encoding="utf-8"
        )

    def run(self, run_id: str, extra_env=None):
        self.finish()
        env = os.environ.copy()
        env.update(
            {
                "TYPEWEAVER_DATA_ROOT": str(self.data_root),
                "RUN_ID": run_id,
            }
        )
        if extra_env:
            env.update(extra_env)
        return subprocess.run(
            [str(QUICK_EVAL), "-d", self.dataset, "--tsc-only"],
            cwd=TYPEWEAVER_ROOT,
            env=env,
            capture_output=True,
            text=True,
            timeout=90,
        )


class QuickEvalTests(unittest.TestCase):
    def require_real_tsc(self):
        if not TSC.is_file():
            self.skipTest("repository TypeScript compiler is unavailable")
        try:
            completed = subprocess.run(
                [str(TSC), "--version"],
                cwd=AST2TYPE_ROOT,
                capture_output=True,
                text=True,
                timeout=30,
            )
        except (OSError, subprocess.SubprocessError):
            self.skipTest("repository TypeScript compiler is unavailable")
        if completed.returncode != 0:
            self.skipTest("repository TypeScript compiler is unavailable")

    def assert_run_succeeded(self, completed):
        self.assertEqual(
            completed.returncode,
            0,
            f"stdout:\n{completed.stdout}\nstderr:\n{completed.stderr}",
        )

    def test_successful_run_writes_manifest_log_and_results(self):
        self.require_real_tsc()
        with tempfile.TemporaryDirectory() as temporary:
            fixture = QuickEvalFixture(Path(temporary))
            fixture.add_package(
                "good",
                "export function add(left, right) { return left + right; }\n",
                "export function add(left: number, right: number): number { return left + right; }\n",
                "export function add(left: number, right: number): number;\n",
            )
            completed = fixture.run("successful-run")
            self.assert_run_succeeded(completed)

            run_dir = fixture.experiment / "runs" / "successful-run"
            manifest_path = run_dir / "manifest.json"
            manifest = json.loads(manifest_path.read_text(encoding="utf-8"))

            self.assertEqual(manifest["run"]["status"], "completed")
            self.assertEqual(manifest["generation"]["mode"], "existing_artifacts")
            self.assertEqual(manifest["results"]["status_counts"], {"PASS": 1})
            self.assertEqual(Path(manifest["compiler"]["command"]), TSC)
            self.assertEqual(manifest["compiler"]["working_directory"], str(AST2TYPE_ROOT))
            self.assertEqual(manifest["compiler"]["version"], "Version 5.9.3")
            self.assertIn("--moduleResolution bundler", manifest["compiler"]["flags"])
            self.assertIn("--noEmitOnError", manifest["compiler"]["evaluation_command"])
            self.assertEqual(manifest["fingerprints"]["source_javascript"]["file_count"], 1)
            self.assertEqual(manifest["fingerprints"]["generated_typescript"]["file_count"], 1)
            self.assertTrue((run_dir / "run.log").stat().st_size > 0)
            self.assertIn("good\tPASS", (run_dir / "results.tsv").read_text(encoding="utf-8"))

    def test_typescript_debug_failure_is_reported_as_tool_error(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            fixture = QuickEvalFixture(root)
            fixture.add_package(
                "crash",
                "export function crash() {}\n",
                "export function crash(): void {}\n",
                "export function crash(): void;\n",
            )
            fake_bin = root / "bin"
            fake_bin.mkdir()
            fake_tsc = fake_bin / "tsc"
            fake_tsc.write_text(
                "#!/bin/sh\n"
                "if [ \"$1\" = --version ]; then\n"
                "  echo 'Version regression-debug-failure'\n"
                "  exit 0\n"
                "fi\n"
                "echo 'Error: Debug Failure.' >&2\n"
                "exit 2\n",
                encoding="utf-8",
            )
            fake_tsc.chmod(0o755)
            completed = fixture.run(
                "tool-error-run", {"AST2TYPE_TSC_BIN": str(fake_tsc)}
            )
            self.assert_run_succeeded(completed)

            run_dir = fixture.experiment / "runs" / "tool-error-run"
            manifest = json.loads((run_dir / "manifest.json").read_text(encoding="utf-8"))
            self.assertEqual(manifest["results"]["status_counts"], {"TOOL_ERROR": 1})
            self.assertTrue(
                (fixture.experiment / "baseline-checked" / "crash.tool-error").is_file()
            )
            self.assertIn("crash\tTOOL_ERROR", (run_dir / "results.tsv").read_text())

    def test_accuracy_ignores_partial_declarations_from_failed_packages(self):
        self.require_real_tsc()
        with tempfile.TemporaryDirectory() as temporary:
            fixture = QuickEvalFixture(Path(temporary))
            fixture.add_package(
                "good",
                "export function good(value) { return value; }\n",
                "export function good(value: string): string { return value; }\n",
                "export function good(value: string): string;\n",
            )
            fixture.add_package(
                "broken",
                "export function broken(value) { return value; }\n",
                "export function broken(value: string): string { return 1; }\n",
                "export function broken(value: string): string;\n",
            )
            completed = fixture.run("partial-declaration-run")
            self.assert_run_succeeded(completed)

            with (fixture.experiment / "accuracy.csv").open(newline="") as handle:
                rows = {row["Package"]: row for row in csv.DictReader(handle)}
            broken = rows.get("broken")
            self.assertTrue(
                broken is None or int(broken["SigsCompared"]) == 0,
                "a TYPE_ERROR package contributed a partially emitted declaration",
            )
            self.assertEqual(
                list((fixture.experiment / "baseline-typedefs" / "broken").rglob("*.d.ts")),
                [],
            )
            manifest = json.loads(
                (
                    fixture.experiment
                    / "runs"
                    / "partial-declaration-run"
                    / "manifest.json"
                ).read_text(encoding="utf-8")
            )
            self.assertEqual(
                manifest["results"]["status_counts"],
                {"PASS": 1, "TYPE_ERROR": 1},
            )

    def test_accuracy_uses_typeweaver_official_compatibility_semantics(self):
        self.require_real_tsc()
        with tempfile.TemporaryDirectory() as temporary:
            fixture = QuickEvalFixture(Path(temporary))
            fixture.add_package(
                "compatibility",
                "export function compare(value, fallback) { return [value.name, fallback]; }\n",
                "type Widget = { name: string };\n"
                "export function compare(value: Widget, fallback: any): readonly string[] {\n"
                "  return [value.name, String(fallback)];\n"
                "}\n",
                "export function compare(value: widget, fallback: number): string[];\n",
            )
            completed = fixture.run("official-accuracy-run")
            self.assert_run_succeeded(completed)

            with (fixture.experiment / "accuracy.csv").open(newline="") as handle:
                rows = list(csv.DictReader(handle))
            self.assertEqual(len(rows), 1)
            self.assertEqual(
                rows[0],
                {
                    "Package": "compatibility",
                    "SigsCompared": "1",
                    "Correct": "1",
                    "InferredAnys": "1",
                    "Checked": "3",
                    "Accuracy": "33.3",
                    "AnyRate": "25.0",
                },
            )

            manifest = json.loads(
                (
                    fixture.experiment
                    / "runs"
                    / "official-accuracy-run"
                    / "manifest.json"
                ).read_text(encoding="utf-8")
            )
            self.assertEqual(
                manifest["metrics"]["comparator"],
                "TypeWeaver Summarizer._accuracy_per_package",
            )
            self.assertEqual(
                manifest["metrics"]["any_rate"],
                "inferred anys / (inferred anys + checked)",
            )
            comparator = TYPEWEAVER_ROOT / "src" / "summarize_results.py"
            self.assertEqual(
                manifest["metrics"]["comparator_source"],
                str(comparator),
            )
            self.assertEqual(
                manifest["metrics"]["comparator_source_sha256"],
                hashlib.sha256(comparator.read_bytes()).hexdigest(),
            )


if __name__ == "__main__":
    unittest.main()
