import contextlib
import io
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from generate import auto_fix, run_auto_fix_all
from generate.tsc_check import TscResult, TscStatus


ROOT = Path(__file__).resolve().parents[2]
TSC = ROOT / "node_modules" / ".bin" / "tsc"


def diagnostic(filepath, line, col, code, message="diagnostic"):
    return auto_fix.TscError(str(filepath), line, col, code, message)


def utf16_col(line, token, occurrence=0):
    start = -1
    for _ in range(occurrence + 1):
        start = line.index(token, start + 1)
    return len(line[:start].encode("utf-16-le")) // 2 + 1


class AstTypeLocatorTests(unittest.TestCase):
    def locate_and_apply(self, content, errors):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        source = root / "index.ts"
        with source.open("w", encoding="utf-8", newline="") as target:
            target.write(content)
        located = auto_fix._locate_type_edits([str(source)], errors(source), root)
        modified, replacements = auto_fix._apply_type_edits(
            [str(source)], located["edits"]
        )
        return source, located, modified, replacements

    def test_implicit_any_parameters_keep_valid_parameter_syntax(self):
        content = (
            "const bare = $value => $value;\n"
            "const asyncBare = async /* ( */ value => value;\n"
            "function optional(value?) { return value; }\n"
            "function defaulted(value = normalize(value)) { return value; }\n"
            "function rest(...values) { return values; }\n"
        )

        def errors(source):
            lines = content.splitlines()
            return [
                diagnostic(source, 1, lines[0].index("$value") + 1, 7006),
                diagnostic(source, 2, lines[1].index("value") + 1, 7006),
                diagnostic(source, 3, lines[2].index("value") + 1, 7006),
                diagnostic(source, 4, lines[3].index("value") + 1, 7006),
                diagnostic(source, 5, lines[4].index("values") + 1, 7006),
            ]

        source, located, _, replacements = self.locate_and_apply(content, errors)
        result = source.read_text(encoding="utf-8")

        self.assertEqual(located["skipped"], [])
        self.assertEqual(replacements, 5)
        self.assertIn("const bare = ($value: any) => $value;", result)
        self.assertIn(
            "const asyncBare = async /* ( */ (value: any) => value;", result
        )
        self.assertIn("optional(value?: any)", result)
        self.assertIn("defaulted(value: any = normalize(value))", result)
        self.assertIn("rest(...values: any[])", result)

    def test_assignment_errors_replace_only_the_containing_types(self):
        content = (
            "function outer(): string {\n"
            '  const value: number = "wrong";\n'
            "  return 1;\n"
            "}\n"
        )

        def errors(source):
            lines = content.splitlines()
            return [
                diagnostic(source, 2, lines[1].index('"wrong"') + 1, 2322),
                diagnostic(source, 3, lines[2].index("1") + 1, 2322),
            ]

        source, _, _, replacements = self.locate_and_apply(content, errors)
        result = source.read_text(encoding="utf-8")

        self.assertEqual(replacements, 2)
        self.assertIn("function outer(): any {", result)
        self.assertIn('const value: any = "wrong";', result)

    def test_index_error_does_not_rewrite_an_object_literal_property(self):
        content = (
            'const key: unknown = "name";\n'
            "const options = { key: key };\n"
            "const values = {};\n"
            "const result = values[key];\n"
        )

        def errors(source):
            line = content.splitlines()[3]
            return [diagnostic(source, 4, line.index("key") + 1, 2538)]

        source, _, _, replacements = self.locate_and_apply(content, errors)
        result = source.read_text(encoding="utf-8")

        self.assertEqual(replacements, 1)
        self.assertIn('const key: any = "name";', result)
        self.assertIn("const options = { key: key };", result)

    def test_property_error_uses_the_bound_declaration_and_keeps_defaults(self):
        content = (
            "declare function normalize(value: unknown): unknown;\n"
            "function outer(value: { ok: string }) {\n"
            "  function inner(value: { nested: number }) {\n"
            "    return value.missing;\n"
            "  }\n"
            "  return value.ok;\n"
            "}\n"
            "function match(value = normalize(value)) {\n"
            "  return value.length;\n"
            "}\n"
        )

        def errors(source):
            lines = content.splitlines()
            return [
                diagnostic(source, 4, lines[3].index("missing") + 1, 2339),
                diagnostic(source, 9, lines[8].index("length") + 1, 2339),
            ]

        source, _, _, replacements = self.locate_and_apply(content, errors)
        result = source.read_text(encoding="utf-8")

        self.assertEqual(replacements, 2)
        self.assertIn("outer(value: { ok: string })", result)
        self.assertIn("inner(value: any)", result)
        self.assertIn("match(value: any = normalize(value))", result)
        self.assertNotIn("normalize(value: any)", result)

    def test_for_of_binding_is_skipped_instead_of_creating_invalid_syntax(self):
        content = (
            "declare const styles: Record<string, unknown>;\n"
            "for (const [key, value] of Object.entries(styles)) {\n"
            "  console.log(value.open);\n"
            "}\n"
        )

        def errors(source):
            line = content.splitlines()[2]
            return [diagnostic(source, 3, line.index("open") + 1, 2339)]

        source, located, modified, replacements = self.locate_and_apply(content, errors)

        self.assertEqual(replacements, 0)
        self.assertEqual(modified, set())
        self.assertEqual(len(located["skipped"]), 1)
        self.assertEqual(source.read_text(encoding="utf-8"), content)

    def test_utf16_columns_and_crlf_are_preserved(self):
        line = (
            'const emoji = "\U0001f600"; const key: unknown = "x"; '
            "const result = values[key];\r\n"
        )

        def errors(source):
            return [diagnostic(source, 1, utf16_col(line, "key", occurrence=1), 2538)]

        source, _, _, replacements = self.locate_and_apply(line, errors)
        with source.open("r", encoding="utf-8", newline="") as handle:
            result = handle.read()

        self.assertEqual(replacements, 1)
        self.assertIn('emoji = "\U0001f600"', result)
        self.assertIn("key: any", result)
        self.assertEqual(result.count("\r\n"), 1)


class AutoFixOrchestrationTests(unittest.TestCase):
    def test_custom_type_checker_replaces_the_uniform_contract(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "index.ts"
            source.write_text("export {};\n", encoding="utf-8")
            calls = []

            def project_check(files, timeout):
                calls.append((tuple(files), timeout))
                return TscResult(TscStatus.PASS, 0, "", ("project-tsc",))

            with mock.patch.object(auto_fix, "check_typescript") as uniform_check:
                result = auto_fix.auto_fix_package(
                    root, timeout=17, type_checker=project_check
                )

            self.assertEqual(result.status, auto_fix.AutoFixStatus.PASS)
            self.assertEqual(calls, [((str(source.resolve()),), 17)])
            uniform_check.assert_not_called()

    def test_package_discovery_reuses_the_shared_typescript_contract(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            included = ["index.ts", "view.tsx", "module.mts", "common.cts"]
            excluded = ["types.d.ts", "types.d.mts", "types.d.cts", "arkts.ets"]
            for name in included + excluded:
                (root / name).write_text("export {};\n", encoding="utf-8")
            passed = TscResult(TscStatus.PASS, 0, "", ("tsc",))

            with mock.patch.object(
                auto_fix, "check_typescript", return_value=passed
            ) as check:
                result = auto_fix.auto_fix_package(root)

            self.assertEqual(result.status, auto_fix.AutoFixStatus.PASS)
            self.assertEqual(result.total_files, 4)
            checked = {Path(path).name for path in check.call_args.args[0]}
            self.assertEqual(checked, set(included))

    def test_diagnostic_path_mapping_does_not_guess_nested_basenames(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            top = root / "same.ts"
            nested = root / "nested" / "same.ts"
            nested.parent.mkdir()
            top.write_text("export {};\n", encoding="utf-8")
            nested.write_text("export {};\n", encoding="utf-8")
            files = [str(top.resolve()), str(nested.resolve())]

            self.assertEqual(
                auto_fix._resolve_diagnostic_file("nested/same.ts", files, root),
                str(nested.resolve()),
            )
            self.assertIsNone(
                auto_fix._resolve_diagnostic_file("other/same.ts", files, root)
            )

    def test_multi_round_statistics_count_unique_modified_files(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "index.ts"
            source.write_text("let first: string; let second: number;\n", encoding="utf-8")
            type_error = TscResult(
                TscStatus.TYPE_ERROR,
                2,
                f"{source}(1,5): error TS2322: mismatch\n",
                ("tsc",),
            )
            passed = TscResult(TscStatus.PASS, 0, "", ("tsc",))
            located = {"edits": [{"placeholder": True}], "skipped": []}

            with (
                mock.patch.object(
                    auto_fix,
                    "check_typescript",
                    side_effect=[type_error, type_error, passed],
                ),
                mock.patch.object(
                    auto_fix, "_locate_type_edits", return_value=located
                ),
                mock.patch.object(
                    auto_fix,
                    "_apply_type_edits",
                    side_effect=[({str(source.resolve())}, 1), ({str(source.resolve())}, 1)],
                ),
            ):
                result = auto_fix.auto_fix_package(root)

            self.assertEqual(result.status, auto_fix.AutoFixStatus.PASS)
            self.assertEqual(result.checks, 3)
            self.assertEqual(result.fix_rounds, 2)
            self.assertEqual(result.modified_files, 1)
            self.assertEqual(result.replacements, 2)

    def test_dependency_diagnostic_never_becomes_a_false_pass(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "index.ts"
            source.write_text("export {};\n", encoding="utf-8")
            failure = TscResult(
                TscStatus.TYPE_ERROR,
                2,
                "dependency/index.ts(1,1): error TS2322: mismatch\n",
                ("tsc",),
            )

            with mock.patch.object(
                auto_fix, "check_typescript", return_value=failure
            ):
                result = auto_fix.auto_fix_file(source)

            self.assertEqual(result.status, auto_fix.AutoFixStatus.TYPE_ERROR)
            self.assertFalse(result.passed)
            self.assertEqual(result.fix_rounds, 0)
            self.assertEqual(result.skipped_diagnostics, 1)

    def test_repeated_diagnostics_share_one_declaration_edit(self):
        content = (
            "const value: { ok: string } = { ok: 'yes' };\n"
            "value.first;\n"
            "value.second;\n"
        )

        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "index.ts"
            source.write_text(content, encoding="utf-8")
            errors = [
                diagnostic(source, 2, content.splitlines()[1].index("first") + 1, 2339),
                diagnostic(source, 3, content.splitlines()[2].index("second") + 1, 2339),
            ]

            located = auto_fix._locate_type_edits([str(source)], errors, root)

            self.assertEqual(len(located["edits"]), 1)
            self.assertEqual(located["skipped"], [])

    @unittest.skipUnless(TSC.is_file(), "repository TypeScript compiler is unavailable")
    def test_real_type_error_is_widened_to_a_compiling_annotation(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "index.ts"
            source.write_text(
                'export const value: number = "wrong";\n', encoding="utf-8"
            )

            with mock.patch.dict(os.environ, {"AST2TYPE_TSC_BIN": ""}):
                result = auto_fix.auto_fix_package(root)

            self.assertEqual(result.initial_status, auto_fix.AutoFixStatus.TYPE_ERROR)
            self.assertEqual(result.status, auto_fix.AutoFixStatus.PASS)
            self.assertEqual(result.fix_rounds, 1)
            self.assertEqual(result.modified_files, 1)
            self.assertEqual(result.replacements, 1)
            self.assertEqual(
                source.read_text(encoding="utf-8"),
                'export const value: any = "wrong";\n',
            )


class AutoFixBatchTests(unittest.TestCase):
    def result(self, status, target, *, initial=None):
        initial_status = initial or status
        diagnostics = 0 if status is auto_fix.AutoFixStatus.PASS else 1
        return auto_fix.AutoFixResult(
            status=status,
            initial_status=initial_status,
            total_files=1,
            checks=2 if initial_status is not status else 1,
            fix_rounds=1 if initial_status is not status else 0,
            modified_files=1 if initial_status is not status else 0,
            replacements=1 if initial_status is not status else 0,
            initial_diagnostics=1 if initial_status is not status else diagnostics,
            final_diagnostics=diagnostics,
            skipped_diagnostics=0,
            modified_paths=(str(target / "index.ts"),)
            if initial_status is not status
            else (),
        )

    def test_discovers_scoped_packages_using_shared_source_extensions(self):
        with tempfile.TemporaryDirectory() as temporary:
            baseline = Path(temporary)
            included = baseline / "@scope" / "included"
            excluded = baseline / "@scope" / "excluded"
            included.mkdir(parents=True)
            excluded.mkdir(parents=True)
            (included / "index.cts").write_text("export {};\n", encoding="utf-8")
            (excluded / "index.ets").write_text("export {};\n", encoding="utf-8")

            self.assertEqual(
                run_auto_fix_all.discover_packages(baseline),
                ["@scope/included"],
            )

    def test_direct_cli_entrypoint_can_render_help(self):
        completed = subprocess.run(
            [sys.executable, str(ROOT / "generate" / "run_auto_fix_all.py"), "--help"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=30,
        )

        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertIn("--baseline-dir", completed.stdout)

    def test_rejects_package_paths_that_escape_the_baseline(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            baseline = root / "baseline"
            outside = root / "outside"
            baseline.mkdir()
            outside.mkdir()
            (baseline / "link").symlink_to(outside, target_is_directory=True)

            for name in ("../outside", str(outside.resolve()), "link"):
                with self.subTest(name=name):
                    with self.assertRaises(ValueError):
                        run_auto_fix_all.resolve_package(baseline, name)

    def test_copy_on_write_preserves_source_and_records_manifest(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            baseline = root / "baseline"
            package = baseline / "sample"
            output = root / "baseline-fixed"
            results = output / "auto-fix-results.json"
            package.mkdir(parents=True)
            source = package / "index.ts"
            source.write_text('export const value: number = "wrong";\n', encoding="utf-8")
            (package / "node_modules").mkdir()
            (package / "node_modules" / "ignored.ts").write_text(
                "export {};\n", encoding="utf-8"
            )
            (package / ".git").mkdir()
            (package / ".git" / "ignored.ts").write_text(
                "export {};\n", encoding="utf-8"
            )
            received = {}

            def fake_auto_fix(target, **kwargs):
                received.update(kwargs)
                target = Path(target)
                target_source = target / "index.ts"
                target_source.write_text(
                    'export const value: any = "wrong";\n', encoding="utf-8"
                )
                return self.result(
                    auto_fix.AutoFixStatus.PASS,
                    target,
                    initial=auto_fix.AutoFixStatus.TYPE_ERROR,
                )

            with (
                mock.patch.object(
                    run_auto_fix_all, "auto_fix_package", side_effect=fake_auto_fix
                ),
                mock.patch.object(
                    run_auto_fix_all, "compiler_version", return_value="Version test"
                ),
            ):
                exit_code = run_auto_fix_all.main([
                    "--baseline-dir",
                    str(baseline),
                    "--max-rounds",
                    "3",
                    "--timeout",
                    "45",
                ])

            self.assertEqual(exit_code, 0)
            self.assertEqual(received, {"max_rounds": 3, "timeout": 45})
            self.assertEqual(
                source.read_text(encoding="utf-8"),
                'export const value: number = "wrong";\n',
            )
            self.assertEqual(
                (output / "sample" / "index.ts").read_text(encoding="utf-8"),
                'export const value: any = "wrong";\n',
            )
            self.assertFalse((output / "sample" / "node_modules").exists())
            self.assertFalse((output / "sample" / ".git").exists())
            manifest = json.loads(results.read_text(encoding="utf-8"))
            self.assertFalse(manifest["in_place"])
            self.assertEqual(manifest["compiler"]["version"], "Version test")
            self.assertEqual(manifest["status_counts"], {"PASS": 1})
            self.assertEqual(manifest["results"][0]["modified_files"], 1)
            self.assertEqual(manifest["results"][0]["modified_paths"], ["index.ts"])
            self.assertNotEqual(
                manifest["results"][0]["source_fingerprint"],
                manifest["results"][0]["target_fingerprint"],
            )

    def test_existing_results_are_rejected_before_copy_or_fix(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            baseline = root / "baseline"
            package = baseline / "sample"
            output = root / "fixed"
            results = root / "results.json"
            package.mkdir(parents=True)
            (package / "index.ts").write_text("export {};\n", encoding="utf-8")
            results.write_text("existing\n", encoding="utf-8")

            with (
                mock.patch.object(run_auto_fix_all, "auto_fix_package") as fix,
                contextlib.redirect_stderr(io.StringIO()),
                self.assertRaises(SystemExit) as raised,
            ):
                run_auto_fix_all.main([
                    "--baseline-dir",
                    str(baseline),
                    "--output-dir",
                    str(output),
                    "--results",
                    str(results),
                ])

            self.assertEqual(raised.exception.code, 2)
            self.assertFalse(output.exists())
            fix.assert_not_called()

    def test_copy_on_write_rejects_results_inside_the_baseline(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            baseline = root / "baseline"
            package = baseline / "sample"
            output = root / "fixed"
            package.mkdir(parents=True)
            (package / "index.ts").write_text("export {};\n", encoding="utf-8")

            with (
                mock.patch.object(run_auto_fix_all, "auto_fix_package") as fix,
                contextlib.redirect_stderr(io.StringIO()),
                self.assertRaises(SystemExit) as raised,
            ):
                run_auto_fix_all.main([
                    "--baseline-dir",
                    str(baseline),
                    "--output-dir",
                    str(output),
                    "--results",
                    str(baseline / "results.json"),
                ])

            self.assertEqual(raised.exception.code, 2)
            self.assertFalse(output.exists())
            fix.assert_not_called()

    def test_results_cannot_overlap_a_future_package_output(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            baseline = root / "baseline"
            package = baseline / "sample"
            output = root / "fixed"
            package.mkdir(parents=True)
            (package / "index.ts").write_text("export {};\n", encoding="utf-8")

            with (
                mock.patch.object(run_auto_fix_all, "auto_fix_package") as fix,
                contextlib.redirect_stderr(io.StringIO()),
                self.assertRaises(SystemExit) as raised,
            ):
                run_auto_fix_all.main([
                    "--baseline-dir",
                    str(baseline),
                    "--output-dir",
                    str(output),
                    "--results",
                    str(output / "sample" / "index.ts"),
                ])

            self.assertEqual(raised.exception.code, 2)
            self.assertFalse(output.exists())
            fix.assert_not_called()

    def test_exit_codes_distinguish_type_and_tool_failures(self):
        cases = [
            (auto_fix.AutoFixStatus.TYPE_ERROR, 1),
            (auto_fix.AutoFixStatus.TOOL_ERROR, 2),
            (auto_fix.AutoFixStatus.EMPTY, 1),
        ]
        for status, expected in cases:
            with self.subTest(status=status), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                baseline = root / "baseline"
                package = baseline / "sample"
                package.mkdir(parents=True)
                (package / "index.ts").write_text("export {};\n", encoding="utf-8")

                with (
                    mock.patch.object(
                        run_auto_fix_all,
                        "auto_fix_package",
                        side_effect=lambda target, **_kwargs: self.result(
                            status, Path(target)
                        ),
                    ),
                    mock.patch.object(
                        run_auto_fix_all,
                        "compiler_version",
                        return_value="Version test",
                    ),
                ):
                    actual = run_auto_fix_all.main([
                        "--baseline-dir",
                        str(baseline),
                        "--output-dir",
                        str(root / "fixed"),
                        "--results",
                        str(root / "results.json"),
                    ])

                self.assertEqual(actual, expected)

    def test_package_exception_is_recorded_and_the_batch_continues(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            baseline = root / "baseline"
            results = root / "results.json"
            for name in ("broken", "working"):
                package = baseline / name
                package.mkdir(parents=True)
                (package / "index.ts").write_text("export {};\n", encoding="utf-8")

            visited = []

            def fake_auto_fix(target, **_kwargs):
                target = Path(target)
                visited.append(target.name)
                if target.name == "broken":
                    raise RuntimeError("simulated package failure")
                return self.result(auto_fix.AutoFixStatus.PASS, target)

            with (
                mock.patch.object(
                    run_auto_fix_all, "auto_fix_package", side_effect=fake_auto_fix
                ),
                mock.patch.object(
                    run_auto_fix_all, "compiler_version", return_value="Version test"
                ),
            ):
                exit_code = run_auto_fix_all.main([
                    "--baseline-dir",
                    str(baseline),
                    "--output-dir",
                    str(root / "fixed"),
                    "--results",
                    str(results),
                ])

            self.assertEqual(exit_code, 2)
            self.assertEqual(visited, ["broken", "working"])
            manifest = json.loads(results.read_text(encoding="utf-8"))
            self.assertEqual(manifest["status_counts"], {"ERROR": 1, "PASS": 1})
            self.assertEqual(
                [record["status"] for record in manifest["results"]],
                ["ERROR", "PASS"],
            )
            self.assertIn("simulated package failure", manifest["results"][0]["message"])


if __name__ == "__main__":
    unittest.main()
