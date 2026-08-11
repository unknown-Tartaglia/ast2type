import argparse
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from generate import tsc_check


ROOT = Path(__file__).resolve().parents[2]
TSC = ROOT / "node_modules" / ".bin" / "tsc"


class TypeScriptSourceDiscoveryTests(unittest.TestCase):
    def test_discovers_supported_sources_deterministically(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            included = [
                root / "index.ts",
                root / "view.tsx",
                root / "module.mts",
                root / "common.cts",
                root / "nested" / "value.ts",
            ]
            excluded = [
                root / "types.d.ts",
                root / "types.d.mts",
                root / "types.d.cts",
                root / "arkts.ets",
                root / "index.js",
                root / "node_modules" / "dependency.ts",
                root / ".git" / "generated.ts",
            ]
            for path in included + excluded:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("export {};\n", encoding="utf-8")

            discovered = tsc_check.discover_typescript_files(root)

            self.assertEqual(discovered, sorted(str(path.resolve()) for path in included))
            self.assertEqual(
                tsc_check.discover_typescript_files(included[0]),
                [str(included[0].resolve())],
            )
            self.assertEqual(tsc_check.discover_typescript_files(root / "missing"), [])


class TypeScriptContractConfigurationTests(unittest.TestCase):
    def test_uses_repository_compiler_and_fixed_declaration_flags(self):
        with mock.patch.dict(os.environ, {"AST2TYPE_TSC_BIN": ""}):
            self.assertEqual(tsc_check.compiler_path(), TSC.resolve())
        self.assertEqual(tsc_check.TSC_WORKING_DIRECTORY, ROOT)
        self.assertIn("--moduleResolution", tsc_check.COMMON_FLAGS)
        self.assertIn("bundler", tsc_check.COMMON_FLAGS)
        self.assertIn("--jsx", tsc_check.COMMON_FLAGS)
        self.assertIn("preserve", tsc_check.COMMON_FLAGS)
        self.assertIn("--emitDeclarationOnly", tsc_check.DECLARATION_FLAGS)
        self.assertIn("--noEmitOnError", tsc_check.DECLARATION_FLAGS)

    def test_compiler_override_and_version_failure_are_explicit(self):
        with tempfile.TemporaryDirectory() as temporary:
            compiler = Path(temporary) / "custom-tsc"
            with mock.patch.dict(os.environ, {"AST2TYPE_TSC_BIN": str(compiler)}):
                self.assertEqual(tsc_check.compiler_path(), compiler.resolve())

        failed = subprocess.CompletedProcess(
            args=["tsc", "--version"],
            returncode=1,
            stdout="",
            stderr="compiler failed\n",
        )
        with mock.patch.object(tsc_check.subprocess, "run", return_value=failed):
            self.assertEqual(tsc_check.compiler_version(), "unavailable")
        with mock.patch.object(tsc_check, "compiler_version") as version:
            self.assertIn("--jsx", tsc_check.config_value("flags"))
            version.assert_not_called()

    def test_classifies_type_and_tool_failures_separately(self):
        cases = [
            (0, "", tsc_check.TscStatus.PASS),
            (2, "error TS2322: not assignable", tsc_check.TscStatus.TYPE_ERROR),
            (-9, "", tsc_check.TscStatus.TOOL_ERROR),
            (2, "Error: Debug Failure.", tsc_check.TscStatus.TOOL_ERROR),
            (0, "Error: Debug Failure.", tsc_check.TscStatus.TOOL_ERROR),
            (0, "error TS2322: inconsistent wrapper", tsc_check.TscStatus.TOOL_ERROR),
            (2, "compiler wrapper failed", tsc_check.TscStatus.TOOL_ERROR),
            (137, "error TS2322: partial output", tsc_check.TscStatus.TOOL_ERROR),
            (
                2,
                "index.ts(1,1): error TS2322: "
                "Type '\"FATAL ERROR\"' is not assignable to type '\"ok\"'.",
                tsc_check.TscStatus.TYPE_ERROR,
            ),
        ]
        for returncode, output, expected in cases:
            with self.subTest(returncode=returncode, output=output):
                self.assertEqual(tsc_check._classify(returncode, output), expected)


class TypeScriptContractExecutionTests(unittest.TestCase):
    def test_project_contract_uses_selected_config_compiler_and_working_directory(self):
        with tempfile.TemporaryDirectory() as temporary:
            project = Path(temporary)
            config = project / "evaluation.json"
            config.write_text("{}\n", encoding="utf-8")
            completed = subprocess.CompletedProcess(
                args=[], returncode=0, stdout="", stderr=""
            )
            with mock.patch.object(
                tsc_check.subprocess, "run", return_value=completed
            ) as run_tsc:
                result = tsc_check.check_typescript_project(
                    project,
                    compiler=project / "node_modules" / ".bin" / "tsc",
                    config=config.name,
                    extra_args=("--types", "node"),
                    timeout=17,
                )

            self.assertEqual(result.status, tsc_check.TscStatus.PASS)
            self.assertEqual(result.command[1:3], ("--project", str(config.resolve())))
            self.assertEqual(result.command[-2:], ("--types", "node"))
            self.assertEqual(run_tsc.call_args.kwargs["cwd"], project.resolve())
            self.assertEqual(run_tsc.call_args.kwargs["timeout"], 17)

    def test_normalizes_filters_and_sorts_root_files(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            first = root / "a.ts"
            second = root / "b.cts"
            declaration = root / "types.d.ts"
            unsupported = root / "arkts.ets"
            for path in (first, second, declaration, unsupported):
                path.write_text("export {};\n", encoding="utf-8")
            completed = subprocess.CompletedProcess(
                args=[], returncode=0, stdout="", stderr=""
            )

            with (
                mock.patch.object(tsc_check, "compiler_path", return_value=Path("/fake/tsc")),
                mock.patch.object(tsc_check.subprocess, "run", return_value=completed),
            ):
                result = tsc_check.check_typescript(
                    [second, first, second, declaration, unsupported],
                    root / "declarations",
                )

            declaration_index = result.command.index("--declarationDir")
            self.assertEqual(
                result.command[declaration_index + 2 :],
                (str(first.resolve()), str(second.resolve())),
            )
            self.assertEqual(result.status, tsc_check.TscStatus.PASS)

    @unittest.skipUnless(TSC.is_file(), "repository TypeScript compiler is unavailable")
    def test_emits_only_for_successful_compilation_and_clears_stale_output(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            valid = root / "valid.ts"
            view = root / "view.tsx"
            esm = root / "module.mts"
            commonjs = root / "common.cts"
            invalid = root / "invalid.ts"
            marker_invalid = root / "marker-invalid.ts"
            declarations = root / "declarations"
            valid.write_text(
                "export function value(input: string): string { return input; }\n",
                encoding="utf-8",
            )
            invalid.write_text(
                "export function value(input: string): string { return 1; }\n",
                encoding="utf-8",
            )
            marker_invalid.write_text(
                'export const value: "ok" = "FATAL ERROR";\n',
                encoding="utf-8",
            )
            view.write_text(
                "declare namespace JSX { interface IntrinsicElements { div: {} } }\n"
                "export const view = <div />;\n",
                encoding="utf-8",
            )
            esm.write_text("export const esm = true;\n", encoding="utf-8")
            commonjs.write_text("export const commonjs = true;\n", encoding="utf-8")

            with mock.patch.dict(os.environ, {"AST2TYPE_TSC_BIN": ""}):
                valid_result = tsc_check.check_typescript(
                    [valid, view, esm, commonjs], declarations
                )
                self.assertTrue((declarations / "valid.d.ts").is_file())
                self.assertTrue((declarations / "view.d.ts").is_file())
                self.assertTrue((declarations / "module.d.mts").is_file())
                self.assertTrue((declarations / "common.d.cts").is_file())
                invalid_result = tsc_check.check_typescript([invalid], declarations)
                marker_result = tsc_check.check_typescript(
                    [marker_invalid], declarations
                )

            self.assertEqual(valid_result.status, tsc_check.TscStatus.PASS)
            self.assertEqual(invalid_result.status, tsc_check.TscStatus.TYPE_ERROR)
            self.assertIn("TS2322", invalid_result.output)
            self.assertEqual(marker_result.status, tsc_check.TscStatus.TYPE_ERROR)
            self.assertIn("FATAL ERROR", marker_result.output)
            self.assertEqual(list(declarations.rglob("*.d.ts")), [])

            empty_result = tsc_check.check_typescript([], declarations)
            self.assertEqual(empty_result.status, tsc_check.TscStatus.PASS)
            self.assertEqual(list(declarations.iterdir()), [])

    def test_missing_compiler_and_timeout_are_tool_errors(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "index.ts"
            source.write_text("export {};\n", encoding="utf-8")
            with mock.patch.dict(
                os.environ,
                {"AST2TYPE_TSC_BIN": str(root / "missing-tsc")},
            ):
                missing = tsc_check.check_typescript([source], root / "missing-out")
            self.assertEqual(missing.status, tsc_check.TscStatus.TOOL_ERROR)
            self.assertIn("TSC_NOT_FOUND", missing.output)

            timeout_output = root / "timeout-out"

            def time_out(*args, **kwargs):
                (timeout_output / "partial.d.ts").write_text(
                    "export declare const partial: true;\n", encoding="utf-8"
                )
                raise subprocess.TimeoutExpired(
                    cmd=["tsc"],
                    timeout=3,
                    output=b"partial stdout",
                    stderr=b"partial stderr",
                )

            with mock.patch.object(tsc_check.subprocess, "run", side_effect=time_out):
                timed_out = tsc_check.check_typescript(
                    [source], timeout_output, timeout=3
                )
            self.assertEqual(timed_out.status, tsc_check.TscStatus.TOOL_ERROR)
            self.assertIn("partial stdoutpartial stderr", timed_out.output)
            self.assertIn("TSC_TIMEOUT after 3s", timed_out.output)
            self.assertEqual(list(timeout_output.iterdir()), [])

            type_error_output = root / "type-error-out"

            def emit_then_fail(*args, **kwargs):
                (type_error_output / "partial.d.ts").write_text(
                    "export declare const partial: true;\n", encoding="utf-8"
                )
                return subprocess.CompletedProcess(
                    args=args[0],
                    returncode=2,
                    stdout="",
                    stderr="index.ts(1,1): error TS2322: not assignable\n",
                )

            with mock.patch.object(
                tsc_check.subprocess, "run", side_effect=emit_then_fail
            ):
                type_error = tsc_check.check_typescript(
                    [source], type_error_output, timeout=3
                )
            self.assertEqual(type_error.status, tsc_check.TscStatus.TYPE_ERROR)
            self.assertEqual(list(type_error_output.iterdir()), [])

    def test_invalid_declaration_output_is_a_tool_error(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "index.ts"
            output_file = root / "not-a-directory"
            source.write_text("export {};\n", encoding="utf-8")
            output_file.write_text("keep\n", encoding="utf-8")

            with mock.patch.object(tsc_check.subprocess, "run") as run_tsc:
                result = tsc_check.check_typescript([source], output_file)

            self.assertEqual(result.status, tsc_check.TscStatus.TOOL_ERROR)
            self.assertIn("TSC_OUTPUT_ERROR", result.output)
            self.assertEqual(output_file.read_text(encoding="utf-8"), "keep\n")
            run_tsc.assert_not_called()

            source_root_result = tsc_check.check_typescript([source], root)
            self.assertEqual(source_root_result.status, tsc_check.TscStatus.TOOL_ERROR)
            self.assertTrue(source.is_file())

    def test_cli_accepts_the_explicit_empty_input_contract(self):
        args = tsc_check.build_parser().parse_args(
            ["check", "--declaration-dir", "declarations"]
        )
        self.assertEqual(args.files, [])

    def test_cli_writes_status_and_maps_exit_codes(self):
        cases = [
            (tsc_check.TscStatus.PASS, 0),
            (tsc_check.TscStatus.TYPE_ERROR, 1),
            (tsc_check.TscStatus.TOOL_ERROR, 2),
        ]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for status, expected_exit in cases:
                with self.subTest(status=status):
                    diagnostics = root / f"{status.value}.txt"
                    status_file = root / f"{status.value}.status"
                    args = argparse.Namespace(
                        files=["index.ts"],
                        declaration_dir=str(root / status.value),
                        diagnostics_file=str(diagnostics),
                        status_file=str(status_file),
                        timeout=7,
                    )
                    result = tsc_check.TscResult(
                        status=status,
                        returncode=expected_exit,
                        output="diagnostic output\n",
                        command=("tsc",),
                    )
                    with mock.patch.object(
                        tsc_check, "check_typescript", return_value=result
                    ):
                        actual_exit = tsc_check.check_command(args)

                    self.assertEqual(actual_exit, expected_exit)
                    self.assertEqual(
                        diagnostics.read_text(encoding="utf-8"),
                        "diagnostic output\n",
                    )
                    self.assertEqual(
                        status_file.read_text(encoding="utf-8"),
                        status.value + "\n",
                    )


if __name__ == "__main__":
    unittest.main()
