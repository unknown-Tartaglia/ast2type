import subprocess
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

from generate import pipeline_ts


class TypeRenderingTests(unittest.TestCase):
    def test_unknown_and_anonymous_objects_degrade_to_any(self):
        self.assertEqual(pipeline_ts._full_type_to_ts("unknown"), "any")
        self.assertEqual(
            pipeline_ts._full_type_to_ts({"kind": "primitive", "name": "unknown"}),
            "any",
        )
        self.assertEqual(
            pipeline_ts._full_type_to_ts({"kind": "object", "name": "obj_123"}),
            "any",
        )

    def test_nested_function_type_is_rendered_as_typescript(self):
        full_type = {
            "kind": "function",
            "params": [
                {
                    "name": "values",
                    "type": {
                        "kind": "array",
                        "elementType": {"kind": "primitive", "name": "number"},
                    },
                },
            ],
            "returnType": {"kind": "primitive", "name": "boolean"},
        }

        self.assertEqual(
            pipeline_ts._full_type_to_ts(full_type),
            "(values: number[]) => boolean",
        )

    def test_invalid_named_types_degrade_to_any(self):
        self.assertEqual(
            pipeline_ts._full_type_to_ts("new (value: string): Item"),
            "any",
        )
        self.assertEqual(pipeline_ts._full_type_to_ts("object:"), "any")

    def test_structural_object_type_is_rendered(self):
        full_type = {
            "kind": "object",
            "name": "",
            "properties": {
                "open": {"kind": "primitive", "name": "string"},
                "close-value": {"kind": "primitive", "name": "boolean"},
            },
        }

        self.assertEqual(
            pipeline_ts._full_type_to_ts(full_type),
            '{ open: string; "close-value": boolean }',
        )


class PackageDiscoveryTests(unittest.TestCase):
    def test_discovers_js_and_mjs_packages(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            js_package = root / "js-package"
            mjs_package = root / "mjs-package"
            ignored = root / "results"
            for directory in (js_package, mjs_package, ignored):
                directory.mkdir()
            (js_package / "index.js").write_text("export default 1;\n", encoding="utf-8")
            (mjs_package / "index.mjs").write_text("export default 2;\n", encoding="utf-8")
            (ignored / "index.js").write_text("export default 3;\n", encoding="utf-8")

            packages = pipeline_ts.discover_packages(root)

        self.assertEqual(packages, ["js-package", "mjs-package"])

    def test_existing_output_check_maps_both_extensions_to_ts(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            output = root / "output"
            source.mkdir()
            output.mkdir()
            (source / "index.js").write_text("export default 1;\n", encoding="utf-8")
            (source / "config.mjs").write_text("export default {};\n", encoding="utf-8")
            (output / "index.ts").write_text("export default 1;\n", encoding="utf-8")

            self.assertFalse(pipeline_ts._check_all_ts_exist(source, output))
            (output / "config.ts").write_text("export default {};\n", encoding="utf-8")
            self.assertTrue(pipeline_ts._check_all_ts_exist(source, output))


class PipelineExecutionTests(unittest.TestCase):
    def test_run_pipeline_removes_stale_artifacts_and_honors_timeout(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            package = root / "package"
            package.mkdir()
            package_output = Path(f"{package}_output")
            package_output.mkdir()
            (package_output / "stale.ast.json").write_text("{}", encoding="utf-8")
            shared_output = root / "output"
            shared_output.mkdir()
            stale_typegraph = shared_output / "typegraph.json"
            stale_typegraph.write_text("{}", encoding="utf-8")

            with (
                mock.patch.object(pipeline_ts, "OUT_DIR", str(shared_output)),
                mock.patch.object(
                    pipeline_ts.subprocess,
                    "run",
                    return_value=SimpleNamespace(returncode=0),
                ) as run_command,
            ):
                pipeline_ts.run_pipeline(str(package), timeout=37)

            self.assertFalse(package_output.exists())
            self.assertFalse(stale_typegraph.exists())
            self.assertEqual(run_command.call_args.kwargs["timeout"], 37)
            self.assertEqual(
                run_command.call_args.args[0][-3:],
                ["--js", "--prepare", "--agent"],
            )

    def test_package_without_named_functions_is_still_migrated(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            output = root / "output"
            source.mkdir()
            (source / "config.mjs").write_text(
                "const config = { enabled: true };\nexport default config;\n",
                encoding="utf-8",
            )

            with (
                mock.patch.object(pipeline_ts, "run_pipeline") as run_pipeline,
                mock.patch.object(
                    pipeline_ts,
                    "_load_typegraph",
                    return_value={"nodes": []},
                ),
            ):
                result = pipeline_ts.generate_ts_for_pkg(
                    str(source),
                    "sample",
                    str(output),
                    cleanup=False,
                    skip_existing=False,
                    timeout=23,
                )

            migrated = output / "sample" / "config.ts"
            self.assertEqual(result, ("ok", 1, []))
            self.assertEqual(
                migrated.read_text(encoding="utf-8"),
                "const config = { enabled: true };\nexport default config;\n",
            )
            run_pipeline.assert_called_once_with(str(source), timeout=23)

    def test_nonzero_inference_command_is_a_pipeline_failure(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            package = root / "package"
            package.mkdir()
            shared_output = root / "output"
            shared_output.mkdir()

            with (
                mock.patch.object(pipeline_ts, "OUT_DIR", str(shared_output)),
                mock.patch.object(
                    pipeline_ts.subprocess,
                    "run",
                    return_value=SimpleNamespace(returncode=7),
                ),
            ):
                with self.assertRaisesRegex(RuntimeError, "status 7"):
                    pipeline_ts.run_pipeline(str(package), timeout=12)

    def test_regeneration_removes_stale_target_files(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            output = root / "output"
            package_output = output / "sample"
            source.mkdir()
            package_output.mkdir(parents=True)
            (source / "index.js").write_text("export default 1;\n", encoding="utf-8")
            stale = package_output / "removed.ts"
            stale.write_text("export default 0;\n", encoding="utf-8")

            with (
                mock.patch.object(pipeline_ts, "run_pipeline"),
                mock.patch.object(
                    pipeline_ts,
                    "_load_typegraph",
                    return_value={"nodes": []},
                ),
            ):
                result = pipeline_ts.generate_ts_for_pkg(
                    str(source),
                    "sample",
                    str(output),
                    cleanup=False,
                    skip_existing=False,
                )

            self.assertEqual(result, ("ok", 1, []))
            self.assertFalse(stale.exists())
            self.assertTrue((package_output / "index.ts").is_file())

    def test_pipeline_failure_does_not_load_a_stale_typegraph(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            source.mkdir()
            (source / "index.js").write_text("export default 1;\n", encoding="utf-8")

            with (
                mock.patch.object(
                    pipeline_ts,
                    "run_pipeline",
                    side_effect=RuntimeError("inference failed"),
                ),
                mock.patch.object(pipeline_ts, "_load_typegraph") as load_typegraph,
            ):
                result = pipeline_ts.generate_ts_for_pkg(
                    str(source),
                    "sample",
                    str(root / "output"),
                    cleanup=False,
                    skip_existing=False,
                )

        self.assertEqual(result, ("failed", 0, ["inference failed"]))
        load_typegraph.assert_not_called()

    def test_pipeline_timeout_is_reported_for_the_current_package(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            source.mkdir()
            (source / "index.js").write_text("export default 1;\n", encoding="utf-8")

            with mock.patch.object(
                pipeline_ts,
                "run_pipeline",
                side_effect=subprocess.TimeoutExpired("make.sh", 11),
            ):
                result = pipeline_ts.generate_ts_for_pkg(
                    str(source),
                    "sample",
                    str(root / "output"),
                    cleanup=False,
                    skip_existing=False,
                    timeout=11,
                )

        self.assertEqual(result, ("failed", 0, ["pipeline timed out after 11s"]))


class NodeGlobalTests(unittest.TestCase):
    def test_imported_node_global_is_not_redeclared(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "screenshot.ts"
            original = "import process from 'node:process';\nconsole.log(process.pid);\n"
            path.write_text(original, encoding="utf-8")

            fixed = pipeline_ts._inject_node_globals([path])

            self.assertEqual(fixed, 0)
            self.assertEqual(path.read_text(encoding="utf-8"), original)

    def test_declarations_follow_shebang_and_use_strict(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "cli.ts"
            path.write_text(
                "#!/usr/bin/env node\n\n"
                '"use strict";\n\n'
                "console.log(process.pid, __dirname, require('config'));\n",
                encoding="utf-8",
            )

            fixed = pipeline_ts._inject_node_globals([path])
            content = path.read_text(encoding="utf-8")

        self.assertEqual(fixed, 1)
        self.assertLess(content.index('"use strict"'), content.index("declare var process"))
        self.assertLess(content.index("declare var process"), content.index("console.log"))
        self.assertIn("declare var __dirname: string;", content)
        self.assertIn("declare function require(name: string): any;", content)


if __name__ == "__main__":
    unittest.main()
