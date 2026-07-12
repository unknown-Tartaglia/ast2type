import tempfile
import unittest
from pathlib import Path
from unittest import mock

from generate import weave


class WeaveExportSelectionTests(unittest.TestCase):
    def test_prefers_esm_export_over_private_namesake(self):
        exports = [
            {"name": "target", "kind": "function", "inferred": "(value: string) => string"}
        ]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            private_path = root / "a-private.js"
            exported_path = root / "b-exported.js"
            private_path.write_text(
                "function target(value) { return value; }\n", encoding="utf-8"
            )
            exported_path.write_text(
                "export function target(value) { return value; }\n", encoding="utf-8"
            )
            walk_result = [(str(root), [], [private_path.name, exported_path.name])]
            with mock.patch.object(weave.os, "walk", return_value=walk_result):
                result = weave.weave_package(root, exports)

        self.assertNotIn("value: string", result[private_path.name])
        self.assertRegex(
            result[exported_path.name],
            r"target\(value: string\)\s*:\s*string",
        )

    def test_prefers_commonjs_export_over_private_namesake(self):
        exports = [
            {"name": "target", "kind": "function", "inferred": "(value: string) => string"}
        ]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            private_path = root / "a-private.js"
            exported_path = root / "b-exported.js"
            private_path.write_text(
                "function target(value) { return value; }\n", encoding="utf-8"
            )
            exported_path.write_text(
                "module.exports = target;\n"
                "function target(value) { return value; }\n",
                encoding="utf-8",
            )

            result = weave.weave_package(root, exports)

        self.assertNotIn("value: string", result[private_path.name])
        self.assertRegex(
            result[exported_path.name],
            r"target\(value: string\)\s*:\s*string",
        )

    def test_selects_export_target_independently_per_symbol(self):
        exports = [
            {"name": "alpha", "kind": "function", "inferred": "(value: string) => string"},
            {"name": "beta", "kind": "function", "inferred": "(value: number) => number"},
        ]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            alpha_path = root / "alpha.js"
            beta_path = root / "beta.js"
            alpha_path.write_text(
                "export function alpha(value) { return value; }\n"
                "function beta(value) { return value; }\n",
                encoding="utf-8",
            )
            beta_path.write_text(
                "export function beta(value) { return value; }\n",
                encoding="utf-8",
            )

            result = weave.weave_package(root, exports)

        self.assertRegex(
            result[alpha_path.name],
            r"alpha\(value: string\)\s*:\s*string",
        )
        self.assertNotIn("beta(value: number)", result[alpha_path.name])
        self.assertRegex(
            result[beta_path.name],
            r"beta\(value: number\)\s*:\s*number",
        )

    def test_does_not_weave_an_internal_function(self):
        exports = [
            {"name": "helper", "kind": "function", "inferred": "(value: string) => string"}
        ]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            path = root / "index.js"
            path.write_text(
                "function helper(value) { return value; }\nexport default 1;\n",
                encoding="utf-8",
            )

            result = weave.weave_package(root, exports)

        self.assertNotIn("value: string", result[path.name])

    def test_weaves_property_of_an_exported_function(self):
        exports = [
            {"name": "range", "kind": "function", "inferred": "(value: number) => number"}
        ]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            path = root / "index.js"
            path.write_text(
                "function main() {}\n"
                "function range(value) { return value; }\n"
                "main.range = range;\n"
                "module.exports = main;\n",
                encoding="utf-8",
            )

            result = weave.weave_package(root, exports)

        self.assertRegex(
            result[path.name],
            r"range\(value: number\)\s*:\s*number",
        )


if __name__ == "__main__":
    unittest.main()
