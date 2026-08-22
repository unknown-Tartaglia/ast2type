import json
import subprocess
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


class BasicTypeInferenceTests(unittest.TestCase):
    def test_intrinsic_calls_and_mutable_assignments_infer_primitives(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            output = root / "output"
            source.mkdir()
            (source / "index.js").write_text(
                "function normalize(value) { return value.toLowerCase().trim(); }\n"
                "function matches(value) { const pattern = /x/; return pattern.test(value); }\n"
                "function coerce(value) { return String(value).replace('x', 'y'); }\n"
                "function defaultFlag(flag) { if (flag === undefined) flag = true; return flag; }\n"
                "function checked(value) { if (typeof value !== 'string') throw new TypeError(); return value; }\n"
                "function checkedNumber(value) { if (typeof value !== 'number' || value < 0) throw new TypeError(); return value; }\n"
                "function checkedOptions(value, {strict = true} = {}) { if (typeof value !== 'string') throw new TypeError(); return value; }\n"
                "function fallback(value) { if (typeof value !== 'string') return ''; return value; }\n",
                encoding="utf-8",
            )
            completed = subprocess.run(
                [
                    "node", "-r", "ts-node/register", "src/cli.ts", "migrate-js",
                    str(source), "--out", str(root / "migrated"),
                    "--work-dir", str(output), "--mode", "std", "--keep-work-dir",
                ],
                cwd=ROOT,
                capture_output=True,
                text=True,
                timeout=30,
            )
            self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)

            graph = json.loads((output / "typegraph.json").read_text(encoding="utf-8"))
            functions = {}
            for node in graph["nodes"]:
                full_type = json.loads(node["fullType"]) if node.get("fullType") else None
                if full_type and full_type.get("kind") == "function" and node["id"] == full_type.get("id"):
                    functions[full_type["name"]] = full_type

            primitive = lambda name: {"kind": "primitive", "name": name}
            self.assertEqual(functions["normalize"]["params"][0]["type"], primitive("string"))
            self.assertEqual(functions["normalize"]["returnType"], primitive("string"))
            self.assertEqual(functions["matches"]["returnType"], primitive("boolean"))
            self.assertEqual(functions["coerce"]["returnType"], primitive("string"))
            self.assertEqual(functions["defaultFlag"]["params"][0]["type"], primitive("boolean"))
            self.assertEqual(functions["defaultFlag"]["returnType"], primitive("boolean"))
            self.assertEqual(functions["checked"]["params"][0]["type"], primitive("string"))
            self.assertEqual(functions["checked"]["returnType"], primitive("string"))
            self.assertEqual(functions["checkedNumber"]["params"][0]["type"], primitive("number"))
            self.assertEqual(functions["checkedNumber"]["returnType"], primitive("number"))
            self.assertEqual(functions["checkedOptions"]["params"][0]["type"], primitive("string"))
            self.assertEqual(functions["checkedOptions"]["returnType"], primitive("string"))
            self.assertEqual(functions["fallback"]["params"][0]["type"], primitive("unknown"))

    def test_shadowed_intrinsics_are_not_treated_as_globals(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            source.mkdir()
            (source / "index.js").write_text(
                "function shadowed(String) { return String(1); }\n",
                encoding="utf-8",
            )
            completed = subprocess.run(
                [
                    "node", "-r", "ts-node/register", "src/cli.ts", "migrate-js",
                    str(source), "--out", str(root / "migrated"),
                    "--work-dir", str(root / "output"), "--mode", "std", "--keep-work-dir",
                ],
                cwd=ROOT,
                capture_output=True,
                text=True,
                timeout=30,
            )
            self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
            graph = json.loads((root / "output" / "typegraph.json").read_text(encoding="utf-8"))
            shadowed = next(
                json.loads(node["fullType"])
                for node in graph["nodes"]
                if node.get("fullType")
                and json.loads(node["fullType"]).get("kind") == "function"
                and json.loads(node["fullType"]).get("name") == "shadowed"
            )
            self.assertNotEqual(shadowed["returnType"], {"kind": "primitive", "name": "number"})

    def test_string_literal_values_do_not_include_source_quotes(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            source.mkdir()
            (source / "index.js").write_text(
                "function marker() { return '@'; }\n",
                encoding="utf-8",
            )
            completed = subprocess.run(
                [
                    "node", "-r", "ts-node/register", "src/cli.ts", "migrate-js",
                    str(source), "--out", str(root / "migrated"),
                    "--work-dir", str(root / "output"), "--mode", "std", "--keep-work-dir",
                ],
                cwd=ROOT,
                capture_output=True,
                text=True,
                timeout=30,
            )
            self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
            graph = json.loads((root / "output" / "typegraph.json").read_text(encoding="utf-8"))
            marker_literal = next(
                json.loads(node["fullType"])
                for node in graph["nodes"]
                if node.get("text") == "'@'" and node.get("fullType")
            )
            self.assertEqual(marker_literal, {"kind": "literal", "value": "@"})


if __name__ == "__main__":
    unittest.main()
