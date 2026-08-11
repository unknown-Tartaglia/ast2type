import json
import os
import tempfile
import unittest
from pathlib import Path
from subprocess import run


ROOT = Path(__file__).resolve().parents[2]


class JavaScriptInputIsolationTests(unittest.TestCase):
    def test_bigint_literals_survive_inference_json(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            package = root / "package"
            output = root / "output"
            package.mkdir()
            (package / "index.js").write_text(
                "export const decimal = 0n;\n"
                "export const hex = 0x2_ad_be_efn;\n"
                "export const binary = 0b101n;\n"
                "export const octal = 0o77n;\n",
                encoding="utf-8",
            )

            completed = run(
                [
                    str(ROOT / "make.sh"),
                    str(package),
                    "--js",
                    "--prepare",
                    "--output-dir",
                    str(output),
                ],
                cwd=ROOT,
                capture_output=True,
                text=True,
                timeout=60,
            )

            self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
            graph = json.loads((output / "typegraph.json").read_text(encoding="utf-8"))
            json.loads((output / "typeinfo.json").read_text(encoding="utf-8"))
            rendered = [node.get("fullType") for node in graph["nodes"]]
            self.assertTrue(any('"valueKind": "bigint"' in item for item in rendered if item))

    def test_js_prepare_excludes_typescript_sources_from_ast_input(self):
        with tempfile.TemporaryDirectory() as temporary:
            package = Path(temporary) / "package"
            package.mkdir()
            sources = {
                "index.js": "export function value(input) { return input; }\n",
                "module.mjs": "export const mode = 'esm';\n",
                "index.d.ts": "export function value(input: string): string;\n",
                "implementation.ts": "export const hidden: number = 1;\n",
                "component.tsx": "export const component = <div />;\n",
            }
            for relative_path, source in sources.items():
                (package / relative_path).write_text(source, encoding="utf-8")

            completed = run(
                [str(ROOT / "make.sh"), str(package), "--js", "--prepare"],
                cwd=ROOT,
                capture_output=True,
                text=True,
                timeout=60,
            )

            self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
            self.assertIn("Found 2 source files.", completed.stdout)

            ast_directory = package.parent / "package_output" / "ast"
            ast_sources = {
                ast_file.name.removesuffix(".ast.json").replace("^", "/")
                for ast_file in ast_directory.rglob("*.ast.json")
            }
            self.assertEqual(ast_sources, {"index.js", "module.mjs"})

    def test_custom_work_directory_keeps_real_source_paths(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            package = root / "package"
            work = root / "work"
            package.mkdir()
            source = package / "index.js"
            source.write_text(
                "export function value(input) { return input; }\n",
                encoding="utf-8",
            )

            completed = run(
                [
                    str(ROOT / "make.sh"),
                    str(package),
                    "--js",
                    "--prepare",
                    "--output-dir",
                    str(work),
                ],
                cwd=ROOT,
                capture_output=True,
                text=True,
                timeout=60,
            )

            self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
            graph = json.loads((work / "typegraph.json").read_text(encoding="utf-8"))
            files = {
                node["file"]
                for node in graph["nodes"]
                if node.get("file") != "unknown_file"
            }
            self.assertEqual(files, {str(source)})
            self.assertTrue((work / "ast" / "index.js.ast.json").is_file())
            self.assertFalse((root / "package_output").exists())

            environment = os.environ.copy()
            for name in (
                "AGENT_API_KEY",
                "DEEPSEEK_API_KEY",
                "OPENAI_API_KEY",
            ):
                environment.pop(name, None)
            agent_work = root / "agent-work"
            completed = run(
                [
                    str(ROOT / "make.sh"),
                    str(package),
                    "--js",
                    "--prepare",
                    "--output-dir",
                    str(agent_work),
                    "--agent",
                    "--agent-provider",
                    "openai",
                ],
                cwd=ROOT,
                capture_output=True,
                text=True,
                timeout=60,
                env=environment,
            )
            self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
            candidates = json.loads(
                (agent_work / "agent-candidates.json").read_text(encoding="utf-8")
            )["candidates"]
            self.assertTrue(candidates)
            self.assertEqual({item["file"] for item in candidates}, {str(source)})


if __name__ == "__main__":
    unittest.main()
