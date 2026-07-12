import tempfile
import unittest
from pathlib import Path
from subprocess import run


ROOT = Path(__file__).resolve().parents[2]


class JavaScriptInputIsolationTests(unittest.TestCase):
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


if __name__ == "__main__":
    unittest.main()
