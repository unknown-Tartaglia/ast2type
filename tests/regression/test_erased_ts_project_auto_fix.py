import tempfile
import unittest
from pathlib import Path

from generate import run_erased_ts_project_auto_fix


ROOT = Path(__file__).resolve().parents[2]
TSC = ROOT / "node_modules/.bin/tsc"


@unittest.skipUnless(TSC.is_file(), "repository TypeScript compiler is unavailable")
class ErasedProjectAutoFixTests(unittest.TestCase):
    def test_fixes_with_the_groundtruth_projects_compiler_and_config(self):
        with tempfile.TemporaryDirectory() as temporary:
            experiment = Path(temporary)
            groundtruth = experiment / "groundtruth/sample"
            raw = experiment / "raw/sample"
            compiler = groundtruth / "node_modules/.bin/tsc"
            compiler.parent.mkdir(parents=True)
            compiler.symlink_to(TSC.resolve())
            raw.mkdir(parents=True)
            config = {
                "compilerOptions": {"strict": True, "target": "ES2020"},
                "include": ["*.ts"],
            }
            import json

            (groundtruth / "tsconfig.json").write_text(
                json.dumps(config), encoding="utf-8"
            )
            (raw / "tsconfig.json").write_text(
                json.dumps(config), encoding="utf-8"
            )
            (raw / "index.ts").write_text(
                'export const value: number = "wrong";\n', encoding="utf-8"
            )

            exit_code = run_erased_ts_project_auto_fix.main([
                "--experiment-root",
                str(experiment),
                "--packages",
                "sample",
            ])

            fixed = experiment / "fixed-project/sample/index.ts"
            self.assertEqual(exit_code, 0)
            self.assertEqual(
                fixed.read_text(encoding="utf-8"),
                'export const value: any = "wrong";\n',
            )
            self.assertFalse((fixed.parent / "node_modules").exists())


if __name__ == "__main__":
    unittest.main()
