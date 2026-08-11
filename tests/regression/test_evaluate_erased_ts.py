import tempfile
import unittest
from pathlib import Path

from generate import ts_project_env


class ProjectEnvironmentTests(unittest.TestCase):
    def test_links_root_and_workspace_dependencies_then_cleans_them(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            dependencies = root / "dependencies"
            migrated = root / "migrated"
            for relative in (Path("node_modules"), Path("packages/compiler/node_modules")):
                (dependencies / relative).mkdir(parents=True)
                (migrated / relative.parent).mkdir(parents=True, exist_ok=True)
            compiler = dependencies / "node_modules/.bin/tsc"
            compiler.parent.mkdir(parents=True)
            compiler.write_text("", encoding="utf-8")

            with ts_project_env.project_compile_environment(
                "vue", migrated, dependencies
            ) as profile:
                self.assertEqual(profile.config, migrated / "tsconfig.json")
                self.assertEqual(profile.environment, "installed")
                self.assertTrue((migrated / "node_modules").is_symlink())
                self.assertTrue(
                    (migrated / "packages/compiler/node_modules").is_symlink()
                )

            self.assertFalse((migrated / "node_modules").exists())
            self.assertFalse((migrated / "packages/compiler/node_modules").exists())

    def test_personal_shim_and_config_are_temporary(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            dependencies = root / "dependencies"
            migrated = root / "personal"
            dependencies.mkdir()
            migrated.mkdir()

            with ts_project_env.project_compile_environment(
                "personal", migrated, dependencies
            ) as profile:
                shim = migrated / "ast2type-evaluation-env.d.ts"
                self.assertEqual(
                    profile.environment, "shimmed-private-dependencies"
                )
                self.assertTrue(profile.config.is_file())
                self.assertIn('declare module "*"', shim.read_text(encoding="utf-8"))

            self.assertFalse(profile.config.exists())
            self.assertFalse(shim.exists())

    def test_partial_workspace_setup_is_cleaned_after_conflict(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            dependencies = root / "dependencies"
            migrated = root / "migrated"
            (dependencies / "node_modules").mkdir(parents=True)
            (dependencies / "packages/compiler/node_modules").mkdir(parents=True)
            (migrated / "packages/compiler/node_modules").mkdir(parents=True)

            with self.assertRaisesRegex(RuntimeError, "unrelated dependency tree"):
                with ts_project_env.project_compile_environment(
                    "vue", migrated, dependencies
                ):
                    self.fail("conflicting workspace should not be evaluated")

            self.assertFalse((migrated / "node_modules").exists())
            self.assertTrue((migrated / "packages/compiler/node_modules").is_dir())


if __name__ == "__main__":
    unittest.main()
