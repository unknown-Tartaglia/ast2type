"""Project-local TypeScript compiler environments for migrated TS evaluation."""

from __future__ import annotations

import json
import os
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path

from generate.tsc_check import compiler_path


PROJECT_EXTRA_ARGS = {
    "skills": ("--types", "node,bun"),
}
PERSONAL_TSCONFIG = {
    "extends": "./tsconfig.json",
    "compilerOptions": {
        "jsx": "preserve",
        "noEmit": True,
        "skipLibCheck": True,
    },
    "include": ["**/*.ts", "**/*.tsx", "**/*.d.ts"],
    "exclude": ["eslint.config.mts", "node_modules"],
}
PERSONAL_SHIM = """\
// The dataset contains only one subproject of a private monorepo. Missing
// external and parent-repository modules are environment inputs, not inferred
// declarations, so expose them as unknown runtime modules for this evaluation.
declare module "*";
declare namespace JSX {
  type Element = any;
  interface IntrinsicElements { [name: string]: any; }
}
"""


@dataclass(frozen=True)
class ProjectCompileProfile:
    compiler: Path
    config: Path
    extra_args: tuple[str, ...]
    environment: str


@contextmanager
def project_compile_environment(
    project: str,
    directory: Path,
    dependency_project: Path,
):
    """Expose the dependency project's exact compiler environment temporarily."""
    directory = directory.resolve()
    dependency_project = dependency_project.resolve()
    linked_modules: list[Path] = []
    temporary_files: list[Path] = []
    try:
        # pnpm workspaces create package-local node_modules trees. Mirroring only
        # the root would make migrated copies resolve fewer packages than GT.
        for current, directories, _ in os.walk(dependency_project):
            if "node_modules" not in directories:
                continue
            directories.remove("node_modules")
            dependency_modules = Path(current) / "node_modules"
            relative_parent = Path(current).relative_to(dependency_project)
            target_modules = directory / relative_parent / "node_modules"
            if not target_modules.exists():
                target_modules.symlink_to(
                    dependency_modules, target_is_directory=True
                )
                linked_modules.append(target_modules)
            elif target_modules.resolve() != dependency_modules.resolve():
                raise RuntimeError(
                    f"refusing to replace unrelated dependency tree: {target_modules}"
                )

        config = directory / "tsconfig.json"
        environment = "installed"
        project_compiler = dependency_project / "node_modules" / ".bin" / "tsc"
        if project == "personal":
            environment = "shimmed-private-dependencies"
            project_compiler = compiler_path()
            shim = directory / "ast2type-evaluation-env.d.ts"
            config = directory / ".ast2type-evaluation-tsconfig.json"
            shim.write_text(PERSONAL_SHIM, encoding="utf-8")
            temporary_files.append(shim)
            config.write_text(
                json.dumps(PERSONAL_TSCONFIG, indent=2), encoding="utf-8"
            )
            temporary_files.append(config)
        elif not project_compiler.is_file():
            raise FileNotFoundError(
                f"project compiler is not installed: {project_compiler}"
            )

        yield ProjectCompileProfile(
            compiler=project_compiler,
            config=config,
            extra_args=PROJECT_EXTRA_ARGS.get(project, ()),
            environment=environment,
        )
    finally:
        for path in temporary_files:
            path.unlink(missing_ok=True)
        for target_modules in reversed(linked_modules):
            target_modules.unlink()
