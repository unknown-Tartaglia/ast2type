# Regression tests

Run the tracked regression suite from the repository root:

```bash
npm test
```

The equivalent explicit command is:

```bash
npm run test:regression
```

The suite currently covers:

- fair and ground-truth Agent candidate selection;
- arrow-function inference and return-slot feedback;
- conservative ground-truth type parsing;
- JavaScript-only AST input isolation;
- inferred type sanitization and annotation weaving;
- ESM and CommonJS export-target selection;
- raw JavaScript-to-TypeScript pipeline conversion and failure isolation;
- TypeScript annotation erasure, graph-based restoration, and inference reuse isolation;
- shared TypeScript compilation inputs, statuses, and declaration-emission rules.

Tests use temporary project directories and do not require generated experiment
outputs. Known limitations of name-based export selection are documented in
`docs/weave-known-limitations.md`.

The erased-TypeScript inference tree intentionally contains only TS-family
sources. Non-TypeScript project files are retained in the final raw project but
are not inference inputs; reuse validation therefore compares TS-family sources.
