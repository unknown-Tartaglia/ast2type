import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


class MigrationCoreTests(unittest.TestCase):
    def run_node(self, script, env=None):
        completed = subprocess.run(
            ["node", "-r", "ts-node/register", "-e", script],
            cwd=ROOT,
            env={**os.environ, **(env or {})},
            capture_output=True,
            text=True,
            timeout=30,
        )
        self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
        return json.loads(completed.stdout)

    def test_source_discovery_and_utf16_edits_preserve_crlf(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "index.ts"
            source.write_text('const emoji = "😀"; const value: string = "x";\r\n', encoding="utf-8", newline="")
            (root / "types.d.ts").write_text("export {};\n", encoding="utf-8")
            (root / "node_modules").mkdir()
            (root / "node_modules" / "ignored.ts").write_text("export {};\n", encoding="utf-8")
            result = self.run_node(
                """
                const fs = require('fs');
                const { applyTextEdits, discoverTypeScriptFiles } = require('./src/migration/files');
                const root = process.env.TEST_ROOT;
                const file = require('path').join(root, 'index.ts');
                const source = fs.readFileSync(file, 'utf8');
                const before = 'value: string';
                const start = source.indexOf(before);
                const applied = applyTextEdits(root, [{ file, start, end: start + before.length, text: 'value: any' }]);
                console.log(JSON.stringify({ files: discoverTypeScriptFiles(root), applied, source: fs.readFileSync(file, 'utf8') }));
                """,
                {"TEST_ROOT": str(root)},
            )
            self.assertEqual(result["files"], [str(source.resolve())])
            self.assertEqual(result["applied"]["edits"], 1)
            self.assertIn("value: any", result["source"])
            self.assertEqual(result["source"].count("\r\n"), 1)

    def test_compiler_returns_structured_diagnostics_and_emits_only_on_success(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            valid = root / "valid.ts"
            invalid = root / "invalid.ts"
            declarations = root / "declarations"
            valid.write_text("export const value: string = 'ok';\n", encoding="utf-8")
            invalid.write_text("export const value: string = 1;\n", encoding="utf-8")
            result = self.run_node(
                """
                const { checkFiles } = require('./src/migration/compiler');
                const path = require('path');
                const root = process.env.TEST_ROOT;
                const out = path.join(root, 'declarations');
                const valid = checkFiles({ files: [path.join(root, 'valid.ts')], declarationDir: out });
                const invalid = checkFiles({ files: [path.join(root, 'invalid.ts')], declarationDir: out });
                console.log(JSON.stringify({ valid, invalid }));
                """,
                {"TEST_ROOT": str(root)},
            )
            self.assertEqual(result["valid"]["status"], "pass")
            self.assertEqual(len(result["valid"]["emittedFiles"]), 1)
            self.assertEqual(result["invalid"]["status"], "type-error")
            self.assertIn(2322, [item["code"] for item in result["invalid"]["diagnostics"]])
            self.assertEqual(list(declarations.glob("*.d.ts")), [])

    def test_source_editor_rejects_escape_and_overlapping_edits(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "index.ts"
            source.write_text("const value = 1;\n", encoding="utf-8")
            result = self.run_node(
                """
                const { applyTextEdits } = require('./src/migration/files');
                const path = require('path');
                const root = process.env.TEST_ROOT;
                const errors = [];
                for (const edits of [
                  [{ file: '../outside.ts', start: 0, end: 0, text: '' }],
                  [
                    { file: 'index.ts', start: 0, end: 5, text: 'let' },
                    { file: 'index.ts', start: 4, end: 8, text: 'x' },
                  ],
                ]) {
                  try { applyTextEdits(root, edits); } catch (error) { errors.push(error.message); }
                }
                console.log(JSON.stringify(errors));
                """,
                {"TEST_ROOT": str(root)},
            )
            self.assertEqual(len(result), 2)
            self.assertIn("escapes root", result[0])
            self.assertIn("overlapping edits", result[1])

    def test_migration_rejects_source_output_and_work_directory_overlap(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            source.mkdir()
            (source / "index.js").write_text("module.exports = 1;\n", encoding="utf-8")
            result = self.run_node(
                """
                const { inferJavaScript } = require('./src/inference/runner');
                const { migrateJavaScriptProject } = require('./src/migration/project');
                const source = process.env.TEST_SOURCE;
                const errors = [];
                for (const operation of [
                  () => inferJavaScript({ source, output: source }),
                  () => migrateJavaScriptProject({
                    source,
                    output: process.env.TEST_OUTPUT,
                    workDirectory: source,
                  }),
                ]) {
                  try { operation(); } catch (error) { errors.push(error.message); }
                }
                console.log(JSON.stringify(errors));
                """,
                {
                    "TEST_SOURCE": str(source),
                    "TEST_OUTPUT": str(root / "output"),
                },
            )
            self.assertEqual(len(result), 2)
            self.assertTrue(all("overlap" in message for message in result))
            self.assertTrue((source / "index.js").is_file())

    def test_project_compiler_uses_the_projects_tsconfig(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "tsconfig.json").write_text(
                json.dumps({
                    "compilerOptions": {"strict": True, "target": "ES2021"},
                    "include": ["src/**/*.ts"],
                }),
                encoding="utf-8",
            )
            source = root / "src" / "index.ts"
            source.parent.mkdir()
            source.write_text("export function value(input) { return input; }\n", encoding="utf-8")
            result = self.run_node(
                """
                const { checkProject } = require('./src/migration/compiler');
                console.log(JSON.stringify(checkProject({ root: process.env.TEST_ROOT })));
                """,
                {"TEST_ROOT": str(root)},
            )
            self.assertEqual(result["status"], "type-error")
            self.assertIn(7006, [item["code"] for item in result["diagnostics"]])

    def test_project_compiler_prefers_the_locally_installed_typescript(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            local = root / "node_modules" / "typescript"
            local.mkdir(parents=True)
            (local / "package.json").write_text(
                json.dumps({"name": "typescript", "main": "index.js"}), encoding="utf-8"
            )
            (local / "index.js").write_text(
                "const compiler = require(process.env.ROOT_TYPESCRIPT);\n"
                "module.exports = { ...compiler, version: 'fixture-local' };\n",
                encoding="utf-8",
            )
            (root / "tsconfig.json").write_text(
                json.dumps({"compilerOptions": {"strict": True}, "files": ["index.ts"]}),
                encoding="utf-8",
            )
            (root / "index.ts").write_text("export const value = 1;\n", encoding="utf-8")
            result = self.run_node(
                """
                const { checkProject } = require('./src/migration/compiler');
                console.log(JSON.stringify(checkProject({ root: process.env.TEST_ROOT })));
                """,
                {
                    "TEST_ROOT": str(root),
                    "ROOT_TYPESCRIPT": str(ROOT / "node_modules" / "typescript"),
                },
            )
            self.assertEqual(result["status"], "pass")
            self.assertEqual(result["compilerVersion"], "fixture-local")

    def test_typegraph_renderer_and_ast_weaver_use_canonical_positions(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "index.js"
            source.write_text(
                "const map = value => String(value);\n"
                "async function load(input) { return input.length; }\n",
                encoding="utf-8",
            )
            result = self.run_node(
                """
                const fs = require('fs');
                const path = require('path');
                const ts = require('typescript');
                const { weaveJavaScript } = require('./src/migration/js');
                const { renderType } = require('./src/migration/typegraph');
                const root = process.env.TEST_ROOT;
                const file = path.join(root, 'index.js');
                const text = fs.readFileSync(file, 'utf8');
                const source = ts.createSourceFile(file, text, ts.ScriptTarget.Latest, true, ts.ScriptKind.JS);
                const functions = [];
                const visit = node => {
                  if ((ts.isArrowFunction(node) || ts.isFunctionDeclaration(node)) && node.body) functions.push(node);
                  ts.forEachChild(node, visit);
                };
                visit(source);
                const position = node => {
                  const value = source.getLineAndCharacterOfPosition(node.getStart(source));
                  return { start: { line: value.line + 1, character: value.character + 1 } };
                };
                const graph = { nodes: [
                  {
                    id: 1, file, position: position(functions[0]),
                    fullType: JSON.stringify({ id: 1, kind: 'function', name: 'map', params: [{ name: 'value', type: { kind: 'primitive', name: 'number' } }], returnType: { kind: 'primitive', name: 'string' } }),
                  },
                  {
                    id: 2, file, position: position(functions[1]),
                    fullType: JSON.stringify({ id: 2, kind: 'function', name: 'load', params: [{ name: 'input', type: { kind: 'primitive', name: 'string' } }], returnType: { kind: 'primitive', name: 'number' } }),
                  },
                  {
                    id: 3, file, position: position(functions[1]),
                    fullType: JSON.stringify({ id: 99, kind: 'function', name: 'ignored', params: [], returnType: 'void' }),
                  },
                ] };
                const woven = weaveJavaScript(root, graph);
                console.log(JSON.stringify({
                  content: woven.files.get('index.js'),
                  report: woven.report,
                  object: renderType({ kind: 'object', properties: { name: { kind: 'primitive', name: 'string' } } }),
                  array: renderType({ kind: 'array', elementType: { kind: 'union', types: ['string', 'number'] } }),
                }));
                """,
                {"TEST_ROOT": str(root)},
            )
            self.assertIn("(value: number)", result["content"])
            self.assertIn(": string =>", result["content"])
            self.assertIn("load(input: string)", result["content"])
            self.assertIn("Promise<number>", result["content"])
            self.assertEqual(result["report"]["canonicalTargets"], 2)
            self.assertEqual(result["report"]["ignoredNoncanonical"], 1)
            self.assertEqual(result["object"], "{ name: string }")
            self.assertEqual(result["array"], "(string | number)[]")

    def test_javascript_migration_normalizes_compatibility_constructs(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "index.js"
            source.write_text(
                '"use strict";\n'
                "class Item { constructor() { this.value = 1; } }\n"
                'export default Item["default"] = Item.current = Item;\n'
                "module.exports = Item;\n",
                encoding="utf-8",
            )
            result = self.run_node(
                """
                const { weaveJavaScript } = require('./src/migration/js');
                const woven = weaveJavaScript(process.env.TEST_ROOT, { nodes: [] });
                console.log(JSON.stringify({ content: woven.files.get('index.js'), report: woven.report }));
                """,
                {"TEST_ROOT": str(root)},
            )
            self.assertIn("value: any;", result["content"])
            self.assertIn('Item["default"] = Item.current = Item;', result["content"])
            self.assertIn("export default Item;", result["content"])
            self.assertIn("declare var module", result["content"])
            self.assertEqual(result["report"]["compatibilityNormalizedFiles"], 1)
            self.assertEqual(result["report"]["nodeGlobalDeclarationFiles"], 1)

    def test_javascript_migration_does_not_redeclare_private_fields(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "index.js").write_text(
                "export default class Queue {\n"
                "  #head;\n"
                "  reset() { this.#head = undefined; }\n"
                "}\n",
                encoding="utf-8",
            )
            result = self.run_node(
                """
                const { weaveJavaScript } = require('./src/migration/js');
                const woven = weaveJavaScript(process.env.TEST_ROOT, { nodes: [] });
                console.log(JSON.stringify({ content: woven.files.get('index.js') }));
                """,
                {"TEST_ROOT": str(root)},
            )
            self.assertEqual(result["content"].count("#head;"), 1)
            self.assertNotIn("#head: any", result["content"])

    def test_typescript_erasure_and_restoration_share_the_same_offsets(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            erased = root / "erased"
            migrated = root / "migrated"
            source.mkdir()
            original = (
                'const marker = "😀";\r\n'
                "export async function load(value: string): Promise<number> {\r\n"
                "  return value.length;\r\n"
                "}\r\n"
                "interface Values { [key: string]: number; enabled: boolean }\r\n"
            )
            (source / "index.ts").write_text(original, encoding="utf-8", newline="")
            result = self.run_node(
                """
                const fs = require('fs');
                const path = require('path');
                const { eraseTypeScript, restoreTypeScript } = require('./src/migration/ts');
                const root = process.env.TEST_ROOT;
                const source = path.join(root, 'source');
                const erased = path.join(root, 'erased');
                const migrated = path.join(root, 'migrated');
                const erasedResult = eraseTypeScript(source, erased);
                const annotations = erasedResult.groundTruth['index.ts'];
                const nodes = annotations
                  .filter(item => item.kind === 'param' || item.kind === 'return')
                  .map(item => ({
                    id: item.offset,
                    text: item.identifier,
                    file: path.join(erased, 'index.ts'),
                    position: { start: { line: item.line, character: item.col } },
                    fullType: JSON.stringify(item.kind === 'return'
                      ? { kind: 'function', returnType: { kind: 'primitive', name: 'number' } }
                      : { kind: 'primitive', name: 'boolean' }),
                  }));
                const report = restoreTypeScript({
                  baseProject: source,
                  erasedRoot: erased,
                  outputRoot: migrated,
                  groundTruth: erasedResult.groundTruth,
                  typegraph: { nodes },
                });
                console.log(JSON.stringify({
                  erasedResult,
                  erased: fs.readFileSync(path.join(erased, 'index.ts'), 'utf8'),
                  migrated: fs.readFileSync(path.join(migrated, 'index.ts'), 'utf8'),
                  report,
                }));
                """,
                {"TEST_ROOT": str(root)},
            )
            self.assertEqual(len(result["erased"]), len(original))
            self.assertEqual(result["erased"].count("\r\n"), original.count("\r\n"))
            self.assertIn("load(value: boolean): Promise<number>", result["migrated"])
            self.assertIn("[key: string]: any", result["migrated"])
            self.assertIn("enabled: any", result["migrated"])
            self.assertEqual(result["report"]["inferred"], 2)
            self.assertEqual(result["report"]["syntaxFallback"], 3)
            self.assertEqual(result["report"]["invalidSpans"], [])

    def test_rule_repair_uses_structured_diagnostics_and_rechecks_the_project(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "index.ts"
            source.write_text(
                "const options: {} = {};\n"
                "export const action = options.action;\n",
                encoding="utf-8",
            )
            result = self.run_node(
                """
                const fs = require('fs');
                const path = require('path');
                const { repairProject } = require('./src/migration/repair');
                repairProject({ root: process.env.TEST_ROOT, strategy: 'rules' })
                  .then(result => console.log(JSON.stringify({
                    result,
                    source: fs.readFileSync(path.join(process.env.TEST_ROOT, 'index.ts'), 'utf8'),
                  })))
                  .catch(error => { console.error(error); process.exit(1); });
                """,
                {"TEST_ROOT": str(root)},
            )
            self.assertEqual(result["result"]["status"], "pass")
            self.assertEqual(result["result"]["initialDiagnostics"], 1)
            self.assertEqual(result["result"]["finalDiagnostics"], 0)
            self.assertIn("options: any", result["source"])

    def test_agent_repair_accepts_unclosed_json_fence(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "index.ts"
            source.write_text(
                "const options: {} = {};\n"
                "export const action = options.action;\n",
                encoding="utf-8",
            )
            result = self.run_node(
                """
                const net = require('./agent/net');
                net.chat = async () => ({ content: '```json\\n{"edits":[{"file":"index.ts","before":"options: {}","after":"options: any","reason":"fix"}],"skip":[]}' });
                const fs = require('fs');
                const path = require('path');
                const { repairProject } = require('./src/migration/repair');
                repairProject({
                  root: process.env.TEST_ROOT,
                  strategy: 'agent',
                  agent: { provider: 'deepseek', apiKey: 'test', baseUrl: 'http://test', model: 'test' },
                }).then(result => console.log(JSON.stringify({
                  result,
                  source: fs.readFileSync(path.join(process.env.TEST_ROOT, 'index.ts'), 'utf8'),
                }))).catch(error => { console.error(error); process.exit(1); });
                """,
                {"TEST_ROOT": str(root)},
            )
            self.assertEqual(result["result"]["status"], "pass")
            self.assertEqual(result["result"]["acceptedEdits"], 1)
            self.assertIn("options: any", result["source"])

    def test_agent_repair_preserves_project_on_invalid_response(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "index.ts"
            original = "const options: {} = {};\nexport const action = options.action;\n"
            source.write_text(original, encoding="utf-8")
            result = self.run_node(
                """
                const net = require('./agent/net');
                net.chat = async () => ({ content: '{"edits":[{"file":"index.ts"' });
                const { repairProject } = require('./src/migration/repair');
                repairProject({
                  root: process.env.TEST_ROOT,
                  strategy: 'agent',
                  agent: { provider: 'deepseek', apiKey: 'test', baseUrl: 'http://test', model: 'test' },
                }).then(result => console.log(JSON.stringify(result)))
                  .catch(error => { console.error(error); process.exit(1); });
                """,
                {"TEST_ROOT": str(root)},
            )
            self.assertEqual(result["status"], "type-error")
            self.assertEqual(result["initialDiagnostics"], result["finalDiagnostics"])
            self.assertEqual(result["rounds"][0]["accepted"], 0)
            self.assertIn("JSON", result["rounds"][0]["error"])
            self.assertEqual(source.read_text(encoding="utf-8"), original)


if __name__ == "__main__":
    unittest.main()
