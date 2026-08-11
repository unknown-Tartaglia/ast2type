import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from generate import pipeline_erased_ts, weave_erased_ts


ROOT = Path(__file__).resolve().parents[2]


def run_eraser(source: Path, erased: Path) -> dict:
    completed = subprocess.run(
        [
            "node",
            "-r",
            "ts-node/register",
            "eraseAnnotation.ts",
            "-i",
            str(source),
            "-o",
            str(erased),
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=60,
    )
    if completed.returncode != 0:
        raise AssertionError(completed.stdout + completed.stderr)
    return json.loads((erased / "_groundtruth.json").read_text(encoding="utf-8"))


class EraseAnnotationTests(unittest.TestCase):
    def test_erases_complete_annotation_spans_and_preserves_dependencies(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            erased = root / "erased"
            source.mkdir()
            original = (
                'const marker = "\U0001f600";\r\n'
                "interface Model { value: number }\r\n"
                "export function read(\r\n"
                "  { value }: { value: number },\r\n"
                "  key: keyof Model,\r\n"
                "): number { return value; }\r\n"
                "class Box { value!: string; get size(): number { return 1; } }\r\n"
                'interface Values { [key: string]: number; enabled: boolean; "quoted": string }\r\n'
            )
            (source / "index.ts").write_bytes(original.encode("utf-8"))
            (source / "module.mts").write_text(
                "export const mode: string = 'esm';\n", encoding="utf-8"
            )
            (source / "module.cts").write_text(
                "export const mode: string = 'cjs';\n", encoding="utf-8"
            )
            declaration = "export declare function parse(value: string): number;\n"
            (source / "types.d.ts").write_text(declaration, encoding="utf-8")
            dependency = source / "node_modules" / "dependency"
            dependency.mkdir(parents=True)
            (dependency / "index.ts").write_text(
                "export const leaked: string = '';\n", encoding="utf-8"
            )

            groundtruth = run_eraser(source, erased)
            erased_bytes = (erased / "index.ts").read_bytes()
            erased_text = erased_bytes.decode("utf-8")

            self.assertEqual(original.count("\r\n"), erased_text.count("\r\n"))
            self.assertEqual(
                max(weave_erased_ts._utf16_boundaries(original)),
                max(weave_erased_ts._utf16_boundaries(erased_text)),
            )
            self.assertEqual(
                (erased / "types.d.ts").read_text(encoding="utf-8"),
                declaration,
            )
            self.assertFalse((erased / "node_modules").exists())
            self.assertIn("module.mts", groundtruth)
            self.assertIn("module.cts", groundtruth)
            self.assertNotIn("types.d.ts", groundtruth)

            annotations = groundtruth["index.ts"]
            self.assertIn("keyof Model", {item["type"] for item in annotations})
            self.assertEqual(
                [item["kind"] for item in annotations].count("index"), 1
            )
            self.assertEqual(
                [item["kind"] for item in annotations].count("index-value"), 1
            )
            self.assertTrue(any(item["kind"] == "return" for item in annotations))
            self.assertTrue(any(not item["inferable"] for item in annotations))

            boundaries = weave_erased_ts._utf16_boundaries(erased_text)
            spans = []
            for annotation in annotations:
                start = boundaries[annotation["annotationStart"]]
                end = boundaries[annotation["annotationEnd"]]
                self.assertFalse(erased_text[start:end].strip())
                spans.append((start, end))
            spans.sort()
            self.assertTrue(all(left[1] <= right[0] for left, right in zip(spans, spans[1:])))


class WeaveErasedTypeScriptTests(unittest.TestCase):
    def test_restores_typegraph_types_with_utf16_offsets_and_syntax_fallbacks(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            erased = root / "erased"
            migrated = root / "migrated"
            source.mkdir()
            original = (
                'const marker = "\U0001f600";\r\n'
                "export async function load(value: string): Promise<number> {\r\n"
                "  return value.length;\r\n"
                "}\r\n"
                "interface Values { [key: string]: number; enabled: boolean }\r\n"
            )
            (source / "index.ts").write_bytes(original.encode("utf-8"))
            groundtruth = run_eraser(source, erased)
            annotations = groundtruth["index.ts"]

            nodes = []
            for annotation in annotations:
                if annotation["kind"] == "param":
                    full_type = {"kind": "primitive", "name": "boolean"}
                elif annotation["kind"] == "return":
                    full_type = {
                        "kind": "function",
                        "params": [],
                        "returnType": {"kind": "primitive", "name": "number"},
                    }
                else:
                    continue
                nodes.append({
                    "text": annotation["identifier"],
                    "file": str(erased / "index.ts"),
                    "position": {
                        "start": {
                            "line": annotation["line"],
                            "character": annotation["col"],
                        }
                    },
                    "fullType": json.dumps(full_type),
                })
            typegraph = root / "typegraph.json"
            typegraph.write_text(json.dumps({"nodes": nodes}), encoding="utf-8")

            report = weave_erased_ts.weave_project(
                source,
                erased,
                erased / "_groundtruth.json",
                typegraph,
                migrated,
            )
            result = weave_erased_ts._read_source(migrated / "index.ts")

            self.assertIn("load(value: boolean): Promise<number>", result)
            self.assertIn(
                "interface Values { [key: string]: any; enabled: any }",
                result,
            )
            self.assertEqual(result.count("\r\n"), original.count("\r\n"))
            self.assertEqual(report["inferred"], 2)
            self.assertEqual(report["syntax_fallback"], 3)
            self.assertEqual(report["unannotated"], 0)
            self.assertEqual(report["invalid_spans"], [])

    def test_async_promise_return_is_not_wrapped_twice(self):
        annotation = {
            "identifier": "load",
            "kind": "return",
            "isAsync": True,
            "matchText": True,
        }
        candidate = {
            "exprText": "load",
            "fullType": {
                "kind": "function",
                "returnType": {"kind": "primitive", "name": "Promise<number>"},
            },
        }

        self.assertEqual(
            weave_erased_ts._annotation_type(annotation, [candidate]),
            ("Promise<number>", True),
        )

        constructor_candidate = {
            "exprText": "load",
            "fullType": {
                "kind": "function",
                "returnType": {
                    "kind": "object",
                    "name": "PromiseConstructor",
                    "properties": {},
                },
            },
        }
        self.assertEqual(
            weave_erased_ts._annotation_type(annotation, [constructor_candidate]),
            ("Promise<any>", True),
        )

    def test_unknown_graph_return_remains_unannotated(self):
        annotation = {
            "identifier": "load",
            "kind": "return",
            "matchText": True,
        }
        candidate = {
            "exprText": "load",
            "fullType": {
                "kind": "function",
                "returnType": {"kind": "primitive", "name": "unknown"},
            },
        }

        self.assertEqual(
            weave_erased_ts._annotation_type(annotation, [candidate]),
            (None, False),
        )

    def test_rejects_groundtruth_paths_outside_the_output_project(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            erased = root / "erased"
            migrated = root / "migrated"
            source.mkdir()
            erased.mkdir()
            (source / "index.ts").write_text("export {};\n", encoding="utf-8")
            (erased / "index.ts").write_text("export {};\n", encoding="utf-8")
            groundtruth = erased / "_groundtruth.json"
            groundtruth.write_text(
                json.dumps({"../outside.ts": []}), encoding="utf-8"
            )
            typegraph = root / "typegraph.json"
            typegraph.write_text('{"nodes": []}', encoding="utf-8")
            outside = root / "outside.ts"
            outside.write_text("keep\n", encoding="utf-8")

            report = weave_erased_ts.weave_project(
                source, erased, groundtruth, typegraph, migrated
            )

            self.assertEqual(outside.read_text(encoding="utf-8"), "keep\n")
            self.assertEqual(
                report["invalid_spans"][0]["reason"],
                "path escapes output directory",
            )


class ErasedPipelineTests(unittest.TestCase):
    def test_inference_command_uses_project_output_without_groundtruth(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "sample"
            output = root / "result"
            source.mkdir()
            (source / "index.ts").write_text("export const value = 1;\n", encoding="utf-8")
            commands = []

            def fake_run(command, timeout):
                commands.append(command)
                if "eraseAnnotation.ts" in command:
                    target = Path(command[command.index("-o") + 1])
                    target.mkdir(parents=True)
                    (target / "index.ts").write_text(
                        "export const value = 1;\n", encoding="utf-8"
                    )
                    (target / "_groundtruth.json").write_text("{}", encoding="utf-8")
                elif "code2ast.ts" in command:
                    Path(f"{command[-1]}_output").mkdir(parents=True)
                elif "ast2type.ts" in command:
                    target = Path(command[command.index("-o") + 1])
                    target.mkdir(parents=True)
                    (target / "typegraph.json").write_text(
                        '{"nodes": []}', encoding="utf-8"
                    )
                    (target / "typeinfo.json").write_text("[]", encoding="utf-8")

            with mock.patch.object(pipeline_erased_ts, "_run", side_effect=fake_run):
                summary = pipeline_erased_ts.run_project(
                    source,
                    output,
                    use_agent=True,
                    timeout=19,
                    agent_provider="openai",
                    agent_model="gpt-test",
                    agent_base_url="https://api.example.test/v1/",
                )

            infer_command = next(command for command in commands if "ast2type.ts" in command)
            inference = output / "work" / "sample" / "inference"
            self.assertEqual(infer_command[infer_command.index("-o") + 1], str(inference))
            self.assertIn("--sourcedir", infer_command)
            self.assertIn("--agent", infer_command)
            self.assertEqual(
                infer_command[infer_command.index("--agent-provider") + 1],
                "openai",
            )
            self.assertEqual(
                infer_command[infer_command.index("--agent-model") + 1],
                "gpt-test",
            )
            self.assertEqual(
                infer_command[infer_command.index("--agent-base-url") + 1],
                "https://api.example.test/v1",
            )
            self.assertNotIn("-g", infer_command)
            self.assertNotIn("--groundtruth", infer_command)
            self.assertEqual(summary["mode"], "agent")
            self.assertEqual(summary["agentProvider"], "openai")
            self.assertEqual(summary["agentModel"], "gpt-test")
            self.assertEqual(
                json.loads((inference / pipeline_erased_ts.INFERENCE_MANIFEST).read_text()),
                pipeline_erased_ts._manifest(
                    True,
                    "openai",
                    "gpt-test",
                    "https://api.example.test/v1",
                ),
            )

    def test_reuse_requires_identical_sources_and_the_same_mode(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            current = root / "current"
            previous = root / "previous"
            inference = root / "inference"
            current.mkdir()
            previous.mkdir()
            inference.mkdir()
            (current / "index.ts").write_bytes(b"export const value = 1;\r\n")
            (previous / "index.ts").write_bytes(b"export const value = 1;\r\n")

            pipeline_erased_ts._assert_same_erased_sources(current, previous)
            pipeline_erased_ts._write_manifest(inference, use_agent=False)
            pipeline_erased_ts._assert_compatible_inference(inference, use_agent=False)
            with self.assertRaisesRegex(RuntimeError, "cannot reuse standard inference"):
                pipeline_erased_ts._assert_compatible_inference(inference, use_agent=True)

            pipeline_erased_ts._write_manifest(
                inference,
                use_agent=True,
                agent_provider="openai",
                agent_model="gpt-test",
                agent_base_url="https://api.example.test/v1",
            )
            pipeline_erased_ts._assert_compatible_inference(
                inference,
                use_agent=True,
                agent_provider="openai",
                agent_model="gpt-test",
                agent_base_url="https://api.example.test/v1/",
            )
            with self.assertRaisesRegex(RuntimeError, "different API configuration"):
                pipeline_erased_ts._assert_compatible_inference(
                    inference,
                    use_agent=True,
                    agent_provider="openai",
                    agent_model="another-model",
                    agent_base_url="https://api.example.test/v1",
                )

            (previous / "index.ts").write_bytes(b"export const value = 2;\r\n")
            with self.assertRaisesRegex(RuntimeError, "erased sources changed"):
                pipeline_erased_ts._assert_same_erased_sources(current, previous)

    def test_real_standard_pipeline_restores_parameter_and_return_types(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            projects = root / "projects"
            source = projects / "sample"
            output = root / "result"
            source.mkdir(parents=True)
            (source / "index.ts").write_text(
                "export function double(value: number): number {\n"
                "  return value * 2;\n"
                "}\n",
                encoding="utf-8",
            )
            (source / "module.mts").write_text(
                "export const esmCount: number = 1;\n", encoding="utf-8"
            )
            (source / "module.cts").write_text(
                "export const cjsCount: number = 2;\n", encoding="utf-8"
            )
            declaration = "export declare const externalValue: string;\n"
            (source / "types.d.ts").write_text(declaration, encoding="utf-8")
            completed = subprocess.run(
                [
                    "python3",
                    "generate/pipeline_erased_ts.py",
                    "--projects-root",
                    str(projects),
                    "--output-root",
                    str(output),
                    "--packages",
                    "sample",
                    "--timeout",
                    "120",
                ],
                cwd=ROOT,
                capture_output=True,
                text=True,
                timeout=180,
            )

            self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
            migrated = (output / "raw" / "sample" / "index.ts").read_text(
                encoding="utf-8"
            )
            summary = json.loads(
                (output / "work" / "sample" / "summary.json").read_text()
            )
            self.assertIn("double(value: number): number", migrated)
            self.assertIn(
                "esmCount: number",
                (output / "raw" / "sample" / "module.mts").read_text(),
            )
            self.assertIn(
                "cjsCount: number",
                (output / "raw" / "sample" / "module.cts").read_text(),
            )
            self.assertEqual(
                (output / "raw" / "sample" / "types.d.ts").read_text(),
                declaration,
            )
            self.assertEqual(summary["mode"], "standard")
            self.assertGreaterEqual(summary["inferred"], 2)
            self.assertEqual(summary["invalid_spans"], [])

            reused_output = root / "reused-result"
            reused = subprocess.run(
                [
                    "python3",
                    "generate/pipeline_erased_ts.py",
                    "--projects-root",
                    str(projects),
                    "--output-root",
                    str(reused_output),
                    "--packages",
                    "sample",
                    "--reuse-inference-root",
                    str(output),
                    "--timeout",
                    "120",
                ],
                cwd=ROOT,
                capture_output=True,
                text=True,
                timeout=120,
            )
            self.assertEqual(reused.returncode, 0, reused.stdout + reused.stderr)
            self.assertEqual(
                (reused_output / "raw" / "sample" / "index.ts").read_text(),
                migrated,
            )


if __name__ == "__main__":
    unittest.main()
