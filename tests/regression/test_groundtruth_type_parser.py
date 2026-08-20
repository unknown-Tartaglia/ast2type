import json
import tempfile
import unittest
from pathlib import Path
from subprocess import run


ROOT = Path(__file__).resolve().parents[2]
UNKNOWN = {"kind": "primitive", "name": "unknown"}


class GroundTruthTypeParserTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory()
        root = Path(cls.temporary.name)
        cls.ast_output = root / "ast-output"
        cls.inference_output = root / "inference-output"
        source_dir = root / "source"
        source_dir.mkdir()

        type_cases = {
            "predicate": "value is Widget",
            "quotedUnion": '"a|b" | string',
            "tupleValue": "[string, number]",
            "shape": "{ x: number, y?: string }",
            "nestedFunction": "(callback: (value: string) => number) => void",
            "arrayGeneric": "ReadonlyArray<string | number>",
            "optionalMethod": "{ maybe?(): string }",
            "unsupportedUnion": "string | (A & B)",
            "unsupportedTuple": "[string, A & B]",
            "unsupportedObject": "{ [key: string]: number }",
            "unsupportedConstructor": "new (value: string) => Widget",
            "unsupportedGeneric": "Promise<string>",
            "unsupportedImport": 'import("./missing").External',
            "genericFunction": "<T>(value: T) => T",
            "genericMethod": "{ map<T>(value: T): T }",
            "invalidReadonly": "readonly string",
            "defaultedParameter": '(value = "x") => void',
            "thisParameter": "(this: Widget, value: string) => void",
            "restParameter": "(...values: string[]) => void",
            "duplicateMembers": "{ value: string; value: number }",
            "protoMember": "{ __proto__: string }",
            "malformed": "string |",
        }
        cls.unsupported_names = {
            "unsupportedUnion",
            "unsupportedTuple",
            "unsupportedObject",
            "unsupportedConstructor",
            "unsupportedGeneric",
            "unsupportedImport",
            "genericFunction",
            "genericMethod",
            "invalidReadonly",
            "defaultedParameter",
            "thisParameter",
            "restParameter",
            "duplicateMembers",
            "protoMember",
            "malformed",
        }
        source_text = "".join(f"const {name} = null;\n" for name in type_cases)
        source_text += "function unsupportedReturn() { return null; }\n"
        (source_dir / "index.js").write_text(source_text, encoding="utf-8")

        annotations = []
        for name, type_text in type_cases.items():
            offset = source_text.index(name)
            prefix = source_text[:offset]
            annotations.append(
                {
                    "identifier": name,
                    "offset": offset,
                    "line": prefix.count("\n") + 1,
                    "col": offset - prefix.rfind("\n"),
                    "type": type_text,
                    "kind": "variable",
                }
            )
        return_offset = source_text.index("unsupportedReturn")
        return_prefix = source_text[:return_offset]
        annotations.append(
            {
                "identifier": "unsupportedReturn",
                "offset": return_offset,
                "line": return_prefix.count("\n") + 1,
                "col": return_offset - return_prefix.rfind("\n"),
                "type": "A & B",
                "kind": "return",
            }
        )
        cls.annotation_count = len(annotations)
        cls.groundtruth = root / "groundtruth.json"
        cls.groundtruth.write_text(
            json.dumps({"index.js": annotations}),
            encoding="utf-8",
        )

        ast = run(
            [
                "node",
                "-r",
                "ts-node/register",
                "code2ast.ts",
                "-i",
                str(source_dir),
                "-o",
                str(cls.ast_output),
            ],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=60,
        )
        if ast.returncode != 0:
            raise AssertionError(ast.stdout + ast.stderr)

        inference = cls._run_inference(
            ["-g", str(cls.groundtruth)],
            cls.inference_output,
        )
        if inference.returncode != 0:
            raise AssertionError(inference.stdout + inference.stderr)

        graph = json.loads(
            (cls.inference_output / "typegraph.json").read_text(encoding="utf-8")
        )
        cls.evaluation = json.loads(
            (cls.inference_output / "evaluation.json").read_text(encoding="utf-8")
        )
        nodes = {node["id"]: node for node in graph["nodes"]}
        cls.source_ids = {}
        cls.source_types = {}
        cls.annotation_types = {}
        cls.annotation_kinds = {}
        for edge in graph["edges"]:
            if edge["label"] not in {"annotation", "returnAnnotation"}:
                continue
            source_node = nodes[edge["from"]]
            target_node = nodes[edge["to"]]
            name = source_node["label"]
            cls.source_ids[name] = edge["from"]
            cls.source_types[name] = json.loads(source_node["fullType"])
            cls.annotation_types[name] = json.loads(target_node["fullType"])
            cls.annotation_kinds[name] = edge["label"]

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    @classmethod
    def _run_inference(cls, extra_args, output_dir):
        return run(
            [
                "node",
                "--max-old-space-size=4096",
                "-r",
                "ts-node/register",
                "ast2type.ts",
                "-i",
                str(cls.ast_output / "ast"),
                "-o",
                str(output_dir),
                *extra_args,
            ],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=60,
        )

    def test_supported_types_are_mapped_without_string_splitting(self):
        predicate = self.annotation_types["predicate"]
        self.assertEqual(predicate, {"kind": "primitive", "name": "boolean"})

        quoted_union = self.annotation_types["quotedUnion"]
        self.assertEqual(quoted_union["kind"], "union")
        self.assertEqual(
            quoted_union["types"],
            [
                {"kind": "literal", "value": "a|b"},
                {"kind": "primitive", "name": "string"},
            ],
        )
        self.assertIn({"kind": "literal", "value": "a|b"}, quoted_union["types"])
        self.assertIn({"kind": "primitive", "name": "string"}, quoted_union["types"])

        tuple_value = self.annotation_types["tupleValue"]
        self.assertEqual(tuple_value["kind"], "array")
        self.assertEqual(tuple_value["elementType"]["kind"], "union")
        tuple_members = tuple_value["elementType"]["types"]
        self.assertIn({"kind": "primitive", "name": "string"}, tuple_members)
        self.assertIn({"kind": "primitive", "name": "number"}, tuple_members)

        shape = self.annotation_types["shape"]
        self.assertEqual(shape["properties"]["x"], {"kind": "primitive", "name": "number"})
        self.assertCountEqual(
            shape["properties"]["y"]["types"],
            [
                {"kind": "primitive", "name": "string"},
                {"kind": "primitive", "name": "undefined"},
            ],
        )

        nested = self.annotation_types["nestedFunction"]
        self.assertEqual(nested["kind"], "function")
        callback = nested["params"][0]["type"]
        self.assertEqual(callback["kind"], "function")
        self.assertEqual(
            callback["params"][0]["type"],
            {"kind": "primitive", "name": "string"},
        )
        self.assertEqual(
            callback["returnType"],
            {"kind": "primitive", "name": "number"},
        )
        self.assertEqual(nested["returnType"], {"kind": "primitive", "name": "void"})

        array_generic = self.annotation_types["arrayGeneric"]
        self.assertEqual(array_generic["kind"], "array")
        self.assertCountEqual(
            array_generic["elementType"]["types"],
            [
                {"kind": "primitive", "name": "string"},
                {"kind": "primitive", "name": "number"},
            ],
        )

        optional_method = self.annotation_types["optionalMethod"]["properties"]["maybe"]
        self.assertEqual(optional_method["kind"], "union")
        self.assertCountEqual(
            [member["kind"] for member in optional_method["types"]],
            ["function", "primitive"],
        )
        self.assertIn(
            {"kind": "primitive", "name": "undefined"},
            optional_method["types"],
        )

    def test_unsupported_or_malformed_types_are_recorded_as_unknown(self):
        self.assertTrue(self.unsupported_names.issubset(self.annotation_types))
        for name in self.unsupported_names:
            self.assertEqual(self.annotation_types[name], UNKNOWN, name)

    def test_unknown_groundtruth_is_ignored_including_return_annotations(self):
        self.assertEqual(self.annotation_kinds["unsupportedReturn"], "returnAnnotation")
        self.assertEqual(self.annotation_types["unsupportedReturn"], UNKNOWN)
        self.assertEqual(self.evaluation["total"], self.annotation_count)
        self.assertEqual(self.evaluation["unknown"], len(self.unsupported_names) + 1)
        self.assertEqual(self.evaluation["missing"], 0)

    def test_unknown_feedback_is_not_injected_as_a_constraint(self):
        root = Path(self.temporary.name)
        feedback = root / "feedback.json"
        feedback.write_text(
            json.dumps(
                [
                    {
                        "id": self.source_ids["unsupportedUnion"],
                        "type": "A & B",
                    }
                ]
            ),
            encoding="utf-8",
        )
        completed = self._run_inference(
            ["-f", str(feedback)],
            root / "feedback-output",
        )
        self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
        self.assertIn("Feedback injected: 0 entries (1 missed)", completed.stdout)
        feedback_graph = json.loads(
            (root / "feedback-output" / "typegraph.json").read_text(encoding="utf-8")
        )
        feedback_node = next(
            node
            for node in feedback_graph["nodes"]
            if node["id"] == self.source_ids["unsupportedUnion"]
        )
        self.assertEqual(
            json.loads(feedback_node["fullType"]),
            self.source_types["unsupportedUnion"],
        )

    def test_agent_feedback_preserves_legal_opaque_generic_types(self):
        root = Path(self.temporary.name)
        feedback = root / "generic-feedback.json"
        feedback.write_text(
            json.dumps(
                [
                    {
                        "id": self.source_ids["unsupportedGeneric"],
                        "type": "Promise<string>",
                    }
                ]
            ),
            encoding="utf-8",
        )
        completed = self._run_inference(
            ["--agent-feedback", str(feedback)],
            root / "generic-feedback-output",
        )
        self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
        graph = json.loads(
            (root / "generic-feedback-output" / "typegraph.json").read_text(encoding="utf-8")
        )
        node = next(
            item for item in graph["nodes"] if item["id"] == self.source_ids["unsupportedGeneric"]
        )
        inferred = json.loads(node["fullType"])
        self.assertEqual(inferred["kind"], "union")
        self.assertIn(
            {"kind": "object", "name": "Promise<string>", "properties": {}},
            inferred["types"],
        )
