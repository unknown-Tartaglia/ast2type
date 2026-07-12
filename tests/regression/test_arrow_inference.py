import json
import tempfile
import unittest
from pathlib import Path
from subprocess import run


ROOT = Path(__file__).resolve().parents[2]


class ArrowInferenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory()
        root = Path(cls.temporary.name)
        source = root / "source"
        ast_output = root / "ast-output"
        inference_output = root / "inference-output"
        source.mkdir()
        (source / "index.js").write_text(
            "const arrayUnion = (...arguments_) => [...arguments_.flat()];\n"
            "const identity = opaqueArg => opaqueArg;\n"
            "const empty = () => {};\n"
            "const outer = () => { function nested() { return 1; } };\n"
            "const expression = function (item) { return item; };\n"
            "const wrapped = ((opaqueWrapped) => opaqueWrapped);\n",
            encoding="utf-8",
        )

        ast = run(
            [
                "node",
                "-r",
                "ts-node/register",
                "code2ast.ts",
                "-i",
                str(source),
                "-o",
                str(ast_output),
            ],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=60,
        )
        if ast.returncode != 0:
            raise AssertionError(ast.stdout + ast.stderr)

        inference = run(
            [
                "node",
                "--max-old-space-size=4096",
                "-r",
                "ts-node/register",
                "ast2type.ts",
                "-i",
                str(ast_output / "ast"),
                "-o",
                str(inference_output),
            ],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=60,
        )
        if inference.returncode != 0:
            raise AssertionError(inference.stdout + inference.stderr)

        graph = json.loads(
            (inference_output / "typegraph.json").read_text(encoding="utf-8")
        )
        cls.function_types = {}
        for node in graph.get("nodes", []):
            if not node.get("fullType"):
                continue
            full_type = json.loads(node["fullType"])
            if isinstance(full_type, dict) and full_type.get("kind") == "function":
                cls.function_types[full_type["name"]] = full_type

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def test_expression_arrow_keeps_binding_params_and_return_type(self):
        inferred = self.function_types["arrayUnion"]
        self.assertEqual(len(inferred["params"]), 1)
        self.assertEqual(inferred["params"][0]["name"], "arguments_")
        self.assertEqual(inferred["params"][0]["type"]["kind"], "array")
        self.assertEqual(inferred["returnType"]["kind"], "array")

    def test_unknown_parameter_slot_and_function_expression_name_are_preserved(self):
        identity = self.function_types["identity"]
        self.assertEqual(len(identity["params"]), 1)
        self.assertEqual(identity["params"][0]["name"], "opaqueArg")
        self.assertEqual(
            identity["params"][0]["type"],
            {"kind": "primitive", "name": "unknown"},
        )

        expression = self.function_types["expression"]
        self.assertEqual(len(expression["params"]), 1)
        self.assertEqual(expression["params"][0]["name"], "item")

        wrapped = self.function_types["wrapped"]
        self.assertEqual(len(wrapped["params"]), 1)
        self.assertEqual(wrapped["params"][0]["name"], "opaqueWrapped")

    def test_nested_return_does_not_change_outer_void_return(self):
        void_type = {"kind": "primitive", "name": "void"}
        self.assertEqual(self.function_types["empty"]["returnType"], void_type)
        self.assertEqual(self.function_types["outer"]["returnType"], void_type)
