import json
import tempfile
import unittest
from pathlib import Path

from generate import weave_typegraph_ast


def utf16_position(source: str, needle: str, occurrence: int = 1) -> dict:
    start = -1
    for _ in range(occurrence):
        start = source.index(needle, start + 1)
    prefix = source[:start]
    line_prefix = prefix.rsplit("\n", 1)[-1]
    return {
        "start": {
            "line": prefix.count("\n") + 1,
            "character": len(line_prefix.encode("utf-16-le")) // 2 + 1,
        },
        "end": {
            "line": prefix.count("\n") + 1,
            "character": len(line_prefix.encode("utf-16-le")) // 2 + 2,
        },
    }


def function_type(identifier, name, params, return_type):
    return json.dumps({
        "kind": "function",
        "id": identifier,
        "name": name,
        "params": [
            {"name": parameter_name, "type": parameter_type}
            for parameter_name, parameter_type in params
        ],
        "returnType": return_type,
    })


class TypegraphAstWeavingTests(unittest.TestCase):
    def run_weave(self, source_files, nodes):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        source_root = root / "source"
        output_root = root / "output"
        source_root.mkdir()
        for relative, content in source_files.items():
            path = source_root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            with path.open("w", encoding="utf-8", newline="") as target:
                target.write(content)

        materialized_nodes = []
        for node in nodes:
            materialized = dict(node)
            materialized["file"] = str(source_root / node["file"])
            materialized_nodes.append(materialized)
        typegraph = root / "typegraph.json"
        typegraph.write_text(
            json.dumps({"nodes": materialized_nodes}), encoding="utf-8"
        )
        report = weave_typegraph_ast.weave_project(
            source_root, typegraph, output_root
        )
        return output_root, report

    def test_position_selects_nested_namesake_and_ignores_noncanonical_node(self):
        source = (
            "function target(value) { return value; }\n"
            "function outer() {\n"
            "  function target(value) { return value.length; }\n"
            "  return target;\n"
            "}\n"
        )
        full_type = function_type(
            7,
            "target",
            [("value", {"kind": "primitive", "name": "string"})],
            {"kind": "primitive", "name": "number"},
        )
        output, report = self.run_weave(
            {"index.js": source},
            [
                {
                    "id": 8,
                    "file": "index.js",
                    "position": utf16_position(source, "function target", 1),
                    "fullType": full_type,
                },
                {
                    "id": 7,
                    "file": "index.js",
                    "position": utf16_position(source, "function target", 2),
                    "fullType": full_type,
                },
            ],
        )

        result = (output / "index.ts").read_text(encoding="utf-8")
        self.assertIn("function target(value) { return value; }", result)
        self.assertIn(
            "function target(value: string) : number { return value.length; }",
            result,
        )
        self.assertEqual(report["function_nodes"], 2)
        self.assertEqual(report["canonical_targets"], 1)
        self.assertEqual(report["ignored_noncanonical"], 1)
        self.assertEqual(report["woven_targets"], 1)
        self.assertEqual(report["edits"], 2)

    def test_arrow_parameters_and_returns_are_inserted_from_ast_nodes(self):
        source = (
            "const convert = (value = 1, { flag }, ...rest) => "
            "flag ? value : rest.length;\n"
            "const identity = value => value;\n"
        )
        convert_type = function_type(
            10,
            "convert",
            [
                ("value", {"kind": "primitive", "name": "number"}),
                (
                    "options",
                    {
                        "kind": "object",
                        "name": "",
                        "properties": {
                            "flag": {"kind": "primitive", "name": "boolean"}
                        },
                    },
                ),
                (
                    "rest",
                    {
                        "kind": "array",
                        "elementType": {"kind": "primitive", "name": "string"},
                    },
                ),
            ],
            {"kind": "primitive", "name": "number"},
        )
        identity_type = function_type(
            11,
            "identity",
            [("value", {"kind": "primitive", "name": "string"})],
            {"kind": "primitive", "name": "string"},
        )
        output, report = self.run_weave(
            {"arrows.mjs": source},
            [
                {
                    "id": 10,
                    "file": "arrows.mjs",
                    "position": utf16_position(source, "(value = 1"),
                    "fullType": convert_type,
                },
                {
                    "id": 11,
                    "file": "arrows.mjs",
                    "position": utf16_position(source, "value => value"),
                    "fullType": identity_type,
                },
            ],
        )

        result = (output / "arrows.ts").read_text(encoding="utf-8")
        self.assertIn("value: number = 1", result)
        self.assertIn("{ flag }: { flag: boolean }", result)
        self.assertIn("...rest: string[]", result)
        self.assertRegex(result, r"rest: string\[\]\)\s*: number\s*=>")
        self.assertRegex(result, r"\(value: string\)\s*: string\s*=> value")
        self.assertEqual(report["canonical_targets"], 2)
        self.assertEqual(report["woven_targets"], 2)
        self.assertEqual(report["edits"], 6)

    def test_position_mismatch_is_reported_without_name_fallback(self):
        source = "function target(value) { return value; }\n"
        output, report = self.run_weave(
            {"index.js": source},
            [{
                "id": 3,
                "file": "index.js",
                "position": {"start": {"line": 1, "character": 2}},
                "fullType": function_type(
                    3,
                    "target",
                    [("value", {"kind": "primitive", "name": "string"})],
                    {"kind": "primitive", "name": "string"},
                ),
            }],
        )

        self.assertEqual((output / "index.ts").read_text(), source)
        self.assertEqual(report["located_targets"], 0)
        self.assertEqual(report["edits"], 0)
        self.assertEqual(report["skipped"][0]["reason"], "position-mismatch")
        self.assertTrue((output / weave_typegraph_ast.REPORT_NAME).is_file())
        manifest = json.loads(
            (output / weave_typegraph_ast.MANIFEST_NAME).read_text(encoding="utf-8")
        )
        self.assertEqual(manifest["counts"]["skipped_targets"], 1)
        self.assertEqual(len(manifest["typegraph"]["sha256"]), 64)

    def test_exact_position_wins_over_a_stale_function_name(self):
        source = "const actual = value => value;\n"
        output, report = self.run_weave(
            {"index.js": source},
            [{
                "id": 4,
                "file": "index.js",
                "position": utf16_position(source, "value => value"),
                "fullType": function_type(
                    4,
                    "staleName",
                    [("value", {"kind": "primitive", "name": "string"})],
                    {"kind": "primitive", "name": "string"},
                ),
            }],
        )

        self.assertIn(
            "const actual = (value: string) : string => value;",
            (output / "index.ts").read_text(encoding="utf-8"),
        )
        notes = report["target_reports"][0]["notes"]
        self.assertEqual(notes[0]["reason"], "name-mismatch-position-used")

    def test_in_memory_integration_keeps_original_relative_extensions(self):
        with tempfile.TemporaryDirectory() as temporary:
            source_root = Path(temporary)
            js_source = "function first(value) { return value; }\n"
            mjs_source = "export const untouched = 1;\n"
            (source_root / "index.js").write_text(js_source, encoding="utf-8")
            (source_root / "module.mjs").write_text(mjs_source, encoding="utf-8")
            (source_root / "index.cjs").write_text(
                "module.exports = 1;\n", encoding="utf-8"
            )
            typegraph = {
                "nodes": [{
                    "id": 30,
                    "file": str(source_root / "index.js"),
                    "position": utf16_position(js_source, "function first"),
                    "fullType": function_type(
                        30,
                        "first",
                        [("value", {"kind": "primitive", "name": "number"})],
                        {"kind": "primitive", "name": "number"},
                    ),
                }]
            }

            woven, report = weave_typegraph_ast.weave_typegraph_package(
                source_root, typegraph
            )

        self.assertEqual(set(woven), {"index.js", "module.mjs"})
        self.assertIn("first(value: number) : number", woven["index.js"])
        self.assertEqual(woven["module.mjs"], mjs_source)
        self.assertEqual(report["output_files"], 2)
        json.dumps(report)

    def test_utf16_positioning_and_crlf_are_preserved(self):
        source = '"😀"; function greet(name) { return name; }\r\n'
        output, report = self.run_weave(
            {"unicode.js": source},
            [{
                "id": 20,
                "file": "unicode.js",
                "position": utf16_position(source, "function greet"),
                "fullType": function_type(
                    20,
                    "greet",
                    [("name", {"kind": "primitive", "name": "string"})],
                    {"kind": "primitive", "name": "string"},
                ),
            }],
        )

        with (output / "unicode.ts").open("r", encoding="utf-8", newline="") as handle:
            result = handle.read()
        self.assertIn("function greet(name: string) : string {", result)
        self.assertTrue(result.endswith("\r\n"))
        self.assertEqual(report["skipped_targets"], 0)

    def test_anonymous_function_expression_is_located_only_by_position(self):
        source = "const transform = function (value) { return value; };\n"
        output, report = self.run_weave(
            {"anonymous.js": source},
            [{
                "id": 40,
                "file": "anonymous.js",
                "position": utf16_position(source, "function (value)"),
                "fullType": function_type(
                    40,
                    "",
                    [("value", {"kind": "primitive", "name": "boolean"})],
                    {"kind": "primitive", "name": "boolean"},
                ),
            }],
        )

        result = (output / "anonymous.ts").read_text(encoding="utf-8")
        self.assertIn("function (value: boolean) : boolean {", result)
        self.assertEqual(report["woven_targets"], 1)

    def test_constructor_and_setter_never_receive_return_annotations(self):
        source = (
            "class Example {\n"
            "  constructor(value) { this._value = value; }\n"
            "  set value(next) { this._value = next; }\n"
            "}\n"
        )
        output, report = self.run_weave(
            {"class.js": source},
            [
                {
                    "id": 50,
                    "file": "class.js",
                    "position": utf16_position(source, "constructor(value)"),
                    "fullType": function_type(
                        50,
                        "constructor",
                        [("value", {"kind": "primitive", "name": "number"})],
                        {"kind": "primitive", "name": "void"},
                    ),
                },
                {
                    "id": 51,
                    "file": "class.js",
                    "position": utf16_position(source, "set value(next)"),
                    "fullType": function_type(
                        51,
                        "value",
                        [("next", {"kind": "primitive", "name": "number"})],
                        {"kind": "primitive", "name": "void"},
                    ),
                },
            ],
        )

        result = (output / "class.ts").read_text(encoding="utf-8")
        self.assertIn("constructor(value: number) {", result)
        self.assertIn("set value(next: number) {", result)
        self.assertNotIn("): void", result)
        self.assertEqual(report["woven_targets"], 2)
        self.assertEqual(report["edits"], 2)

    def test_typegraph_file_outside_package_is_safely_skipped(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source_root = root / "source"
            source_root.mkdir()
            inside = source_root / "index.js"
            outside = root / "outside.js"
            inside.write_text("export default 1;\n", encoding="utf-8")
            outside_source = "function escaped(value) { return value; }\n"
            outside.write_text(outside_source, encoding="utf-8")
            typegraph = {
                "nodes": [{
                    "id": 60,
                    "file": str(outside),
                    "position": utf16_position(outside_source, "function escaped"),
                    "fullType": function_type(
                        60,
                        "escaped",
                        [("value", {"kind": "primitive", "name": "string"})],
                        {"kind": "primitive", "name": "string"},
                    ),
                }]
            }

            woven, report = weave_typegraph_ast.weave_typegraph_package(
                source_root, typegraph
            )

        self.assertEqual(woven, {"index.js": "export default 1;\n"})
        self.assertEqual(report["skipped_targets"], 1)
        self.assertEqual(report["skipped"][0]["reason"], "file-outside-source-root")

    def test_materialization_preserves_cjs_beside_same_stem_js(self):
        output, report = self.run_weave(
            {
                "index.js": "export default 1;\n",
                "index.cjs": "module.exports = 2;\n",
            },
            [],
        )

        self.assertEqual(
            (output / "index.ts").read_text(encoding="utf-8"),
            "export default 1;\n",
        )
        self.assertEqual(
            (output / "index.cjs").read_text(encoding="utf-8"),
            "module.exports = 2;\n",
        )
        self.assertEqual(report["output_files"], 1)

    def test_invalid_rendered_types_fall_back_and_duplicate_target_is_ignored(self):
        with tempfile.TemporaryDirectory() as temporary:
            source_root = Path(temporary)
            source = "async function load(value) { return value; }\n"
            source_path = source_root / "index.js"
            source_path.write_text(source, encoding="utf-8")
            node = {
                "id": 70,
                "file": str(source_path),
                "position": utf16_position(source, "async function load"),
                "fullType": function_type(
                    70,
                    "load",
                    [("value", {"kind": "primitive", "name": "broken"})],
                    {"kind": "primitive", "name": "broken"},
                ),
            }
            typegraph = {"nodes": [node, dict(node)]}

            woven, report = weave_typegraph_ast.weave_typegraph_package(
                source_root,
                typegraph,
                render_type=lambda _value: "Promise<string",
            )

        self.assertIn("load(value: any) : Promise<any> {", woven["index.js"])
        self.assertEqual(report["canonical_targets"], 1)
        self.assertEqual(report["ignored_duplicate_canonical"], 1)
        notes = report["target_reports"][0]["notes"]
        self.assertEqual(
            sum(note["reason"] == "invalid-type-fallback" for note in notes),
            2,
        )
        self.assertIn("async-return-wrapped", {note["reason"] for note in notes})

    def test_async_union_starting_with_promise_is_still_wrapped(self):
        with tempfile.TemporaryDirectory() as temporary:
            source_root = Path(temporary)
            source = "async function load(value) { return value; }\n"
            source_path = source_root / "index.js"
            source_path.write_text(source, encoding="utf-8")
            typegraph = {"nodes": [{
                "id": 71,
                "file": str(source_path),
                "position": utf16_position(source, "async function load"),
                "fullType": function_type(
                    71,
                    "load",
                    [("value", {"kind": "primitive", "name": "number"})],
                    {"kind": "primitive", "name": "return-union"},
                ),
            }]}

            def render(full_type):
                return (
                    "Promise<string> | string"
                    if full_type.get("name") == "return-union"
                    else "number"
                )

            woven, _report = weave_typegraph_ast.weave_typegraph_package(
                source_root,
                typegraph,
                render_type=render,
            )

        self.assertIn(
            "load(value: number) : Promise<Promise<string> | string> {",
            woven["index.js"],
        )


if __name__ == "__main__":
    unittest.main()
