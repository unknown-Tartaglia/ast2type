import tempfile
import unittest
from pathlib import Path
from subprocess import run

from generate import weave


ROOT = Path(__file__).resolve().parents[2]
TSC = ROOT / "node_modules" / ".bin" / "tsc"


class TypeSanitizationTests(unittest.TestCase):
    def test_invalid_or_internal_types_degrade_to_any(self):
        self.assertEqual(weave._sanitize_ts_type("new (value: string) => Item"), "any")
        self.assertEqual(weave._sanitize_ts_type("object:"), "any")
        self.assertEqual(weave._sanitize_ts_type("obj_123"), "any")
        self.assertEqual(weave._sanitize_ts_type("Promise<string"), "any")

    def test_nested_generic_type_survives_sanitization(self):
        value = "Promise<Record<string, Array<number | null>>>"
        self.assertEqual(weave._sanitize_ts_type(value), value)

    def test_promise_constructor_return_becomes_an_instance_type(self):
        self.assertEqual(
            weave._sanitize_inferred("(value: any) => PromiseConstructor"),
            "(value: any) => Promise<any>",
        )


class SignatureWeavingTests(unittest.TestCase):
    def test_function_signature_changes_only_the_declaration(self):
        source = "function convert(value) { return value; }\nconvert(value);\n"

        result = weave._weave_signature(
            source,
            "convert",
            "(value: string) => string",
        )

        self.assertIsNotNone(result)
        self.assertRegex(result, r"function convert\(value: string\)\s*:\s*string\s*\{")
        self.assertIn("convert(value);", result)
        self.assertEqual(result.count("value: string"), 1)

    def test_nested_function_type_uses_the_outer_arrow(self):
        inferred = "(callback: (value: string) => number) => boolean"

        params, return_type = weave._parse_inferred_params(inferred)

        self.assertEqual(params, ["(value: string) => number"])
        self.assertEqual(return_type, "boolean")

    def test_multiline_default_parameter_with_call_is_woven(self):
        source = (
            "export function arg(\n"
            "  spec,\n"
            "  {argv = process.argv.slice(2), permissive = false} = {}\n"
            ") { return spec; }\n"
        )

        result = weave._weave_signature(
            source,
            "arg",
            "(spec: any, options: any) => any",
        )

        self.assertIsNotNone(result)
        self.assertIn("spec: any", result)
        self.assertIn(
            "{argv = process.argv.slice(2), permissive = false}: any = {}",
            result,
        )

    def test_parameter_defaults_can_contain_closing_delimiters_in_strings(self):
        source = 'function close(value = ")") { return value; }\n'

        result = weave._weave_signature(
            source,
            "close",
            "(value: string) => string",
        )

        self.assertRegex(result, r'close\(value: string = "\)"\)\s*:\s*string')

    def test_rest_arrow_parameter_is_typed(self):
        source = "const arrayUnion = (...arguments_) => arguments_.flat();\n"

        result = weave._weave_signature(
            source,
            "arrayUnion",
            "(arguments_: any[]) => any[]",
        )

        self.assertEqual(
            result,
            "const arrayUnion = (...arguments_: any[]): any[] => arguments_.flat();\n",
        )

    def test_bare_arrow_parameter_is_parenthesized(self):
        source = "const identity = value => value;\n"

        result = weave._weave_signature(
            source,
            "identity",
            "(value: string) => string",
        )

        self.assertEqual(
            result,
            "const identity = (value: string): string => value;\n",
        )

    def test_async_function_keeps_async_modifier(self):
        source = "async function load(key) { return key.length; }\n"

        result = weave._weave_signature(
            source,
            "load",
            "(key: string) => Promise<number>",
        )

        self.assertRegex(
            result,
            r"async function load\(key: string\)\s*:\s*Promise<number>\s*\{",
        )

    def test_runtime_constructor_name_is_not_emitted_as_a_type(self):
        source = (
            "function parse(value) { return new ContentType(value); }\n"
            "function ContentType(value) { this.value = value; }\n"
        )

        result = weave._weave_signature(
            source,
            "parse",
            "(value: string) => ContentType",
        )

        self.assertIn("function parse(value: string) {", result)
        self.assertNotIn(": ContentType", result)

    @unittest.skipUnless(TSC.is_file(), "repository TypeScript compiler is unavailable")
    def test_destructured_arrow_output_parses_as_typescript(self):
        source = (
            "const pick = ({value}, [fallback]) => {\n"
            "  const label = `${value}`;\n"
            "  return value || fallback;\n"
            "};\n"
        )
        exports = [
            {
                "name": "pick",
                "kind": "function",
                "inferred": "({value}: {value: number}, [fallback]: [number]) => number",
            }
        ]
        with tempfile.TemporaryDirectory() as temporary:
            js_path = Path(temporary) / "sample.js"
            ts_path = Path(temporary) / "sample.ts"
            js_path.write_text(source, encoding="utf-8")

            result, woven_names = weave.weave_file(js_path, exports)
            ts_path.write_text(result, encoding="utf-8")

            self.assertEqual(woven_names, ["pick"])
            self.assertIn("`${value}`", result)
            completed = run(
                [
                    str(TSC),
                    "--noEmit",
                    "--skipLibCheck",
                    "--target",
                    "es2021",
                    str(ts_path),
                ],
                capture_output=True,
                text=True,
                timeout=30,
            )
            self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)


class VariableWeavingTests(unittest.TestCase):
    def test_valid_variable_type_is_woven(self):
        source = "export const count = 1;\n"

        result = weave._weave_variable(source, "count", "number")

        self.assertEqual(result, "export const count: number = 1;\n")

    def test_uninformative_or_invalid_variable_type_is_not_woven(self):
        source = "export const value = input;\n"

        self.assertIsNone(weave._weave_variable(source, "value", "any"))
        self.assertIsNone(weave._weave_variable(source, "value", "unknown"))
        self.assertIsNone(weave._weave_variable(source, "value", "object:"))


class PackageNormalizationTests(unittest.TestCase):
    def test_mjs_source_is_woven(self):
        exports = [
            {"name": "mode", "kind": "variable", "inferred": "string"},
        ]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source_path = root / "module.mjs"
            source_path.write_text("export const mode = 'esm';\n", encoding="utf-8")

            result = weave.weave_package(root, exports)

        self.assertIn("module.mjs", result)
        self.assertEqual(result["module.mjs"], "export const mode: string = 'esm';\n")

    def test_class_assignments_receive_only_missing_field_declarations(self):
        source = (
            "class ArgError extends Error {\n"
            "  code: any;\n"
            "  constructor(code) {\n"
            "    super();\n"
            "    this.code = code;\n"
            "    this.reason = 'invalid';\n"
            "  }\n"
            "}\n"
        )

        result = weave._inject_class_fields(source)

        self.assertEqual(result.count("code: any;"), 1)
        self.assertIn("\n  reason: any;\n", result)

    def test_default_export_assignment_is_split_for_declaration_emit(self):
        source = "export default co['default'] = co.co = co;\n"

        result = weave._normalize_default_export_assignments(source)

        self.assertEqual(
            result,
            "co['default'] = co.co = co;\nexport default co;\n",
        )


if __name__ == "__main__":
    unittest.main()
