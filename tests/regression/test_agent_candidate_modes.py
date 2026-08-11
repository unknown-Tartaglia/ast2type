import json
import os
import tempfile
import unittest
from pathlib import Path
from subprocess import run


ROOT = Path(__file__).resolve().parents[2]


class AgentCandidateModeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory()
        cls.root = Path(cls.temporary.name)
        cls.source_dir = cls.root / "source"
        cls.ast_output = cls.root / "ast-output"
        cls.source_dir.mkdir()

        cls.source_text = (
            "let leaked;\n"
            "function mystery(opaqueParam) {\n"
            "  return leaked;\n"
            "}\n"
            "class Holder {\n"
            "  opaqueField;\n"
            "}\n"
        )
        (cls.source_dir / "index.js").write_text(
            cls.source_text,
            encoding="utf-8",
        )

        ast = run(
            [
                "node",
                "-r",
                "ts-node/register",
                "code2ast.ts",
                "-i",
                str(cls.source_dir),
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

        offset = cls.source_text.index("leaked")
        prefix = cls.source_text[:offset]
        cls.groundtruth = cls.root / "groundtruth.json"
        cls.groundtruth.write_text(
            json.dumps(
                {
                    "index.js": [
                        {
                            "identifier": "leaked",
                            "offset": offset,
                            "line": prefix.count("\n") + 1,
                            "col": offset - prefix.rfind("\n"),
                            "type": "string",
                            "kind": "variable",
                        }
                    ]
                }
            ),
            encoding="utf-8",
        )
        cls._completed = {}

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    @classmethod
    def _run_inference(cls, label, extra_args):
        output_dir = cls.root / label
        env = os.environ.copy()
        # Candidate discovery must remain testable without contacting the LLM.
        env["DEEPSEEK_API_KEY"] = ""
        env["OPENAI_API_KEY"] = ""
        env["AGENT_PROVIDER"] = "deepseek"
        completed = run(
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
            env=env,
            capture_output=True,
            text=True,
            timeout=60,
        )
        return completed, output_dir

    @classmethod
    def _candidate_run(cls, mode, with_groundtruth=False):
        cache_key = (mode, with_groundtruth)
        if cache_key in cls._completed:
            return cls._completed[cache_key]

        mode_label = "default" if mode is None else mode
        gt_label = "with-gt" if with_groundtruth else "without-gt"
        args = ["--agent"]
        if mode is not None:
            args.extend(["--agent-candidate-mode", mode])
        if with_groundtruth:
            args.extend(["--groundtruth", str(cls.groundtruth)])

        completed, output_dir = cls._run_inference(
            f"candidates-{mode_label}-{gt_label}",
            args,
        )
        if completed.returncode != 0:
            raise AssertionError(completed.stdout + completed.stderr)

        candidate_path = output_dir / "agent-candidates.json"
        if not candidate_path.is_file():
            raise AssertionError(
                f"missing {candidate_path}\n"
                f"stdout:\n{completed.stdout}\n"
                f"stderr:\n{completed.stderr}"
            )
        document = json.loads(candidate_path.read_text(encoding="utf-8"))
        result = completed, output_dir, document
        cls._completed[cache_key] = result
        return result

    @staticmethod
    def _candidate_keys(document):
        return {(candidate["id"], candidate["slot"]) for candidate in document["candidates"]}

    @staticmethod
    def _named_value_candidate(document, name):
        matches = [
            candidate
            for candidate in document["candidates"]
            if candidate["slot"] == "value" and candidate["exprText"] == name
        ]
        if len(matches) != 1:
            raise AssertionError(f"expected one value candidate for {name}, got {matches}")
        return matches[0]

    def test_fair_candidates_are_independent_of_groundtruth(self):
        _, _, without_gt = self._candidate_run("fair", with_groundtruth=False)
        _, _, with_gt = self._candidate_run("fair", with_groundtruth=True)

        self.assertEqual(without_gt["mode"], "fair")
        self.assertEqual(with_gt["mode"], "fair")
        self.assertEqual(
            self._candidate_keys(without_gt),
            self._candidate_keys(with_gt),
        )

        self._named_value_candidate(without_gt, "leaked")
        self._named_value_candidate(without_gt, "opaqueParam")
        self._named_value_candidate(without_gt, "opaqueField")
        self.assertTrue(
            any(candidate["slot"] == "return" for candidate in without_gt["candidates"]),
            without_gt["candidates"],
        )

    def test_gt_candidates_include_the_groundtruth_annotated_variable(self):
        _, _, fair = self._candidate_run("fair", with_groundtruth=False)
        _, _, without_gt = self._candidate_run("gt", with_groundtruth=False)
        _, _, with_gt = self._candidate_run("gt", with_groundtruth=True)

        self._named_value_candidate(fair, "leaked")
        without_keys = self._candidate_keys(without_gt)
        with_keys = self._candidate_keys(with_gt)

        self.assertEqual(without_gt["mode"], "gt")
        self.assertEqual(with_gt["mode"], "gt")
        added_keys = with_keys - without_keys
        self.assertEqual(len(added_keys), 1)
        added = next(
            candidate
            for candidate in with_gt["candidates"]
            if (candidate["id"], candidate["slot"]) in added_keys
        )
        self.assertEqual(added["slot"], "value")
        self.assertEqual(added["exprText"], "leaked")

    def test_default_candidate_mode_is_fair(self):
        _, _, default = self._candidate_run(None, with_groundtruth=False)
        _, _, explicit = self._candidate_run("fair", with_groundtruth=False)

        self.assertEqual(default["mode"], "fair")
        self.assertEqual(
            self._candidate_keys(default),
            self._candidate_keys(explicit),
        )

    def test_invalid_candidate_mode_fails_before_inference(self):
        completed, output_dir = self._run_inference(
            "invalid-candidate-mode",
            ["--agent", "--agent-candidate-mode", "invalid"],
        )

        self.assertNotEqual(completed.returncode, 0)
        diagnostics = completed.stdout + completed.stderr
        self.assertIn("invalid", diagnostics.lower())
        self.assertFalse((output_dir / "agent-candidates.json").exists())

    def test_cached_return_feedback_updates_the_function_return_slot(self):
        _, _, candidates = self._candidate_run("fair", with_groundtruth=False)
        return_candidates = [
            candidate
            for candidate in candidates["candidates"]
            if candidate["slot"] == "return"
        ]
        self.assertEqual(len(return_candidates), 1, return_candidates)
        return_candidate = return_candidates[0]

        feedback_path = self.root / "return-feedback.json"
        feedback_path.write_text(
            json.dumps(
                [
                    {
                        "id": return_candidate["id"],
                        "slot": "return",
                        "type": "number",
                    }
                ]
            ),
            encoding="utf-8",
        )
        completed, output_dir = self._run_inference(
            "cached-return-feedback",
            ["--agent-feedback", str(feedback_path)],
        )
        self.assertEqual(
            completed.returncode,
            0,
            completed.stdout + completed.stderr,
        )

        graph = json.loads((output_dir / "typegraph.json").read_text(encoding="utf-8"))
        node = next(
            item for item in graph["nodes"] if item["id"] == return_candidate["id"]
        )
        function_type = json.loads(node["fullType"])
        self.assertEqual(function_type["kind"], "function")
        self.assertEqual(
            function_type["returnType"],
            {"kind": "primitive", "name": "number"},
        )


if __name__ == "__main__":
    unittest.main()
