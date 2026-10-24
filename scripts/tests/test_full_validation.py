"""A partial or skipped validation graph must never satisfy the required CI check."""

import copy
import importlib.util
from pathlib import Path
import re
import sys
import unittest

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
from check_ensemble_export import RUST_TESTS, rust_groups

spec = importlib.util.spec_from_file_location("full_validation", SCRIPTS / "ci/check_full_validation.py")
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


class FullValidationTests(unittest.TestCase):
    def setUp(self):
        self.jobs = {name: {"result": "success"} for name in gate.REQUIRED}
        self.jobs["build"]["outputs"] = {"full-build": "true"}

    def test_complete_graph_passes(self):
        gate.validate(self.jobs)

    def test_every_non_success_and_missing_job_fails(self):
        for name in gate.REQUIRED:
            for status in ["failure", "cancelled", "skipped", None]:
                with self.subTest(name=name, status=status):
                    jobs = copy.deepcopy(self.jobs)
                    jobs[name]["result"] = status
                    with self.assertRaises(ValueError):
                        gate.validate(jobs)
            jobs = copy.deepcopy(self.jobs)
            del jobs[name]
            with self.assertRaises(ValueError):
                gate.validate(jobs)

    def test_core_build_is_not_full_validation(self):
        for outputs in [{}, {"full-build": "false"}]:
            self.jobs["build"]["outputs"] = outputs
            with self.assertRaisesRegex(ValueError, "Core-only"):
                gate.validate(self.jobs)

    def test_workflow_requires_all_jobs_and_every_rust_group(self):
        workflow = (SCRIPTS.parent / ".github/workflows/lean_action_ci.yml").read_text()
        gate_job = workflow.split("  build-full:\n", 1)[1]
        needs = re.search(r"needs: \[([^]]+)\]", gate_job)[1]
        self.assertEqual(set(needs.split(", ")), gate.REQUIRED)
        self.assertIn("always()", gate_job)
        rust_job = workflow.split("  export-rust:\n", 1)[1].split("  build-full:\n")[0]
        self.assertIn("configuration: [default, mprotect]", rust_job)
        groups = re.findall(r"^          - (\w+)$", rust_job, re.M)
        self.assertEqual(set(groups), set(rust_groups()))
        flattened = {name: count for group in rust_groups().values() for name, count in group.items()}
        self.assertEqual(flattened, RUST_TESTS)


if __name__ == "__main__":
    unittest.main()
