"""The proof-closure report groups reachability by module and rejects incomplete reports."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from proof_closure import group, summarize, validate


def report(reachable, modules):
    return {"version": 1, "roots": ["Root.theorem"], "modules": modules,
            "reachable": [{"name": name, "module": module} for name, module in reachable]}


class ProofClosureTests(unittest.TestCase):
    def test_modules_without_reachable_declarations_are_outside(self):
        data = report([("A.x", "SP1Clean.A"), ("A.y", "SP1Clean.A"), ("B.z", "SP1Clean.B")],
                      ["SP1Clean.A", "SP1Clean.B", "SP1Clean.C"])
        summary = summarize(data, ["A.x", "C.w"])
        self.assertEqual(summary["outside"], ["SP1Clean.C"])
        self.assertEqual((summary["modules"], summary["inside"], summary["declarations"]), (3, 2, 3))
        self.assertEqual(summary["names"], {"A.x": True, "C.w": False})
        self.assertEqual(summary["reachable_modules"]["SP1Clean.A"], 2)

    def test_incomplete_reports_are_rejected(self):
        validate(report([], ["SP1Clean.A"]))
        for broken in ({"version": 2, "roots": ["r"], "modules": ["m"], "reachable": []},
                       {"version": 1, "roots": [], "modules": ["m"], "reachable": []},
                       {"version": 1, "roots": ["r"], "modules": [], "reachable": []},
                       {"version": 1, "roots": ["r"], "modules": ["m"]}):
            with self.assertRaises(ValueError):
                validate(broken)

    def test_grouping_uses_the_first_two_components(self):
        self.assertEqual(group(["SP1Clean.Soundness.A", "SP1Clean.Soundness.B", "SP1Clean.Model.C"]),
                         {"SP1Clean.Model": ["C"], "SP1Clean.Soundness": ["A", "B"]})


if __name__ == "__main__":
    unittest.main()
