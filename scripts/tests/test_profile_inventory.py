"""Regressions for scripts/profile_aggregate.py --inventory: the join and the verdicts."""

import importlib.util
from pathlib import Path
import unittest


SPEC = importlib.util.spec_from_file_location(
    "profile_aggregate", Path(__file__).resolve().parents[1] / "profile_aggregate.py")
pa = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(pa)


class InventoryTests(unittest.TestCase):
    def test_join_ranks_by_instructions_with_verdicts(self):
        summary = "5.0\t6.0\t0\tSP1Clean.A\n1.0\t1.0\t0\tSP1Clean.B\n2.0\t2.0\t0\tSP1CleanTest.C\n3.0\t3.0\t0\tLeanRV64D.D\n"
        resources = "SP1Clean.A\t100\t10\t1\nSP1Clean.B\t300\t30\t3\nSP1CleanTest.C\t200\t20\t2\nLeanRV64D.D\t50\t5\t5\n"
        closure = {"reachable": [{"module": "SP1Clean.A", "name": "x"}],
                   "unreachable": [{"module": "SP1Clean.A", "name": "y"}, {"module": "SP1Clean.B", "name": "z"}]}
        rows = pa.inventory_rows(summary, resources, closure)
        self.assertEqual([row["module"] for row in rows], ["SP1Clean.B", "SP1CleanTest.C", "SP1Clean.A", "LeanRV64D.D"])
        verdicts = {row["module"]: row["verdict"] for row in rows}
        self.assertEqual(verdicts, {"SP1Clean.A": "headline", "SP1Clean.B": "off-path",
                                    "SP1CleanTest.C": "test", "LeanRV64D.D": "model"})
        a = next(row for row in rows if row["module"] == "SP1Clean.A")
        self.assertEqual((a["reached"], a["declarations"], a["cpu"]), (1, 2, 5.0))

    def test_without_closure_production_verdict_is_unknown(self):
        rows = pa.inventory_rows("1.0\t1.0\t0\tSP1Clean.A\n", "SP1Clean.A\t1\t1\t1\n", None)
        self.assertEqual(rows[0]["verdict"], "-")


if __name__ == "__main__":
    unittest.main()
