"""Regressions for scripts/ci/handoff_restore.py: which hand-off a run may use, and when to wait."""

import importlib.util
from pathlib import Path
import unittest


SPEC = importlib.util.spec_from_file_location(
    "handoff_restore", Path(__file__).resolve().parents[1] / "ci" / "handoff_restore.py"
)
hr = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(hr)

A, B = "a" * 40, "b" * 40


class WantedShaTests(unittest.TestCase):
    def test_main_merge_uses_second_parent(self):
        self.assertEqual(hr.wanted_sha("main", None, [A, B]), B)

    def test_main_non_merge_has_none(self):
        self.assertIsNone(hr.wanted_sha("main", None, [A]))

    def test_stacked_pr_uses_first_parent(self):
        self.assertEqual(hr.wanted_sha("pr", "claude/parent", [A, B]), A)

    def test_pr_on_main_uses_lineage_cache(self):
        self.assertIsNone(hr.wanted_sha("pr", "main", [A, B]))
        self.assertIsNone(hr.wanted_sha("pr", None, [A, B]))


class DecideTests(unittest.TestCase):
    def test_newest_live_artifact_is_restored(self):
        arts = [{"id": 1, "created_at": "2026-11-17T01:00:00Z"}, {"id": 2, "created_at": "2026-11-17T02:00:00Z"},
                {"id": 3, "created_at": "2026-11-17T03:00:00Z", "expired": True}]
        self.assertEqual(hr.decide(arts, []), ("restore", 2))

    def test_running_parent_waits(self):
        self.assertEqual(hr.decide([], [{"status": "completed"}, {"status": "in_progress"}]), ("wait", None))
        self.assertEqual(hr.decide([], [{"status": "queued"}]), ("wait", None))

    def test_finished_parent_without_artifact_falls_back(self):
        self.assertEqual(hr.decide([], [{"status": "completed"}]), ("fallback", None))
        self.assertEqual(hr.decide([{"id": 4, "expired": True}], []), ("fallback", None))


if __name__ == "__main__":
    unittest.main()
