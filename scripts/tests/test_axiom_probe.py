"""Regressions for census coverage that survives partial target matches."""

import contextlib
import importlib.util
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch


SPEC = importlib.util.spec_from_file_location(
    "gen_axiom_probe", Path(__file__).resolve().parents[1] / "gen_axiom_probe.py"
)
probes = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(probes)


class ProbeInventoryTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.source = self.root / "SP1Clean" / "Example.lean"
        self.source.parent.mkdir()
        self.source.write_text(
            "namespace Example\ntheorem kept : True := by trivial\n"
            "theorem renamed : True := by trivial\nend Example\n"
        )
        self.main_probe = self.root / "main.lean"
        self.test_probe = self.root / "test.lean"
        overrides = patch.multiple(
            probes,
            ROOT=self.root,
            OUT_MAIN=self.main_probe,
            OUT_TEST=self.test_probe,
            TARGETS=[("SP1Clean/Example.lean", r"theorem\s+(kept|renamed)\b")],
        )
        overrides.start()
        self.addCleanup(overrides.stop)
        self.run_generator()

    def run_generator(self, *args):
        with patch("sys.argv", ["gen_axiom_probe.py", *args]):
            with contextlib.redirect_stdout(io.StringIO()) as output:
                probes.main()
        return output.getvalue()

    def test_renamed_sibling_cannot_silently_disappear(self):
        before = (self.main_probe.read_bytes(), self.test_probe.read_bytes())
        self.source.write_text(
            self.source.read_text().replace("theorem renamed :", "theorem renamed_core :")
        )
        with self.assertRaises(SystemExit):
            self.run_generator()
        self.assertEqual(before, (self.main_probe.read_bytes(), self.test_probe.read_bytes()))

    def test_recorded_test_probe_loss_preserves_both_files(self):
        self.main_probe.write_text(self.main_probe.read_text() + "\n")
        self.test_probe.write_text(self.test_probe.read_text() + "#print axioms Test.gone\n")
        before = (self.main_probe.read_bytes(), self.test_probe.read_bytes())
        with self.assertRaises(SystemExit):
            self.run_generator()
        self.assertEqual(before, (self.main_probe.read_bytes(), self.test_probe.read_bytes()))

    def test_explicit_rename_updates_the_inventory(self):
        self.source.write_text(
            self.source.read_text().replace("theorem renamed :", "theorem renamed_core :")
        )
        with patch.object(probes, "TARGETS", [
            ("SP1Clean/Example.lean", r"theorem\s+(kept|renamed_core)\b")
        ]):
            self.run_generator("--allow-removals")
            self.run_generator("--check")
        self.assertIn("#print axioms Example.renamed_core\n", self.main_probe.read_text())
        self.assertNotIn("#print axioms Example.renamed\n", self.main_probe.read_text())

    def test_allow_removals_does_not_hide_an_empty_target(self):
        self.source.write_text("namespace Example\nend Example\n")
        with self.assertRaises(SystemExit):
            self.run_generator("--allow-removals")

    def test_check_does_not_write(self):
        with patch.object(Path, "write_text", side_effect=AssertionError("check wrote a file")):
            self.run_generator("--check")

    def test_check_rejects_an_unrecorded_addition_without_writing(self):
        self.source.write_text(self.source.read_text() + "theorem added : True := by trivial\n")
        before = (self.main_probe.read_bytes(), self.test_probe.read_bytes())
        with patch.object(probes, "TARGETS", [
            ("SP1Clean/Example.lean", r"theorem\s+(kept|renamed|added)\b")
        ]):
            with self.assertRaises(SystemExit):
                self.run_generator("--check")
        self.assertEqual(before, (self.main_probe.read_bytes(), self.test_probe.read_bytes()))

    def test_check_rejects_a_missing_probe_file(self):
        self.main_probe.unlink()
        with self.assertRaises(SystemExit):
            self.run_generator("--check")
        self.assertFalse(self.main_probe.exists())

    def test_upstream_additions_are_in_the_main_census(self):
        source = self.root / "ToClean" / "Example.lean"
        source.parent.mkdir()
        source.write_text("namespace Air\ntheorem exported : True := by trivial\nend Air\n")
        with patch.object(probes, "TARGETS", [
            *probes.TARGETS,
            ("ToClean/Example.lean", r"theorem\s+(exported)\b"),
        ]):
            self.run_generator()
        self.assertIn("#print axioms Air.exported\n", self.main_probe.read_text())
        self.assertNotIn("Air.exported", self.test_probe.read_text())


if __name__ == "__main__":
    unittest.main()
