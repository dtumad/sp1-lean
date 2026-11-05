"""Module/config controls must reject unrelated generator changes."""
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_sail_regeneration import CONFIG_SITES, check_matrix


class RegenerationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.roots = [Path(self.temp.name) / str(n) for n in range(4)]
        for n, root in enumerate(self.roots):
            (root / "LeanRV64D").mkdir(parents=True)
            files = {"LeanRV64D.lean": "import Sail.Sail\n\nnamespace LeanRV64D\ndef value := 42\n"}
            for name, sites in CONFIG_SITES.items():
                files[name] = "import Sail.Sail\n\n" + "\n".join(
                    site + " : Bool := " + ("true" if n % 2 == 0 else "false") for site in sites)
            for name, source in files.items():
                if n >= 2:
                    source = "module\n\n" + source.replace(
                        "import Sail.Sail\n\n", "public import Sail.Sail\n\n@[expose] public section\n\n")
                (root / name).write_text(source)

    def test_only_reviewed_changes_pass(self):
        check_matrix(*self.roots)

    def test_body_and_namespace_changes_fail_in_each_control(self):
        for root in self.roots:
            path = root / "LeanRV64D.lean"
            original = path.read_text()
            for old, new in (("42", "43"), ("namespace LeanRV64D", "namespace Other")):
                with self.subTest(root=root, change=old):
                    path.write_text(original.replace(old, new))
                    with self.assertRaises(ValueError):
                        check_matrix(*self.roots)
            path.write_text(original)

    def test_missing_extra_or_linked_files_fail(self):
        path = self.roots[1] / "LeanRV64D/extra.lean"
        path.write_text("extra")
        with self.assertRaises(ValueError):
            check_matrix(*self.roots)
        path.unlink()
        path.symlink_to(self.roots[0] / "LeanRV64D.lean")
        with self.assertRaises(ValueError):
            check_matrix(*self.roots)
        path.unlink()
        (self.roots[1] / next(iter(CONFIG_SITES))).unlink()
        with self.assertRaises(ValueError):
            check_matrix(*self.roots)

    def test_incomplete_configuration_delta_fails(self):
        path = self.roots[1] / next(iter(CONFIG_SITES))
        path.write_text(path.read_text().replace("false", "true", 1))
        with self.assertRaises(ValueError):
            check_matrix(*self.roots)
