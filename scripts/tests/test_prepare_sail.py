"""Restored generated files must be authenticated before becoming build inputs."""

from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_pins import tree_hash, validate_sail
from prepare_sail import install


class SailPreparationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.source = self.root / "source"
        (self.source / "LeanRV64D").mkdir(parents=True)
        (self.source / "LeanRV64D.lean").write_text("module\npublic import LeanRV64D.Defs\n")
        (self.source / "LeanRV64D/Defs.lean").write_text("module\n@[expose] public def sample := 1\n")
        digest, count = tree_hash(self.source)
        self.pins = dict(moduleSystem=True, generatedTreeSha256=digest, generatedFiles=count)
        self.destination = self.root / "prepared"

    def test_valid_tree_is_copied_and_verified(self):
        install(self.source, self.destination, self.pins)
        validate_sail(self.destination, self.pins)
        self.assertEqual(tree_hash(self.source), tree_hash(self.destination))

    def test_corruption_preserves_the_previous_prepared_tree(self):
        install(self.source, self.destination, self.pins)
        (self.source / "LeanRV64D/Defs.lean").write_text("module\naxiom bad : False\n")
        with self.assertRaises(ValueError):
            install(self.source, self.destination, self.pins)
        validate_sail(self.destination, self.pins)

    def test_missing_extra_and_symlinked_files_are_rejected(self):
        leaf = self.source / "LeanRV64D/Defs.lean"
        contents = leaf.read_text()
        leaf.unlink()
        with self.assertRaises(ValueError):
            validate_sail(self.source, self.pins)
        leaf.write_text(contents)
        extra = self.source / "LeanRV64D/Unexpected.lean"
        extra.write_text("module\n")
        with self.assertRaises(ValueError):
            validate_sail(self.source, self.pins)
        extra.unlink()
        outside = self.root / "outside.lean"
        leaf.rename(outside)
        leaf.symlink_to(outside)
        with self.assertRaisesRegex(ValueError, "symlink"):
            validate_sail(self.source, self.pins)


if __name__ == "__main__":
    unittest.main()
