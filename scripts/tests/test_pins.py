"""Pin/provenance checks must reject drift without depending on prose snapshots."""

import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import check_pins


class PinTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain",
                     "scripts/provenance.json", "scripts/sail-config/sp1_rv64d_cfg.json",
                     "SP1Clean/FormalModel/CoreProfile.lean", "export/sp1dump/index.json",
                     "LeanRV64D.lean"):
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(check_pins.ROOT / name, path)
        shutil.copytree(check_pins.ROOT / "LeanRV64D", self.root / "LeanRV64D")

    def edit_json(self, name, change):
        path = self.root / name
        content = json.loads(path.read_text())
        change(content)
        path.write_text(json.dumps(content))

    def test_no_documentation_required(self):
        self.assertEqual(check_pins.check(self.root), [])

    def test_wrong_resolved_commit(self):
        self.edit_json("lake-manifest.json", lambda data: next(
            p for p in data["packages"] if p["name"] == "Clean").update(rev="0" * 40))
        self.assertTrue(any("revisions disagree" in e for e in check_pins.check(self.root)))

    def test_wrong_repository_even_with_matching_commit(self):
        self.edit_json("lake-manifest.json", lambda data: next(
            p for p in data["packages"] if p["name"] == "Clean").update(url="https://example.org/other"))
        self.assertTrue(any("URL mismatch" in e for e in check_pins.check(self.root)))

    def test_transitive_path_dependency(self):
        self.edit_json("lake-manifest.json", lambda data: data["packages"].append(
            {"name": "hidden", "type": "path", "inherited": True, "rev": "0" * 40}))
        self.assertTrue(any("git pin" in e for e in check_pins.check(self.root)))

    def test_generated_drift(self):
        with (self.root / "LeanRV64D.lean").open("a") as output:
            output.write("\n-- unreviewed generated edit\n")
        self.assertTrue(any("generated Sail tree" in e for e in check_pins.check(self.root)))

    def test_dump_pin_drift(self):
        self.edit_json("export/sp1dump/index.json", lambda data: data.update(sp1Commit="0" * 40))
        self.assertTrue(any("SP1 dumps" in e for e in check_pins.check(self.root)))

    def test_widened_rvfi_workaround(self):
        path = self.root / "lakefile.toml"
        path.write_text(path.read_text().replace(
            'roots = ["LeanRV64D.RvfiDii"]', 'roots = ["LeanRV64D.RvfiDii", "LeanRV64D.Step"]'))
        self.assertTrue(any("confined" in e for e in check_pins.check(self.root)))


if __name__ == "__main__":
    unittest.main()
