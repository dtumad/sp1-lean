"""The built-in Rust comparison must retain every supported instruction family."""

from pathlib import Path
import re
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_release_surface import ROOT, instruction_export_errors


class InstructionExportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lean = (ROOT / "SP1CleanTest/Core/InstructionExport.lean").read_text()
        cls.rust = (ROOT / "rust/sp1-comparison/tests/instruction_export.rs").read_text()

    def test_current_sources_cover_release(self):
        self.assertEqual(instruction_export_errors(self.lean, self.rust), [])

    def test_missing_export_is_rejected(self):
        lean = self.lean.replace('"jal_instruction.rs"', '"missing.rs"')
        self.assertIn("built-in instruction exporter inventory/order differs",
                      instruction_export_errors(lean, self.rust))

    def test_duplicate_export_is_rejected(self):
        lean = self.lean + '\n("jal_instruction.rs", ignored)'
        self.assertTrue(instruction_export_errors(lean, self.rust))

    def test_missing_rust_comparison_is_rejected(self):
        rust, count = re.subn(
            r'generated_instruction!\(\s*generated_jal,.*?\);', '', self.rust, flags=re.S)
        self.assertEqual(count, 1)
        self.assertIn("Rust instruction comparison registrations differ",
                      instruction_export_errors(self.lean, rust))

    def test_wrong_program_or_air_is_rejected(self):
        for name in ("JalInstruction", "JalInstructionAirSpec"):
            with self.subTest(name=name):
                rust = self.rust.replace(name + "\n", "OtherProgram\n", 1)
                rust = rust.replace(name + ",\n", "OtherProgram,\n", 1)
                self.assertNotEqual(rust, self.rust)
                self.assertTrue(instruction_export_errors(self.lean, rust))


if __name__ == "__main__":
    unittest.main()
