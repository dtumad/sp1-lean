"""Audit completion requires the exact semantic roots, not just a matching count."""
from pathlib import Path
import sys
import unittest
import contextlib
import io
import json
import subprocess
import tempfile
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_capstone_contract import EXPECTED_ROOTS, validate_manifest
import check_capstone_contract as contract


class ManifestTests(unittest.TestCase):
    def test_complete_roots(self):
        validate_manifest({"version": 1, "roots": sorted(EXPECTED_ROOTS), "declarations": ["fixture"]})

    def test_same_count_cannot_mask_substituted_or_duplicated_roots(self):
        roots = sorted(EXPECTED_ROOTS)
        for replacement in ("unrelated", roots[1]):
            with self.assertRaises(ValueError):
                validate_manifest({"version": 1, "roots": [replacement, *roots[1:]],
                                   "declarations": ["fixture"]})

    def test_missing_root_or_empty_dependency_graph_fails(self):
        for roots, declarations in ((sorted(EXPECTED_ROOTS)[:-1], ["fixture"]),
                                    (sorted(EXPECTED_ROOTS), [])):
            with self.assertRaises(ValueError):
                validate_manifest({"version": 1, "roots": roots, "declarations": declarations})

    def test_zero_exit_does_not_accept_missing_output_or_stack_overflow(self):
        for diagnostics in ("", "error: stack overflow\n"):
            with patch.object(sys, "argv", ["check", "--no-build"]), \
                    patch.object(contract.subprocess, "run", return_value=
                                 subprocess.CompletedProcess([], 0, diagnostics, "")), \
                    contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(contract.main(), 1)

    def test_changed_contract_cannot_pass_a_successful_process(self):
        original = {"version": 1, "roots": sorted(EXPECTED_ROOTS),
                    "declarations": [{"name": "headline", "typeFingerprint": "original"}]}
        changed = {**original, "declarations": [{"name": "headline", "typeFingerprint": "extra-premise"}]}

        def run(_command, **kwargs):
            Path(kwargs["env"]["CAPSTONE_SURFACE_OUT"]).write_text(json.dumps(changed))
            return subprocess.CompletedProcess([], 0, "", "")

        with tempfile.TemporaryDirectory() as directory:
            snapshot = Path(directory) / "snapshot.json"
            snapshot.write_text(json.dumps(original, indent=2, sort_keys=True) + "\n")
            with patch.object(sys, "argv", ["check", "--no-build"]), \
                    patch.object(contract, "SNAPSHOT", snapshot), \
                    patch.object(contract, "ROOT", Path(directory)), \
                    patch.object(contract.subprocess, "run", side_effect=run), \
                    contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(contract.main(), 1)
