"""A stale generated file or incomplete Rust run must never satisfy export validation."""

from pathlib import Path
import hashlib
import os
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_ensemble_export import check_rust_log, exclusive_run, stage_inputs


class InputStagingTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.source = self.root / "fresh"
        self.source.mkdir()
        self.inputs = self.root / "compile-inputs"

    def stage(self, files):
        hashes = {}
        for name, content in files.items():
            (self.source / name).write_bytes(content)
            hashes[name] = hashlib.sha256(content).hexdigest()
        return stage_inputs(self.source, self.inputs, hashes)

    def test_regeneration_preserves_unchanged_inputs_and_updates_changed_bytes(self):
        self.stage({"a.rs": b"original", "b.json": b"reference"})
        for path in self.inputs.iterdir():
            os.utime(path, ns=(1_000_000_000, 1_000_000_000))
        before = (self.inputs / "b.json").stat()
        result = self.stage({"a.rs": b"changed", "b.json": b"reference"})
        self.assertEqual(result, {"changed": ["a.rs"], "removed": [], "unchanged": 1})
        self.assertEqual((self.inputs / "a.rs").read_bytes(), b"changed")
        after = (self.inputs / "b.json").stat()
        self.assertEqual((after.st_ino, after.st_mtime_ns), (before.st_ino, before.st_mtime_ns))

    def test_removed_artifact_cannot_mask_a_stale_rust_include(self):
        self.stage({"a.rs": b"a", "retired.rs": b"retired"})
        result = self.stage({"a.rs": b"a"})
        self.assertEqual(result["removed"], ["retired.rs"])
        self.assertFalse((self.inputs / "retired.rs").exists())

    def test_missing_or_corrupt_fresh_artifact_does_not_fall_back_to_cache(self):
        self.stage({"a.rs": b"old", "b.rs": b"cached"})
        (self.source / "a.rs").write_bytes(b"new")
        for name in ["missing.rs", "b.rs"]:
            with self.subTest(name=name):
                hashes = {"a.rs": hashlib.sha256(b"new").hexdigest(), name: "0" * 64}
                with self.assertRaises((FileNotFoundError, ValueError)):
                    stage_inputs(self.source, self.inputs, hashes)
                self.assertEqual((self.inputs / "a.rs").read_bytes(), b"old")

    def test_corrupt_cached_file_is_replaced_by_fresh_output(self):
        self.stage({"a.rs": b"correct"})
        (self.inputs / "a.rs").write_bytes(b"corrupt")
        self.assertEqual(self.stage({"a.rs": b"correct"})["changed"], ["a.rs"])
        self.assertEqual((self.inputs / "a.rs").read_bytes(), b"correct")

    def test_second_run_cannot_modify_inputs_while_first_holds_lock(self):
        path = self.root / "inputs.lock"
        with exclusive_run(path):
            with self.assertRaisesRegex(RuntimeError, "already running"):
                with exclusive_run(path):
                    self.fail("concurrent run acquired the same inputs")
        with exclusive_run(path):
            pass


class RustCompletionTests(unittest.TestCase):
    @staticmethod
    def binary(name, count):
        return (f"Running tests/{name}.rs (target/{name})\n"
                f"test result: ok. {count} passed; 0 failed; 0 ignored; "
                "0 measured; 0 filtered out; finished in 0.01s\n")

    def test_requires_each_named_binary_not_just_matching_total_counts(self):
        log = self.binary("first", 3) + self.binary("second", 3)
        self.assertEqual(check_rust_log(log, {"first": 3, "second": 3}),
                         {"first": "target/first", "second": "target/second"})
        with self.assertRaises(ValueError):
            check_rust_log(log.replace("second", "different"), {"first": 3, "second": 3})

    def test_duplicate_partial_filtered_and_warning_runs_fail(self):
        complete = self.binary("first", 3)
        for log in [complete + complete, "Running tests/first.rs (target/first)\n",
                    complete.replace("0 filtered", "1 filtered"),
                    complete + "warning: generated code warning\n"]:
            with self.subTest(log=log), self.assertRaises(ValueError):
                check_rust_log(log, {"first": 3})


if __name__ == "__main__":
    unittest.main()
