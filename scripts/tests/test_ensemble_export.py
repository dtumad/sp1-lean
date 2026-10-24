"""A stale generated file or incomplete Rust run must never satisfy export validation."""

from pathlib import Path
import hashlib
import os
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_ensemble_export import check_rust_log, exclusive_run, stage_inputs
import check_ensemble_export as exports
import json


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


class ExportHandoffTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.identity = {"sourceRevision": "head", "sourceDigest": "tree",
                         "cleanRevision": "emitter", "sp1Revision": "release"}
        for target, value in [("artifact_names", ["fixture.rs", "fixture.reference.json"]),
                              ("source_identity", self.identity)]:
            mock = patch.object(exports, target, return_value=value)
            mock.start()
            self.addCleanup(mock.stop)
        self.first, self.second = self.root / "first", self.root / "second"
        self.verified = self.root / "verified"
        for directory in [self.first, self.second]:
            directory.mkdir()
            (directory / "fixture.rs").write_text("generated")
            (directory / "fixture.reference.json").write_text("{}")
            exports.write_json(directory / "generation.json", {
                "source": self.identity, "executable": "driver",
                "artifacts": exports.artifact_hashes(directory),
            })

    def change_record(self, directory, update):
        path = directory / "generation.json"
        record = json.loads(path.read_text())
        update(record)
        exports.write_json(path, record)

    def test_verified_handoff_preserves_and_authenticates_every_artifact(self):
        exports.verify(self.first, self.second, self.verified)
        self.assertEqual(exports.validate_inputs(self.verified), exports.artifact_hashes(self.first))
        (self.verified / "fixture.rs").write_text("changed after comparison")
        with self.assertRaisesRegex(ValueError, "matching deterministic"):
            exports.validate_inputs(self.verified)

    def test_stale_source_or_pins_cannot_be_compared(self):
        for field in self.identity:
            with self.subTest(field=field):
                self.change_record(self.second, lambda r: r["source"].update({field: "stale"}))
                with self.assertRaisesRegex(ValueError, "source/pins"):
                    exports.verify(self.first, self.second, self.verified)
                self.assertFalse(self.verified.exists())
                self.change_record(self.second, lambda r: r.update(source=self.identity))

    def test_different_executables_cannot_claim_determinism(self):
        self.change_record(self.second, lambda r: r.update(executable="other driver"))
        with self.assertRaisesRegex(ValueError, "different exporter"):
            exports.verify(self.first, self.second, self.verified)

    def test_missing_extra_or_corrupt_generation_never_publishes_inputs(self):
        for mutation in ["missing", "extra", "corrupt"]:
            with self.subTest(mutation=mutation):
                target = self.second / "fixture.rs"
                if mutation == "missing":
                    target.unlink()
                elif mutation == "extra":
                    (self.second / "unexpected.rs").write_text("extra")
                else:
                    target.write_text("different bytes")
                with self.assertRaises(ValueError):
                    exports.verify(self.first, self.second, self.verified)
                self.assertFalse(self.verified.exists())
                target.write_text("generated")
                (self.second / "unexpected.rs").unlink(missing_ok=True)

    def test_two_successful_but_different_generations_reject(self):
        (self.second / "fixture.rs").write_text("nondeterministic output")
        self.change_record(self.second, lambda r: r.update(artifacts=exports.artifact_hashes(self.second)))
        with self.assertRaisesRegex(ValueError, "Nondeterministic"):
            exports.verify(self.first, self.second, self.verified)

    def test_one_generation_cannot_be_compared_with_itself(self):
        with self.assertRaisesRegex(ValueError, "independent"):
            exports.verify(self.first, self.first, self.verified)

    def test_unverified_generation_is_not_a_rust_input(self):
        with self.assertRaises(FileNotFoundError):
            exports.validate_inputs(self.first)
        record = json.loads((self.first / "generation.json").read_text())
        exports.write_json(self.first / "provenance.json", record)
        with self.assertRaisesRegex(ValueError, "deterministic"):
            exports.validate_inputs(self.first)


if __name__ == "__main__":
    unittest.main()
