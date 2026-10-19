#!/usr/bin/env python3
"""Regenerate Clean exports twice and compare them with released SP1 in Rust."""
from contextlib import contextmanager
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

from check_release_surface import CHIPS
from lean_flags import flags_for, load_lakefile

ROOT = Path(__file__).resolve().parents[1]
BUILD_TARGETS = [
    "SP1CleanTest.Core.EnsembleExport",
    "SP1CleanTest.Core.RangeProviderExport",
    "SP1CleanTest.Core.SystemExport",
    "SP1CleanTest.Core.SyscallExport",
    "SP1CleanTest.Core.HostControlExport",
    "SP1CleanTest.Core.InstructionExport",
    "SP1CleanTest.Core.ByteProviderExport",
    "SP1CleanTest.Core.SyscallCodeExport",
    "SP1CleanTest.Core.SnapshotRegisterExport",
    "SP1CleanTest.Core.StaticProviderExport",
    "SP1CleanTest.Core.RamExport",
    "SP1CleanTest.Core.ProgramExport",
    "SP1CleanTest.Core.WritePermissionExport",
    "SP1CleanTest.Core.HintSourceExport",
    "SP1CleanTest.Alignment.Support.InstalledAssemblyExport",
    "SP1CleanTest.Alignment.Support.StoppedAssemblyFixture"
]
RUST_TESTS = {
    "clean_export": 17, "instruction_export": 26, "symbolic_add_export": 2, "system_export": 4,
    "syscall_export": 7, "host_control_export": 7, "byte_provider_export": 6,
    "ram_export": 4, "syscall_code_export": 3,
    "program_export": 5, "write_permission_export": 3, "hint_source_export": 5,
    "installed_assembly_export": 10,
}


def artifact_names():
    files = ["program_fixed.rs", "program_unused.rs", "program_empty.rs", "program_sparse.rs", "program_fixed.reference.json",
             "write_permission.rs", "write_permission_empty.rs", "write_permission.reference.json",
             "syscall_code_guard.rs", "syscall_code_guard.reference.json", "fixed_membership.rs", "fixed_membership.reference.json", "snapshot_registers.rs",
             "snapshot_registers_empty.rs", "snapshot_registers.reference.json", "target_registers.rs",
             "target_registers_empty.rs", "target_registers.reference.json",
             "static_membership.reference.json", "ram_membership.reference.json", "ram_rows.reference.json",
             "ram_byte.rs", "ram_word.rs", "ram_source.rs", "ram_target.rs",
             "ram_source_membership.rs", "ram_target_membership.rs"] + [
        "static_" + name + suffix + ".rs"
        for name in ["empty", "singleton", "uneven", "duplicates", "zeroes"]
        for suffix in ["", "_unused"]
    ] + [
        re.sub(r"(?<!^)(?=[A-Z])", "_", name).lower() + "_instruction.rs"
        for _, name, _ in CHIPS
    ] + [name + "_byte_provider.rs" for name in ["and", "or", "xor", "u8_range", "ltu", "msb"]]
    files += [f"range_{n}_provider.rs" for n in range(17)] + ["memory_bump.rs", "state_bump.rs"]
    files += ["syscall_instruction.rs", "core_syscall.rs", "host_call.rs"]
    files += ["host_halt.rs", "host_enter.rs", "host_control.reference.json",
              "host_commit_terminal.rs", "host_deferred_terminal.rs"]
    files += [f"host_{bank}_{slot}.rs" for bank in ["commit", "deferred"] for slot in range(8)]
    files += ["host_hint_length_empty.rs", "host_hint_length.rs", "host_hint_read.rs",
              "host_hints.reference.json"]
    files += ["hint_sources.reference.json"] + [
        f"hint_{kind}{suffix}.rs" for kind in ["nodes", "words"] for suffix in ["", "_unused", "_empty"]
    ]
    files += ["installed_assembly.rs", "installed_assembly.reference.json",
              "installed_empty.rs", "installed_empty.reference.json", "opcodes.reference.json"]
    files += [name + suffix
              for name in ["installed_stopped_zero", "installed_stopped_wide",
                           "installed_stopped_changed", "installed_fabricated_halt"]
              for suffix in [".rs", ".reference.json"]]
    return files


@contextmanager
def exclusive_run(path):
    """Hold the lock through generation, staging and every Cargo consumer."""
    with path.open("w") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise RuntimeError("Another ensemble export check is already running") from error
        yield


def run_logged(command, log, env):
    print("+ " + " ".join(map(str, command)), flush=True)
    with log.open("w") as stream:
        with subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                              text=True, env=env) as process:
            for line in process.stdout:
                stream.write(line)
                stream.flush()
                print(line, end="", flush=True)
            status = process.wait()
    if status:
        raise RuntimeError(f"Command exited {status}; see {log}")
    return log.read_text()


def stage_inputs(source, destination, hashes):
    """Refresh this owned cache from verified fresh bytes, leaving identical files untouched."""
    if not hashes or any(Path(name).name != name for name in hashes):
        raise ValueError("Expected a nonempty inventory of artifact basenames")
    contents = {}
    for name, expected in hashes.items():
        contents[name] = (source / name).read_bytes()
        if hashlib.sha256(contents[name]).hexdigest() != expected:
            raise ValueError(f"Fresh artifact hash mismatch: {name}")
    if destination.is_symlink():
        raise ValueError("Compile input directory must not be a symlink")
    destination.mkdir(exist_ok=True)
    existing = list(destination.iterdir())
    if any(path.is_symlink() or not path.is_file() for path in existing):
        raise ValueError("Compile inputs must contain only generated regular files")
    removed = []
    for path in existing:
        if path.name not in contents:
            path.unlink()
            removed.append(path.name)
    changed = []
    for name, content in contents.items():
        path = destination / name
        if not path.exists() or path.read_bytes() != content:
            path.write_bytes(content)
            changed.append(name)
    return {"changed": sorted(changed), "removed": sorted(removed),
            "unchanged": len(hashes) - len(changed)}


def check_rust_log(log, expected=RUST_TESTS):
    """Require each named binary once, its full success count and no warnings."""
    if "warning:" in log:
        raise ValueError("Rust comparison emitted warnings")
    counts, binaries = {}, {}
    current = None
    for line in log.splitlines():
        running = re.search(r"Running tests/(\w+)\.rs \(([^)]+)\)", line)
        if running:
            current, binary = running.groups()
            if current in binaries:
                raise ValueError(f"Duplicate Rust comparison binary: {current}")
            binaries[current] = binary
        result = re.match(r"test result: ok\. (\d+) passed; 0 failed; 0 ignored; "
                          r"0 measured; 0 filtered out;", line)
        if result:
            if current is None or current in counts:
                raise ValueError("Unexpected Rust test completion marker")
            counts[current] = int(result[1])
            current = None
    if counts != expected or set(binaries) != set(expected):
        raise ValueError(f"Incomplete Rust comparisons: {counts}")
    return binaries


def generate(out, env):
    build = run_logged(["lake", "build", "--wfail", "--iofail", *BUILD_TARGETS],
                       out / "build.log", env)
    if "Build completed successfully" not in build:
        raise RuntimeError(f"Incomplete dependency build; see {out}/build.log")
    manifest = json.loads(Path("lake-manifest.json").read_text())
    clean = next(package for package in manifest["packages"] if package["name"] == "Clean")
    directory = Path(manifest["packagesDir"]) / "Clean"
    revision = subprocess.check_output(
        ["git", "-C", str(directory), "rev-parse", "HEAD"], text=True).strip()
    dirty = subprocess.check_output(
        ["git", "-C", str(directory), "status", "--porcelain", "--untracked-files=no"], text=True)
    if revision != clean["rev"] or dirty:
        raise RuntimeError("Clean checkout differs from the pinned emitter/backend")
    command = ["lake", "env", "lean", *flags_for(load_lakefile("lakefile.toml"), "SP1CleanTest"),
               "scripts/ensembleExportFixture.lean"]
    for directory in [out, out / "repeat"]:
        directory.mkdir(exist_ok=True)
        result = subprocess.run(command, env={**env, "ENSEMBLE_EXPORT_OUT": str(directory)},
                                text=True, capture_output=True)
        (directory / "lean.log").write_text(result.stdout + result.stderr)
        if result.returncode or result.stderr or result.stdout != "EXPORTED ensemble Rust and Lean reference cases\n":
            raise RuntimeError(f"Incomplete Lean export; see {directory}/lean.log")
    names = artifact_names()
    if len(names) != len(set(names)):
        raise ValueError("Duplicate expected export artifact")
    for directory in [out, out / "repeat"]:
        actual = {path.name for path in directory.iterdir() if path.suffix in {".rs", ".json"}}
        if actual != set(names):
            raise ValueError(f"Unexpected export inventory: {actual.symmetric_difference(names)}")
    hashes = {}
    for name in names:
        content = (out / name).read_bytes()
        if content != (out / "repeat" / name).read_bytes():
            raise ValueError(f"Nondeterministic ensemble export: {name}")
        hashes[name] = hashlib.sha256(content).hexdigest()
    provenance = {
        "cleanRevision": revision,
        "sp1Revision": json.loads(Path("scripts/provenance.json").read_text())["sp1"]["revision"],
        "sourceRevision": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
        "artifacts": hashes,
    }
    (out / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
    return hashes


def compare_rust(out, env):
    """Keep the large assembly's compiler cost separate from component optimization."""
    assembly = {"installed_assembly_export": RUST_TESTS["installed_assembly_export"]}
    components = {name: count for name, count in RUST_TESTS.items() if name not in assembly}
    groups = [
        ("components", components, []),
        ("assembly", assembly, [
            "--config", "profile.release.package.sp1-clean-comparison.opt-level=0",
            "--config", "profile.release.package.sp1-clean-comparison.debug-assertions=false",
        ]),
    ]
    for features, name in [("instruction-export", "rust"),
                           ("instruction-export,mprotect", "rust-mprotect")]:
        logs = []
        for group, expected, options in groups:
            tests = [argument for test in expected for argument in ["--test", test]]
            log = run_logged(["cargo", "test", "--locked", "--release", "--manifest-path",
                              "rust/sp1-comparison/Cargo.toml", "--no-default-features",
                              "--features", features, *options, *tests],
                             out / f"{name}-{group}.log", env)
            check_rust_log(log, expected)
            logs.append(log)
        combined = "\n".join(logs)
        check_rust_log(combined)
        (out / f"{name}.log").write_text(combined)


def main():
    os.chdir(ROOT)
    root = ROOT / ".lake/ensemble-export"
    root.mkdir(parents=True, exist_ok=True)
    env = {**os.environ, "CARGO_TERM_COLOR": "never",
           "LEAN_NUM_THREADS": os.environ.get("LEAN_NUM_THREADS", "2"),
           "CARGO_BUILD_JOBS": os.environ.get("CARGO_BUILD_JOBS", "2")}
    with exclusive_run(root / "inputs.lock"):
        subprocess.run([sys.executable, "scripts/check_pins.py"], env=env, check=True)
        out = Path(tempfile.mkdtemp(prefix="run.", dir=root))
        hashes = generate(out, env)
        print(f"Fresh ensemble artifacts: {out}", flush=True)
        inputs = root / "compile-inputs"
        staging = stage_inputs(out, inputs, hashes)
        (out / "compile-inputs.json").write_text(json.dumps({
            "directory": str(inputs), "artifacts": hashes, **staging}, indent=2) + "\n")
        print(f"Cargo inputs: {len(staging['changed'])} changed, "
              f"{len(staging['removed'])} removed, {staging['unchanged']} unchanged", flush=True)
        env["CLEAN_ENSEMBLE_EXPORT_DIR"] = str(inputs)
        compare_rust(out, env)
        print("PASS: deterministic Clean export, Rust backend regressions and released SP1 "
              "instruction, system and Byte/Range provider comparisons")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
