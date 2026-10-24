#!/usr/bin/env python3
"""Regenerate Clean exports twice and compare them with released SP1 in Rust."""
import argparse
from contextlib import contextmanager
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from time import monotonic

from check_release_surface import CHIPS

ROOT = Path(__file__).resolve().parents[1]
RUST_TESTS = {
    "clean_export": 17, "instruction_export": 26, "symbolic_arithmetic_export": 2, "system_export": 4,
    "syscall_export": 7, "host_control_export": 8, "byte_provider_export": 6,
    "ram_export": 4, "syscall_code_export": 3,
    "program_export": 5, "write_permission_export": 3, "hint_source_export": 5,
    "assembly_boundaries_export": 5, "assembly_stopped_export": 5,
    "assembly_hint_read_export": 3, "assembly_halt_export": 3,
    "assembly_commitments_export": 3, "assembly_ordinary_export": 3,
    "assembly_hints_export": 4, "assembly_enter_export": 3,
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
              "installed_empty.rs", "installed_empty.reference.json", "opcodes.reference.json",
              "installed_hint_read.rs", "installed_hint_read.reference.json",
              "installed_hint_word_padding.rs", "installed_hint_word_padding.reference.json"]
    files += [name + suffix
              for name in ["installed_stopped_zero", "installed_stopped_wide",
                           "installed_stopped_changed", "installed_fabricated_halt",
                           "installed_halt_zero", "installed_halt_wide", "installed_halt_max",
                           "installed_commit_repeat", "installed_deferred_repeat",
                           "installed_commit_partial_halt", "installed_commit_complete_halt"]
              for suffix in [".rs", ".reference.json"]]
    files += [name + suffix
              for name in ["installed_ordinary", "installed_ordinary_prefix", "installed_ordinary_suffix",
                           "installed_ordinary_empty", "installed_hints_empty", "installed_hints_tail",
                           "installed_hints_aligned", "installed_enter"]
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


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_identity():
    """Bind hand-offs to this checkout, including local edits and new source files."""
    names = subprocess.check_output(
        ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"]
    ).decode().split("\0")
    content = hashlib.sha256()
    for name in sorted(set(names) - {""}):
        path = ROOT / name
        # A tracked deletion is distinct from both the old file and an empty file.
        content.update(name.encode() + b"\0")
        content.update(digest(path).encode() if path.is_file() else b"deleted")
        content.update(b"\0")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    clean = next(p for p in manifest["packages"] if p["name"] == "Clean")
    return {
        "sourceRevision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True).strip(),
        "sourceDigest": content.hexdigest(),
        "cleanRevision": clean["rev"],
        "sp1Revision": json.loads((ROOT / "scripts/provenance.json").read_text())["sp1"]["revision"],
    }


def timed_run(command, log, env):
    """Keep GNU time's per-process-tree resource report separate from checked output."""
    started = monotonic()
    if sys.platform.startswith("linux"):
        command = ["/usr/bin/time", "-v", "-o", str(log.with_suffix(".resources.log")), *command]
    try:
        return run_logged(command, log, env)
    finally:
        write_json(log.with_suffix(".timing.json"), {"seconds": monotonic() - started})


def prepare(driver, env):
    driver.mkdir(parents=True, exist_ok=True)
    identity = source_identity()
    build = timed_run(["lake", "build", "--wfail", "--iofail", "ensembleExport"],
                      driver / "build.log", env)
    if "Build completed successfully" not in build:
        raise RuntimeError(f"Incomplete dependency build; see {driver}/build.log")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    directory = ROOT / manifest["packagesDir"] / "Clean"
    revision = subprocess.check_output(
        ["git", "-C", str(directory), "rev-parse", "HEAD"], text=True).strip()
    dirty = subprocess.check_output(
        ["git", "-C", str(directory), "status", "--porcelain", "--untracked-files=no"], text=True)
    if revision != identity["cleanRevision"] or dirty:
        raise RuntimeError("Clean checkout differs from the pinned emitter/backend")
    if identity != source_identity():
        raise RuntimeError("Source changed during exporter build")
    executable = driver / "ensembleExport"
    shutil.copy2(ROOT / ".lake/build/bin/ensembleExport", executable)
    write_json(driver / "driver.json", {"source": identity, "executable": digest(executable)})


def check_source(record):
    if record["source"] != source_identity():
        raise ValueError("Export provenance differs from the current source/pins")


def artifact_hashes(directory):
    names = artifact_names()
    if len(names) != len(set(names)):
        raise ValueError("Duplicate expected export artifact")
    actual = {p.name for p in directory.iterdir() if p.suffix in {".rs", ".json"}
              and p.name not in {"generation.json", "provenance.json"}
              and not p.name.endswith(".timing.json")}
    if actual != set(names):
        raise ValueError(f"Unexpected export inventory: {actual.symmetric_difference(names)}")
    if any((directory / name).is_symlink() for name in names):
        raise ValueError("Export artifacts must be regular files, not symlinks")
    return {name: digest(directory / name) for name in names}


def generate(driver, out, env):
    """One fresh generation; CI can run two independent copies of the same executable."""
    record = json.loads((driver / "driver.json").read_text())
    check_source(record)
    executable = driver / "ensembleExport"
    if executable.is_symlink() or digest(executable) != record["executable"]:
        raise ValueError("Exporter executable differs from its build manifest")
    # upload-artifact does not preserve executable mode.
    executable.chmod(0o755)
    out.mkdir(parents=True, exist_ok=False)
    result = timed_run([str(executable)], out / "lean.log",
                       {**env, "ENSEMBLE_EXPORT_OUT": str(out)})
    if result != "EXPORTED ensemble Rust and Lean reference cases\n":
        raise RuntimeError(f"Incomplete Lean export; see {out}/lean.log")
    check_source(record)
    write_json(out / "generation.json", {**record, "artifacts": artifact_hashes(out)})


def verify(first, second, out):
    """Authenticate both independent generations before publishing any Cargo input."""
    records = [json.loads((path / "generation.json").read_text()) for path in [first, second]]
    for path, record in zip([first, second], records):
        check_source(record)
        if record["artifacts"] != artifact_hashes(path):
            raise ValueError(f"Fresh artifact hash mismatch: {path}")
    if records[0] != records[1]:
        raise ValueError("Nondeterministic exports or different exporter builds")
    if first.resolve() == second.resolve():
        raise ValueError("Two independent generation directories are required")
    out.mkdir(parents=True, exist_ok=False)
    stage_inputs(first, out, records[0]["artifacts"])
    write_json(out / "provenance.json", {**records[0], "deterministic": True})
    print(f"Verified {len(records[0]['artifacts'])} deterministic artifacts: {out}", flush=True)


def validate_inputs(source):
    record = json.loads((source / "provenance.json").read_text())
    check_source(record)
    if record.get("deterministic") is not True or record["artifacts"] != artifact_hashes(source):
        raise ValueError("Cargo inputs lack matching deterministic export evidence")
    return record["artifacts"]


def rust_groups():
    components = {name: count for name, count in RUST_TESTS.items() if not name.startswith("assembly_")}
    return {"components": components, **{
        name: {name: count} for name, count in RUST_TESTS.items() if name.startswith("assembly_")}}


def compare_rust(out, env, group="all", configuration="all"):
    groups = rust_groups()
    if group != "all":
        groups = {group: groups[group]}
    configurations = {"default": "instruction-export", "mprotect": "instruction-export,mprotect"}
    if configuration != "all":
        configurations = {configuration: configurations[configuration]}
    out.mkdir(parents=True, exist_ok=True)
    for name, features in configurations.items():
        logs = []
        for group_name, expected in groups.items():
            options = [] if group_name == "components" else [
                "--config", "profile.release.package.sp1-clean-comparison.opt-level=0",
                "--config", "profile.release.package.sp1-clean-comparison.debug-assertions=false",
            ]
            tests = [argument for test in expected for argument in ["--test", test]]
            log = timed_run(["cargo", "test", "--locked", "--release", "--manifest-path",
                            "rust/sp1-comparison/Cargo.toml", "--no-default-features",
                            "--features", features, *options, *tests],
                           out / f"{name}-{group_name}.log", env)
            check_rust_log(log, expected)
            logs.append(log)
        combined = "\n".join(logs)
        check_rust_log(combined, {test: n for tests in groups.values() for test, n in tests.items()})
        (out / f"{name}.log").write_text(combined)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("stage", nargs="?", default="all",
                        choices=["all", "prepare", "generate", "verify", "rust"])
    parser.add_argument("--output", type=Path)
    parser.add_argument("--driver", type=Path)
    parser.add_argument("--first", type=Path)
    parser.add_argument("--second", type=Path)
    parser.add_argument("--inputs", type=Path)
    parser.add_argument("--group", default="all", choices=["all", *rust_groups()])
    parser.add_argument("--configuration", default="all", choices=["all", "default", "mprotect"])
    args = parser.parse_args()
    required = {"prepare": ["output"], "generate": ["driver", "output"],
                "verify": ["first", "second", "output"], "rust": ["inputs", "output"]}
    for name in required.get(args.stage, []):
        if getattr(args, name) is None:
            parser.error(f"{args.stage} requires --{name}")
    for name in ["output", "driver", "first", "second", "inputs"]:
        value = getattr(args, name)
        if value is not None:
            setattr(args, name, value.resolve())
    os.chdir(ROOT)
    root = ROOT / ".lake/ensemble-export"
    root.mkdir(parents=True, exist_ok=True)
    env = {**os.environ, "CARGO_TERM_COLOR": "never",
           "LEAN_NUM_THREADS": os.environ.get("LEAN_NUM_THREADS", "2"),
           "CARGO_BUILD_JOBS": os.environ.get("CARGO_BUILD_JOBS", "2")}
    with exclusive_run(root / "inputs.lock"):
        subprocess.run([sys.executable, "scripts/check_pins.py"], env=env, check=True)
        if args.stage == "prepare":
            prepare(args.output, env)
        elif args.stage == "generate":
            generate(args.driver, args.output, env)
        elif args.stage == "verify":
            verify(args.first, args.second, args.output)
        else:
            if args.stage == "all":
                out = args.output or Path(tempfile.mkdtemp(prefix="run.", dir=root))
                out.mkdir(parents=True, exist_ok=True)
                prepare(out / "driver", env)
                generate(out / "driver", out / "first", env)
                generate(out / "driver", out / "second", env)
                verify(out / "first", out / "second", out / "verified")
                source = out / "verified"
            else:
                out, source = args.output, args.inputs
            hashes = validate_inputs(source)
            inputs = root / "compile-inputs"
            staging = stage_inputs(source, inputs, hashes)
            out.mkdir(parents=True, exist_ok=True)
            write_json(out / "compile-inputs.json", {"artifacts": hashes, **staging})
            env["CLEAN_ENSEMBLE_EXPORT_DIR"] = str(inputs)
            compare_rust(out, env, args.group, args.configuration)
        print(f"PASS: ensemble export {args.stage}", flush=True)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
