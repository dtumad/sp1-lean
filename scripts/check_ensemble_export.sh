#!/usr/bin/env bash
# Compile fresh Clean Rust and compare backend cases and instruction AIR against released SP1.
set -euo pipefail
# Cargo colour can split the completion marker consumed below, including in CI.
export CARGO_TERM_COLOR=never
cd "$(dirname "$0")/.."
python3 scripts/check_pins.py
mkdir -p .lake/ensemble-export
scratch=$(mktemp -d "$PWD/.lake/ensemble-export/run.XXXXXX")
LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2} lake build --wfail --iofail SP1CleanTest.Core.EnsembleExport \
  SP1CleanTest.Core.InstructionExport SP1CleanTest.Core.ByteProviderExport \
  SP1CleanTest.Core.SnapshotRegisterExport SP1CleanTest.Core.StaticProviderExport SP1CleanTest.Core.RamExport \
  SP1CleanTest.Core.PreprocessedByteExport \
  2>&1 | tee "$scratch/build.log"
python3 - "$scratch" <<'PY'
import hashlib
import json
import os
import re
from pathlib import Path
import subprocess
import sys
sys.path.insert(0, "scripts")
from lean_flags import flags_for, load_lakefile
from check_release_surface import CHIPS

out = Path(sys.argv[1])
build_log = (out / "build.log").read_text()
if "Build completed successfully" not in build_log:
    raise SystemExit(f"Incomplete dependency build; see {out}/build.log")
manifest = json.loads(Path("lake-manifest.json").read_text())
clean = next(p for p in manifest["packages"] if p["name"] == "Clean")
directory = Path(manifest["packagesDir"]) / "Clean"
revision = subprocess.check_output(["git", "-C", str(directory), "rev-parse", "HEAD"], text=True).strip()
dirty = subprocess.check_output(
    ["git", "-C", str(directory), "status", "--porcelain", "--untracked-files=no"], text=True)
if revision != clean["rev"] or dirty:
    raise SystemExit("Clean checkout differs from the pinned emitter/backend")
command = ["lake", "env", "lean", *flags_for(load_lakefile("lakefile.toml"), "SP1CleanTest"),
           "scripts/ensembleExportFixture.lean"]
files = ["fixed_membership.rs", "fixed_membership.reference.json", "snapshot_registers.rs",
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
files += ["unified_byte_row.rs", "unified_byte.reference.json"] + [
    f"unified_byte_{n}.rs" for n in [0, 1, 7, 9, 17, 64, 65]
] + [
    f"byte_{layout}_{name}.rs" for layout in ["baseline", "candidate", "routed", "fixed"]
    for name in ["empty", "and-only", "range-heavy", "mixed", "distinct-64", "distinct-65",
                 "add", "beq", "load-byte"]
]
files += ["preprocessed_byte.reference.json"]
files += [f"preprocessed_byte_{n}.rs" for n in [0, 1, 7, 9, 17, 64, 65]]
files += [f"byte_large_{layout}_{n}.rs" for layout in ["routed", "candidate", "fixed"]
          for n in [1024, 16384, 65536]]
for directory in [out, out / "repeat"]:
    directory.mkdir(exist_ok=True)
    result = subprocess.run(command, env=dict(os.environ, ENSEMBLE_EXPORT_OUT=str(directory)),
                            text=True, capture_output=True)
    (directory / "lean.log").write_text(result.stdout + result.stderr)
    if result.returncode or result.stderr or result.stdout != "EXPORTED ensemble Rust and Lean reference cases\n":
        raise SystemExit(f"Incomplete Lean export; see {directory}/lean.log")
for name in files:
    if (out / name).read_bytes() != (out / "repeat" / name).read_bytes():
        raise SystemExit(f"Nondeterministic ensemble export: {name}")
hashes = {name: hashlib.sha256((out / name).read_bytes()).hexdigest() for name in files}
(out / "provenance.json").write_text(json.dumps({
    "cleanRevision": revision,
    "sp1Revision": json.loads(Path("scripts/provenance.json").read_text())["sp1"]["revision"],
    "sourceRevision": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
    "artifacts": hashes,
}, indent=2) + "\n")
print(f"Fresh ensemble artifacts: {out}")
PY
CLEAN_ENSEMBLE_EXPORT_DIR="$scratch" CARGO_BUILD_JOBS=${CARGO_BUILD_JOBS:-2} \
  cargo test --locked --release --manifest-path rust/sp1-comparison/Cargo.toml \
    --no-default-features --features instruction-export --test clean_export \
    --test instruction_export --test byte_provider_export --test ram_export \
    --test unified_byte_export 2>&1 | tee "$scratch/rust.log"
CLEAN_ENSEMBLE_EXPORT_DIR="$scratch" CARGO_BUILD_JOBS=${CARGO_BUILD_JOBS:-2} \
  cargo test --locked --release --manifest-path rust/sp1-comparison/Cargo.toml \
    --no-default-features --features instruction-export,mprotect \
    --test clean_export --test instruction_export --test byte_provider_export --test ram_export \
    --test unified_byte_export 2>&1 | tee "$scratch/rust-mprotect.log"
python3 - "$scratch/rust.log" "$scratch/rust-mprotect.log" <<'PY'
from pathlib import Path
import re
import subprocess
import sys
assert len(sys.argv) == 3
# Require every binary's exact success count in both configurations.
for path, counts in zip(sys.argv[1:], [[3, 4, 11, 17, 25], [3, 4, 11, 17, 25]]):
    log = Path(path).read_text()
    actual = [int(count) for count in re.findall(r"test result: ok\. (\d+) passed; 0 failed;", log)]
    if sorted(actual) != counts or "warning:" in log:
        raise SystemExit(f"Rust export comparison did not complete cleanly: {path}")
first = Path(sys.argv[1])
binaries = re.findall(r"Running tests/unified_byte_export\.rs \(([^)]+)\)", re.sub(r"\x1b\[[0-?]*[ -/]*[@-~]", "", first.read_text()))
if len(binaries) != 1:
    raise SystemExit(f"Missing unique benchmark binary: {first}")
subprocess.run([sys.executable, "scripts/measure_byte_providers.py", "--artifacts", str(first.parent),
                "--binary", binaries[0]], check=True)
PY
echo "PASS: deterministic Clean export, Rust backend regressions and released SP1 instruction and byte-provider comparisons"
