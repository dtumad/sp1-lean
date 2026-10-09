#!/usr/bin/env bash
# Compile fresh Clean Rust and compare backend cases and instruction AIR against released SP1.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check_pins.py
mkdir -p .lake/ensemble-export
scratch=$(mktemp -d "$PWD/.lake/ensemble-export/run.XXXXXX")
LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2} lake build --wfail --iofail SP1CleanTest.Core.EnsembleExport \
  SP1CleanTest.Core.InstructionExport \
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
files = ["fixed_membership.rs", "fixed_membership.reference.json"] + [
    re.sub(r"(?<!^)(?=[A-Z])", "_", name).lower() + "_instruction.rs"
    for _, name, _ in CHIPS
]
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
    "sourceRevision": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
    "artifacts": hashes,
}, indent=2) + "\n")
print(f"Fresh ensemble artifacts: {out}")
PY
CLEAN_ENSEMBLE_EXPORT_DIR="$scratch" CARGO_BUILD_JOBS=${CARGO_BUILD_JOBS:-2} \
  cargo test --locked --release --manifest-path rust/sp1-comparison/Cargo.toml \
    --no-default-features --features instruction-export --test clean_export \
    --test instruction_export 2>&1 | tee "$scratch/rust.log"
CLEAN_ENSEMBLE_EXPORT_DIR="$scratch" CARGO_BUILD_JOBS=${CARGO_BUILD_JOBS:-2} \
  cargo test --locked --release --manifest-path rust/sp1-comparison/Cargo.toml \
    --no-default-features --features instruction-export,mprotect \
    --test instruction_export 2>&1 | tee "$scratch/rust-mprotect.log"
python3 - "$scratch/rust.log" "$scratch/rust-mprotect.log" <<'PY'
from pathlib import Path
import sys
assert len(sys.argv) == 3
for path, counts in zip(sys.argv[1:], [[3, 19], [19]]):
    log = Path(path).read_text()
    if (log.count("test result: ok.") != len(counts)
            or any(log.count(f"test result: ok. {count} passed; 0 failed;") != 1
                   for count in counts) or "warning:" in log):
        raise SystemExit(f"Rust export comparison did not complete cleanly: {path}")
PY
echo "PASS: deterministic Clean export, Rust backend regressions and released SP1 instruction comparisons"
