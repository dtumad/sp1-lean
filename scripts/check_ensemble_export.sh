#!/usr/bin/env bash
# Compile freshly generated Rust with Clean's backend and compare against Lean and semantic cases.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check_pins.py
mkdir -p .lake/build/ensemble-export
scratch=$(mktemp -d "$PWD/.lake/build/ensemble-export/run.XXXXXX")
LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2} lake build --wfail --iofail SP1CleanTest.Core.EnsembleExport \
  2>&1 | tee "$scratch/build.log"
python3 - "$scratch" <<'PY'
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
sys.path.insert(0, "scripts")
from lean_flags import flags_for, load_lakefile

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
result = subprocess.run(command, env=dict(os.environ, ENSEMBLE_EXPORT_OUT=str(out)),
                        text=True, capture_output=True)
(out / "lean.log").write_text(result.stdout + result.stderr)
if result.returncode or result.stderr or result.stdout != "EXPORTED ensemble Rust and Lean reference cases\n":
    raise SystemExit(f"Incomplete Lean export; see {out}/lean.log")
files = ["fixed_membership.rs", "fixed_membership.reference.json"]
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
    --no-default-features --features clean-export --test clean_export 2>&1 | tee "$scratch/rust.log"
python3 - "$scratch/rust.log" <<'PY'
from pathlib import Path
import sys
log = Path(sys.argv[1]).read_text()
if "test result: ok. 3 passed; 0 failed;" not in log or "warning:" in log:
    raise SystemExit("Rust export comparison did not complete cleanly")
PY
echo "PASS: built-in ensemble export matches Lean and passes Rust backend regressions"
