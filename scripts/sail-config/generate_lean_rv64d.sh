#!/usr/bin/env bash
# Build the pinned Sail compiler and regenerate the SP1-configured Lean model.
# --deps installs the compiler into an isolated, cacheable opam root under SAIL_GEN_DIR.
# --generate produces fresh module-mode output; --sp1 also checks its recorded fingerprint.
# --stock generates legacy headers for comparison with the original upstream base snapshot.
# --make-config checks the stock config plus the SP1 overlay. Never edit generated Lean.
# Run scripts/prepare_sail.py to validate and install output into .lake/generated/sail.
# Requires opam, cmake, z3, a C compiler, GMP, pkg-config, zlib and m4.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
MODE="${1:?usage: generate_lean_rv64d.sh --deps | --stock | --sp1 | --generate | --make-config}"
case "$MODE" in
  --deps|--stock|--sp1|--generate|--make-config) ;;
  *) echo "unknown mode: $MODE" >&2; exit 2 ;;
esac
REPO_ROOT="$(cd "$HERE/../.." && pwd)"
read -r SAIL_URL SAIL_SHA SAIL_RISCV_SHA OCAML_VERSION BASE_SNAPSHOT < <(
  python3 - "$REPO_ROOT/scripts/provenance.json" <<'PYPROVENANCE'
import json, sys
sail = json.load(open(sys.argv[1]))["sail"]
print(*(sail[key] for key in ("compilerRepository", "compilerRevision", "modelRevision", "ocamlVersion", "baseSnapshot")))
PYPROVENANCE
)
WORK="${SAIL_GEN_DIR:-$REPO_ROOT/.lake/sail-gen}"
mkdir -p "$WORK"
WORK="$(cd "$WORK" && pwd)"
export OPAMROOT="$WORK/opam"
SWITCH=sail-gen
export OPAMYES=1
export OPAMJOBS="${OPAMJOBS:-2}"

cd "$WORK"
[ -d sail ] || git clone --quiet "$SAIL_URL"
[ -d sail-riscv ] || git clone --quiet https://github.com/riscv/sail-riscv
git -C sail cat-file -e "$SAIL_SHA^{commit}" 2>/dev/null || git -C sail fetch --quiet "$SAIL_URL" "$SAIL_SHA"
git -C sail-riscv cat-file -e "$SAIL_RISCV_SHA^{commit}" 2>/dev/null || git -C sail-riscv fetch --quiet origin "$SAIL_RISCV_SHA"
[ -z "$(git -C sail status --porcelain)" ] || { echo "dirty compiler checkout: $WORK/sail" >&2; exit 1; }
[ -z "$(git -C sail-riscv status --porcelain)" ] || { echo "dirty model checkout: $WORK/sail-riscv" >&2; exit 1; }
git -C sail checkout --quiet "$SAIL_SHA"
git -C sail-riscv checkout --quiet "$SAIL_RISCV_SHA"

if [ "$MODE" = --deps ]; then
  if [ -f "$WORK/compiler-revision" ] && [ "$(cat "$WORK/compiler-revision")" = "$SAIL_SHA:$OCAML_VERSION" ] && [ -x "$OPAMROOT/$SWITCH/bin/sail" ]; then
    echo "Using cached compiler $SAIL_SHA"
    exit 0
  fi
  [ -f "$OPAMROOT/config" ] || opam init --bare --disable-sandboxing --no-setup --yes
  opam switch list --short | grep -qx "$SWITCH" || opam switch create "$SWITCH" "$OCAML_VERSION"
  eval "$(opam env --switch=$SWITCH --set-switch)"
  opam update >/dev/null
  (cd sail && opam install . --deps-only --yes)
  (cd sail && make install)
  sail --version
  echo "$SAIL_SHA:$OCAML_VERSION" > "$WORK/compiler-revision"
  exit 0
fi

eval "$(opam env --switch=$SWITCH --set-switch)"
command -v sail >/dev/null || { echo "run --deps first"; exit 1; }
[ -f "$WORK/compiler-revision" ] && [ "$(cat "$WORK/compiler-revision")" = "$SAIL_SHA:$OCAML_VERSION" ] || { echo "run --deps for the pinned compiler first" >&2; exit 1; }
echo "sail: $(sail --version)"

# Configure (writes the stock build/config/rv64d_v256_e64.json from config/config.json.in).
modules="--all-modules;--lean-module-system"
[ "$MODE" != --stock ] || modules="--all-modules"
cmake -S sail-riscv -B sail-riscv/build -DCMAKE_BUILD_TYPE=RelWithDebInfo \
  "-DSAIL_BIN=$OPAMROOT/$SWITCH/bin/sail" "-DSAIL_MODULES=$modules" >/dev/null
CFG=sail-riscv/build/config/rv64d_v256_e64.json

if [ "$MODE" = --make-config ]; then
  # The generated config carries //-comments; strip them before merging, and write via a temp
  # file so a failure never leaves a blank config.
  python3 - "$CFG" "$HERE/sp1-overlay.json" "$HERE/sp1_rv64d_cfg.json" <<'PYEOF'
import json, os, re, sys
def load_jsonc(path):
    text = re.sub(r"^\s*//.*$", "", open(path).read(), flags=re.M)
    return json.loads(text)
def deep_merge(base, overlay):
    for key, value in overlay.items():
        if isinstance(value, dict) and isinstance(base.get(key), dict):
            deep_merge(base[key], value)
        else:
            base[key] = value
    return base
base, overlay, out = sys.argv[1:4]
merged = deep_merge(load_jsonc(base), load_jsonc(overlay))
tmp = out + ".tmp"
with open(tmp, "w") as f:
    json.dump(merged, f, indent=2, sort_keys=True)
    f.write("\n")
os.replace(tmp, out)
PYEOF
  echo "wrote sp1_rv64d_cfg.json (sha256 $(shasum -a 256 "$HERE/sp1_rv64d_cfg.json" | cut -d' ' -f1))"
  exit 0
fi

if [ "$MODE" = --sp1 ] || [ "$MODE" = --generate ]; then
  [ -f "$HERE/sp1_rv64d_cfg.json" ] || { echo "missing sp1_rv64d_cfg.json — run --make-config"; exit 1; }
  cp "$HERE/sp1_rv64d_cfg.json" "$CFG"
fi

# Build the Lean model; the hash guard catches a cmake re-configure clobbering the SP1 config.
H0=$(shasum -a 256 "$CFG" | cut -d' ' -f1)
# Remove only this generator-owned output, so every verification is a fresh generation.
OUT=sail-riscv/build/model/Lean_RV64D
python3 - "$OUT" <<'PYCLEAN'
from pathlib import Path
import shutil, sys
path = Path(sys.argv[1])
if path.exists():
    shutil.rmtree(path)
PYCLEAN
cmake --build sail-riscv/build --target generated_lean_rv64d
H1=$(shasum -a 256 "$CFG" | cut -d' ' -f1)
[ "$H0" = "$H1" ] || { echo "FAIL: cmake regenerated the config mid-build"; exit 1; }

# Repo furniture the nightly adds around the generated tree.
EXCLUDES=(-x README.md -x report.py -x build_log.txt -x .github -x .gitignore -x .lake
          -x lake-manifest.json -x lakefile.toml -x lean-toolchain -x README.md.template -x .git)

verdict=0
diff_against() { # rev label
  [ -d ref ] || git clone --quiet https://github.com/opencompl/sail-riscv-lean ref || return 1
  git -C ref cat-file -e "$1^{commit}" 2>/dev/null || git -C ref fetch --quiet origin "$1" || return 1
  git -C ref checkout --quiet "$1" || return 1
  echo "=== diff vs $2 ($1) ==="
  if diff -ru "${EXCLUDES[@]}" ref "$OUT"; then
    echo "=== IDENTICAL vs $2 ==="
  else
    echo "=== DIFFERS vs $2 (see above) ==="
    return 1
  fi
}

case "$MODE" in
  --stock)
    diff_against "$BASE_SNAPSHOT" "opencompl base" || verdict=1 ;;
  --sp1)
    python3 - "$REPO_ROOT" "$OUT" <<'PYCHECK'
import json, sys
from pathlib import Path
root, output = map(Path, sys.argv[1:])
sys.path.insert(0, str(root / "scripts"))
from check_pins import validate_sail
validate_sail(output, json.loads((root / "scripts/provenance.json").read_text())["sail"])
print("PASS: fresh Sail output matches provenance")
PYCHECK
    ;;
  --generate)
    python3 - "$REPO_ROOT" "$OUT" <<'PYHASH'
import sys
from pathlib import Path
root, output = map(Path, sys.argv[1:])
sys.path.insert(0, str(root / "scripts"))
from check_pins import tree_hash
print("Generated tree fingerprint and file count:", *tree_hash(output))
PYHASH
    ;;
esac
echo "config sha256: $H1"
exit "$verdict"
