#!/usr/bin/env bash
# Gate: every recorded pin value must match reality. Cross-checks, in order:
#   1. `lakefile.toml` `[[require]]` revs against `lake-manifest.json` (resolved graph);
#   2. the pin table in `docs/release-audit.md` against the manifest + `lean-toolchain`;
#  2b. the Sail generation pins + config hash in `scripts/sail-config/` against that same
#      table (they are generator inputs, so the build graph does not constrain them);
#   3. the SP1 semantic revision quoted in README/report against the single authoritative
#      source, `SP1Clean.FormalModel.CoreProfile.sp1SemanticRevision` (itself `rfl`-checked
#      against the extracted provenance);
#   4. `lakefile.toml` invariants Lake does not check: the two test libraries carry identical
#      option blocks, the one-module `LeanRV64DRvfi` mirrors `LeanRV64D` plus only
#      `backward.do.legacy`, and no other library carries linter options (they are package-level).
#
# This is the gate whose absence let a wrong recorded PolyFun pin survive the 2026-08
# migration: `check_report_citations.sh` validates that cited paths resolve, not that
# recorded pin VALUES match the build graph. Run from anywhere; part of
# `scripts/run_audit.sh` and the CI `guards` job. Exit 0 = all recorded values match.
set -uo pipefail
cd "$(dirname "$0")/.."

if [ "$#" -ne 0 ]; then
  echo "usage: scripts/check_pins.sh" >&2
  exit 2
fi

python3 - <<'EOF'
import hashlib
import pathlib, json, re, sys

fail = 0
def err(msg):
    global fail
    print(f"FAIL: {msg}")
    fail = 1

# -- 1. lakefile.toml requires vs lake-manifest.json ------------------------------------
lakefile = open("lakefile.toml").read()
requires = {}  # name -> rev as written in lakefile
for block in re.split(r"\[\[require\]\]", lakefile)[1:]:
    # a require block ends at the next [[...]] table header
    body = re.split(r"\n\[\[", block)[0]
    name = re.search(r'^name = "([^"]+)"', body, re.M)
    rev = re.search(r'^rev = "([^"]+)"', body, re.M)
    if name and rev:
        requires[name.group(1)] = rev.group(1)

manifest = {p["name"]: p for p in json.load(open("lake-manifest.json"))["packages"]}

for name, rev in requires.items():
    if name not in manifest:
        err(f"lakefile requires '{name}' but lake-manifest.json has no such package")
        continue
    entry = manifest[name]
    if re.fullmatch(r"[0-9a-f]{40}", rev):
        if entry.get("rev") != rev:
            err(f"{name}: lakefile rev {rev} != manifest rev {entry.get('rev')}")
    else:  # tag or branch pin: the manifest records it as inputRev
        if entry.get("inputRev") != rev:
            err(f"{name}: lakefile rev '{rev}' != manifest inputRev '{entry.get('inputRev')}'")
for name, entry in manifest.items():
    # Transitive dependencies (mathlib's own graph) are marked inherited; only direct
    # packages must have a matching [[require]].
    if not entry.get("inherited", False) and name not in requires:
        err(f"lake-manifest.json direct package '{name}' has no [[require]] in lakefile.toml")

# -- 2. docs/release-audit.md pin table vs the resolved graph ---------------------------
audit = open("docs/release-audit.md").read()
def table_value(row_label):
    m = re.search(rf"^\| {re.escape(row_label)} \| `([^`]+)`", audit, re.M)
    return m.group(1) if m else None

toolchain = open("lean-toolchain").read().strip()
core_profile = open("SP1Clean/FormalModel/CoreProfile.lean").read()
semantic = re.search(r'def sp1SemanticRevision : String := "([0-9a-f]{40})"', core_profile)
if not semantic:
    err("sp1SemanticRevision not found in SP1Clean/FormalModel/CoreProfile.lean")
    sys.exit(1)
semantic = semantic.group(1)

expected_rows = {
    "Lean toolchain": toolchain,
    "SP1 semantic source": semantic,
    "mathlib pin": manifest.get("mathlib", {}).get("rev"),
    "Clean pin": manifest.get("Clean", {}).get("rev"),
    "lean-sail pin": manifest.get("Sail", {}).get("rev"),
    "PolyFun pin": manifest.get("PolyFun", {}).get("rev"),
}
for label, expected in expected_rows.items():
    recorded = table_value(label)
    if recorded is None:
        err(f"docs/release-audit.md pin table has no row '| {label} |'")
    elif recorded != expected:
        err(f"docs/release-audit.md row '{label}' records `{recorded}` but the source of truth is `{expected}`")

# AGENTS.md is the operational authority agents load before touching the dependency graph.  A stale
# revision there is more dangerous than stale prose because it can directly steer a future pin
# update, so gate it against the same resolved Clean revision.
agents = open("AGENTS.md").read()
agents_clean = re.search(
    r"The Clean pin is upstream `main`\*\* \(`([0-9a-f]{40})`", agents, re.S)
if not agents_clean:
    err("AGENTS.md does not record the current Clean pin as a full 40-hex commit")
elif agents_clean.group(1) != expected_rows["Clean pin"]:
    err(f"AGENTS.md records Clean pin `{agents_clean.group(1)}` but the resolved pin is "
        f"`{expected_rows['Clean pin']}`")

# -- 2b. the Sail generation pins, which live in a script rather than the build graph ----
# `SAIL_SHA` / `SAIL_RISCV_SHA` / the config hash are inputs to the GENERATED `Lean_RV64D`
# snapshot, so nothing in the manifest constrains them: without this check all three can
# drift from the table with the build fully green.
gen = open("scripts/sail-config/generate_lean_rv64d.sh").read()
def script_pin(name):
    m = re.search(rf"^{name}=([0-9a-f]{{40}})\b", gen, re.M)
    if not m:
        err(f"scripts/sail-config/generate_lean_rv64d.sh has no {name}=<40-hex> constant")
        return None
    return m.group(1)

for label, value in (("Sail compiler source", script_pin("SAIL_SHA")),
                     ("sail-riscv model source", script_pin("SAIL_RISCV_SHA"))):
    if value is None:
        continue
    recorded = table_value(label)
    if recorded is None:
        err(f"docs/release-audit.md pin table has no row '| {label} |'")
    elif recorded != value:
        err(f"docs/release-audit.md row '{label}' records `{recorded}` but "
            f"generate_lean_rv64d.sh pins `{value}`")

# The in-tree generated model (`LeanRV64D/` + `LeanRV64D.lean`) is never hand-edited; its tree hash
# is the local provenance record (CI additionally regenerates it from the pins and diffs).
def tree_hash():
    files = ["LeanRV64D.lean"] + sorted(
        str(q) for q in pathlib.Path("LeanRV64D").rglob("*") if q.is_file())
    h = hashlib.sha256()
    for f in files:
        h.update(f.encode()); h.update(b"\0")
        h.update(hashlib.sha256(open(f, "rb").read()).hexdigest().encode()); h.update(b"\n")
    return h.hexdigest(), len(files)
model_hash, model_files = tree_hash()
m = re.search(r"^\| Generated Sail model \| sha256 `([0-9a-f]{64})` \((\d+) files\)", audit, re.M)
if not m:
    err("docs/release-audit.md pin table has no row '| Generated Sail model | sha256 `<64-hex>` (<n> files)'")
elif m.group(1) != model_hash or int(m.group(2)) != model_files:
    err(f"docs/release-audit.md records the generated Sail model as sha256 `{m.group(1)}` "
        f"({m.group(2)} files) but LeanRV64D/ + LeanRV64D.lean hash to `{model_hash}` "
        f"({model_files} files); regenerate with generate_lean_rv64d.sh --install or refresh the row")

cfg_path = "scripts/sail-config/sp1_rv64d_cfg.json"
cfg_sha = hashlib.sha256(open(cfg_path, "rb").read()).hexdigest()
m = re.search(r"^\| SP1 Sail config \| sha256 `([0-9a-f]{64})`", audit, re.M)
if not m:
    err("docs/release-audit.md pin table has no row '| SP1 Sail config | sha256 `<64-hex>`'")
elif m.group(1) != cfg_sha:
    err(f"docs/release-audit.md records SP1 Sail config sha256 `{m.group(1)}` "
        f"but {cfg_path} hashes to `{cfg_sha}`")

# -- 3. the semantic hash quoted outside the table --------------------------------------
for path in ("README.md", "docs/verification-report.md", "docs/overview.md"):
    text = open(path).read()
    for quoted in set(re.findall(r"`([0-9a-f]{40})`", text)):
        # Any bare 40-hex quote in the reader docs must be a pin this script knows about.
        known = {semantic, *(e for e in expected_rows.values() if e and re.fullmatch(r"[0-9a-f]{40}", e))}
        known |= {p.get("rev") for p in manifest.values()}
        known |= set(re.findall(r"\| [^|]+ \| `([0-9a-f]{40})`", audit))  # e.g. extraction branch
        if quoted not in known:
            err(f"{path} quotes commit `{quoted}` which matches no recorded pin")

# -- 3b. the committed SP1 trace dumps vs the extraction pin ----------------------------
# `export/sp1dump/index.json` records the sp1 commit its dumps were generated at
# (`scripts/update_sp1_dumps.sh` is the sole writer); it must be the same extraction
# pin `update_extracted.py` enforces, or the dumps and the extracted AIR describe
# different Rust trees.
pinned = re.search(r'SP1_PINNED_COMMIT = "([0-9a-f]{40})"', open("update_extracted.py").read())
if not pinned:
    err("SP1_PINNED_COMMIT not found in update_extracted.py")
else:
    dump_index = json.load(open("export/sp1dump/index.json"))
    if dump_index.get("sp1Commit") != pinned.group(1):
        err(f"export/sp1dump/index.json sp1Commit {dump_index.get('sp1Commit')} != "
            f"update_extracted.py SP1_PINNED_COMMIT {pinned.group(1)}")

# 4. lakefile invariants that Lake will not check for us. The two test libraries must carry
#    identical `leanOptions` blocks: Lake gives a module the options of the LAST declared library
#    that matches it, and `SP1CleanTest` matches every test module, so a divergent `SP1CoreTest`
#    block would silently not apply to anything. Any other library carrying linter options would
#    reintroduce the per-library flag copies this file's package-level set replaced.
lakefile = open("lakefile.toml").read()
libs = re.split(r"^\[\[lean_lib\]\]\s*$", lakefile, flags=re.M)[1:]
lib_opts = {}
for block in libs:
    name = re.search(r'^name = "([^"]+)"', block, re.M)
    if not name:
        continue
    opts = sorted(re.findall(r"^leanOptions\.(\S+ = \S+)", block, re.M))
    lib_opts[name.group(1)] = opts
if lib_opts.get("SP1CoreTest") != lib_opts.get("SP1CleanTest"):
    err("lakefile.toml: SP1CoreTest and SP1CleanTest must carry identical leanOptions blocks "
        f"(got {lib_opts.get('SP1CoreTest')} vs {lib_opts.get('SP1CleanTest')})")
# `LeanRV64DRvfi` owns exactly `LeanRV64D.RvfiDii` (declared after `LeanRV64D`) so that one module
# builds with the legacy `do` elaborator (lean4#13858); everything else must equal the model's.
rvfi_expected = sorted(lib_opts.get("LeanRV64D", []) + ["backward.do.legacy = true"])
if lib_opts.get("LeanRV64DRvfi") != rvfi_expected:
    err("lakefile.toml: LeanRV64DRvfi must carry LeanRV64D's leanOptions plus backward.do.legacy = true "
        f"(got {lib_opts.get('LeanRV64DRvfi')}, expected {rvfi_expected})")
for name, opts in lib_opts.items():
    if name in ("SP1CoreTest", "SP1CleanTest", "LeanRV64D", "LeanRV64DRvfi"):
        continue
    if any(o.startswith("weak.linter") or o.startswith("linter") for o in opts):
        err(f"lakefile.toml: library {name} carries linter options {opts}; linters are set once at "
            "package level (see AGENTS.md § Linters)")

if fail == 0:
    print("PASS: recorded pins and Lake configuration agree")
sys.exit(fail)
EOF
