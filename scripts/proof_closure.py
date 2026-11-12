#!/usr/bin/env python3
"""Report which repository modules the headline results depend on, following theorem proofs.

Default builds the full library first; --no-build reuses an existing full build. A fresh output
file and silent diagnostics are required even on exit zero, because the Lean frontend can return
zero after a stack overflow. The traversal must reach a module that only proofs reach, so a
statement-only result (proof bodies unavailable) is rejected rather than reported as dead code.

This is a retirement report, not a gate: a module outside the closure may still guard a distinct
claim through a test or be planned material for an open obligation.
"""

import argparse
import re
from collections import defaultdict
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent.parent
# Reached from `Shard.sail_trace` only through proof bodies (`path_of_replay`, `step_of_replay`).
PROOF_ONLY_MODULE = "SP1Clean.Soundness.HostHintReadExecutionPath"
# Compiler-generated auxiliaries are hidden from per-module listings; their owners are listed.
AUXILIARY = re.compile(
    r"\.(match_\d+|proof_\d+|eq_\d+|eq_def|_sunfold|_unfold|_cstage\d*|_spec_\d+|_unsafe_rec|"
    r"brecOn|below|binductionOn|casesOn|recOn|rec|noConfusion|noConfusionType|ctorIdx|"
    r"injEq|inj|sizeOf_spec|_sizeOf_\d+|_sizeOf_inst|ext_iff|_auxLemma\.\d+|_simp_\d+|"
    r"_flat_ctor|_boxed|_redArg|_proof_\d+)$|\._@\.|\._redArg\.")


def validate(data):
    if (data.get("version") != 1 or not data.get("roots") or not data.get("modules")
            or not isinstance(data.get("reachable"), list)
            or not isinstance(data.get("unreachable"), list)):
        raise ValueError("incomplete proof-closure report")


def unreachable_in(data, module):
    """Declarations of one module outside the closure, without compiler auxiliaries."""
    return sorted(entry["name"] for entry in data.get("unreachable", [])
                  if entry["module"] == module and not AUXILIARY.search(entry["name"]))


def summarize(data, names=()):
    """Group the report by module; names are checked against the reachable set."""
    reachable_modules = defaultdict(int)
    reachable_names = set()
    for entry in data["reachable"]:
        reachable_modules[entry["module"]] += 1
        reachable_names.add(entry["name"])
    modules = list(data["modules"])
    outside = sorted(module for module in modules if module not in reachable_modules)
    return {
        "modules": len(modules),
        "inside": len(modules) - len(outside),
        "outside": outside,
        "declarations": len(reachable_names),
        "names": {name: name in reachable_names for name in names},
        "reachable_modules": dict(reachable_modules),
    }


def group(modules):
    """Group module names by their first two path components for a compact listing."""
    groups = defaultdict(list)
    for module in modules:
        parts = module.split(".")
        groups[".".join(parts[:2])].append(".".join(parts[2:]) or parts[-1])
    return dict(sorted(groups.items()))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-build", action="store_true")
    parser.add_argument("--root", action="append", default=[],
                        help="override the default roots (repeatable)")
    parser.add_argument("--name", action="append", default=[],
                        help="report whether this declaration is reachable (repeatable)")
    parser.add_argument("--module", action="append", default=[],
                        help="list this module's declarations outside the closure (repeatable)")
    parser.add_argument("--json", type=Path, help="also write the raw report here")
    args = parser.parse_args()
    if not args.no_build:
        subprocess.run(["lake", "build", "--wfail", "--iofail", "SP1Clean"], cwd=ROOT, check=True)
    with tempfile.TemporaryDirectory(prefix="sp1-proof-closure-") as temporary:
        output = Path(temporary) / "closure.json"
        environment = {**os.environ, "PROOF_CLOSURE_OUT": str(output)}
        if args.root:
            environment["PROOF_CLOSURE_ROOTS"] = ",".join(args.root)
        result = subprocess.run(["lake", "env", "lean", "scripts/proofClosure.lean"],
                                cwd=ROOT, env=environment, capture_output=True, text=True)
        diagnostics = result.stdout + result.stderr
        if result.returncode or diagnostics.strip() or not output.is_file():
            print(diagnostics, end="")
            print("FAIL: proof-closure report did not complete cleanly")
            return 1
        data = json.loads(output.read_text())
    try:
        validate(data)
    except ValueError as error:
        print(f"FAIL: {error}")
        return 1
    summary = summarize(data, args.name)
    if not args.root and PROOF_ONLY_MODULE not in summary["reachable_modules"]:
        print(f"FAIL: {PROOF_ONLY_MODULE} is unreachable; proof bodies were not followed")
        return 1
    if args.json:
        args.json.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    print(f"roots: {', '.join(data['roots'])}")
    print(f"{summary['declarations']} reachable declarations; "
          f"{summary['inside']} of {summary['modules']} repository modules inside the closure")
    for prefix, members in group(summary["outside"]).items():
        print(f"outside {prefix} ({len(members)}): {', '.join(sorted(members))}")
    for name, inside in summary["names"].items():
        print(f"{'inside ' if inside else 'outside'} {name}")
    for module in args.module:
        names = unreachable_in(data, module)
        print(f"{module}: {len(names)} declarations outside the closure")
        for name in names:
            print(f"  {name}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
