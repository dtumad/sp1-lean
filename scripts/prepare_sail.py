#!/usr/bin/env python3
"""Prepare the fingerprinted Sail model outside Git before invoking Lake.

A valid existing tree or --from tree is reused only after checking every byte against
provenance. Otherwise build the pinned generator and regenerate. --force exercises that
fallback even with a warm cache; --check never downloads or generates anything.
"""

import argparse
import fcntl
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

from check_pins import ROOT, SAIL_MODEL_DIR, validate_sail as validate


def install(source, destination, pins):
    validate(source, pins)
    destination.parent.mkdir(parents=True, exist_ok=True)
    # Stage and verify before replacing an earlier generated tree. Never delete the source.
    with tempfile.TemporaryDirectory(prefix="sail-stage-", dir=destination.parent) as temporary:
        staged = Path(temporary) / "model"
        staged.mkdir()
        shutil.copyfile(source / "LeanRV64D.lean", staged / "LeanRV64D.lean")
        shutil.copytree(source / "LeanRV64D", staged / "LeanRV64D")
        validate(staged, pins)
        backup = Path(temporary) / "previous"
        if destination.exists() or destination.is_symlink():
            destination.rename(backup)
        try:
            staged.rename(destination)
        except BaseException:
            if backup.exists() or backup.is_symlink():
                backup.rename(destination)
            raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--from", dest="source", type=Path, help="use a fingerprinted generated tree")
    mode.add_argument("--force", action="store_true", help="regenerate even with a valid cache")
    mode.add_argument("--check", action="store_true", help="verify the prepared tree only")
    args = parser.parse_args()
    pins = json.loads((ROOT / "scripts/provenance.json").read_text())["sail"]
    destination = ROOT / SAIL_MODEL_DIR
    destination.parent.mkdir(parents=True, exist_ok=True)
    with (destination.parent / "sail.lock").open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if args.check:
            validate(destination, pins)
        elif args.source:
            install(args.source.resolve(), destination, pins)
        else:
            try:
                validate(destination, pins)
                cached = True
            except (OSError, ValueError):
                cached = False
            if args.force or not cached:
                work = Path(os.environ.get("SAIL_GEN_DIR", str(ROOT / ".lake/sail-gen"))).resolve()
                environment = {**os.environ, "SAIL_GEN_DIR": str(work)}
                generator = ROOT / "scripts/sail-config/generate_lean_rv64d.sh"
                subprocess.run([str(generator), "--deps"], env=environment, check=True)
                subprocess.run([str(generator), "--sp1"], env=environment, check=True)
                install(work / "sail-riscv/build/model/Lean_RV64D", destination, pins)
        print(f"PASS: prepared {pins['generatedFiles']} Sail modules ({pins['generatedTreeSha256']})")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"FAIL: Sail preparation: {error}", file=sys.stderr)
        sys.exit(1)
