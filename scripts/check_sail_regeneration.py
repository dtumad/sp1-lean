#!/usr/bin/env python3
"""Check compiler-independent configuration and module-header controls, byte for byte."""
import argparse
import json
from pathlib import Path
import re

from check_pins import ROOT, tree_hash, validate_sail


CONFIG_SITES = {
    "LeanRV64D/PlatformConfig.lean": ("def plat_have_clint", "def plat_have_sig"),
    "LeanRV64D/ValidateConfig.lean": ("let clint_supported", "let sig_supported"),
}

# The current model also embeds these configuration reads in its MMIO validation.
# Match the surrounding expression within this one function, never arbitrary Booleans.
MMIO_CONFIG_SITES = (
    "if (((true : Bool) && ((Sail.BitVec.extractLsb plat_sig_base",
    "let valid : Bool :=\n    if ((true : Bool) : Bool)",
    "(if ((not (true : Bool)) : Bool)",
    "let _ : Unit :=\n    if ((true : Bool) : Bool)",
)


def replace_once(source, old, new):
    if source.count(old) != 1:
        raise ValueError(f"Missing or ambiguous config site: {old}")
    return source.replace(old, new, 1)


def sp1_configuration(source, name):
    for site in CONFIG_SITES.get(name, ()):
        source = replace_once(source, site + " : Bool := true", site + " : Bool := false")
    if name == "LeanRV64D/PlatformConfig.lean":
        for extension in ("Zicntr", "Sdtrig"):
            source = replace_once(source, f"  | .Ext_{extension} => true",
                                  f"  | .Ext_{extension} => false")
    if name == "LeanRV64D/ValidateConfig.lean":
        sdtrig_site = """  if ((true : Bool) : Bool)
  then
    (let valid : Bool :=
      if (((true : Bool) && (not (true : Bool))) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "The `hcontext` CSR is supported but the H extension is not: `hcontext` requires H to be supported.")"""
        source = replace_once(source, sdtrig_site, sdtrig_site.replace("true", "false", 1))
        match = re.search(r"^def check_mmio_devices .*?(?=^def |\Z)", source, flags=re.M | re.S)
        if match is None:
            raise ValueError("Missing MMIO configuration validation")
        body = match.group()
        for site in MMIO_CONFIG_SITES:
            body = replace_once(body, site, site.replace("true", "false", 1))
        source = source[:match.start()] + body + source[match.end():]
    return source


def sources(root):
    paths = [root / "LeanRV64D.lean", *sorted((root / "LeanRV64D").rglob("*"))]
    if root.is_symlink() or any(path.is_symlink() for path in paths):
        raise ValueError("Sail controls must not contain symlinks")
    return {path.relative_to(root).as_posix(): path.read_text()
            for path in paths if path.is_file()}


def legacy_headers(source):
    if not source.startswith("module\n\n") or source.count("@[expose] public section\n\n") != 1:
        raise ValueError("Unexpected generated module header")
    source = source.removeprefix("module\n\n").replace("@[expose] public section\n\n", "", 1)
    return re.sub(r"^public import ", "import ", source, flags=re.M)


def check_matrix(stock, sp1, stock_module, sp1_module):
    controls = [sources(path) for path in (stock, sp1, stock_module, sp1_module)]
    a, b, c, d = controls
    if not a or any(set(control) != set(a) for control in controls):
        raise ValueError("Sail control file inventories differ")
    if not set(CONFIG_SITES) <= set(a):
        raise ValueError("Missing platform configuration controls")
    for name, source in a.items():
        expected = sp1_configuration(source, name)
        if expected != b[name]:
            raise ValueError(f"Unexpected stock/SP1 body delta: {name}")
        if legacy_headers(c[name]) != source or legacy_headers(d[name]) != b[name]:
            raise ValueError(f"Module mode changed generated bodies: {name}")


def check_stock(path, pins, key="currentStock"):
    stock = pins[key]
    validate_sail(path, {**stock, "moduleSystem": False})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["stock", "previous-stock", "matrix"])
    parser.add_argument("paths", type=Path, nargs="+")
    args = parser.parse_args()
    pins = json.loads((ROOT / "scripts/provenance.json").read_text())["sail"]
    if args.mode in {"stock", "previous-stock"}:
        if len(args.paths) != 1:
            parser.error("stock requires one directory")
        check_stock(args.paths[0], pins, "previousModelStock" if args.mode == "previous-stock" else "currentStock")
    else:
        if len(args.paths) != 4:
            parser.error("matrix requires stock, SP1, module stock, module SP1 directories")
        check_stock(args.paths[0], pins)
        validate_sail(args.paths[3], pins)
        check_matrix(*args.paths)
    for path in args.paths:
        print(f"Verified {path}: {tree_hash(path)}")
    print("PASS: Sail regeneration controls")


if __name__ == "__main__":
    main()
