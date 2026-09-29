#!/usr/bin/env python3
"""Check resolved dependencies and generated provenance, independently of documentation."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
from lean_flags import load_lakefile

ROOT = Path(__file__).resolve().parents[1]


def tree_hash(root: Path) -> tuple[str, int]:
    """Hash the generated model with paths, preserving the generator's historical digest."""
    files = [root / "LeanRV64D.lean", *sorted(
        path for path in (root / "LeanRV64D").rglob("*") if path.is_file())]
    digest = hashlib.sha256()
    for path in files:
        digest.update(path.relative_to(root).as_posix().encode() + b"\0")
        digest.update(hashlib.sha256(path.read_bytes()).hexdigest().encode() + b"\n")
    return digest.hexdigest(), len(files)


def check(root: Path) -> list[str]:
    errors = []

    def require(condition, message):
        if not condition:
            errors.append(message)

    config = load_lakefile(root / "lakefile.toml")
    packages = json.loads((root / "lake-manifest.json").read_text())["packages"]
    manifest = {package["name"]: package for package in packages}
    require(len(manifest) == len(packages), "duplicate package in Lake manifest")
    requirements = config["require"]
    names = [item["name"] for item in requirements]
    require(len(set(names)) == len(names), "duplicate direct dependency")
    for package in packages:
        name = package["name"]
        require(package.get("type") == "git", f"{name}: dependency must be a git pin")
        require(bool(re.fullmatch(r"[0-9a-f]{40}", package.get("rev", ""))),
                f"{name}: resolved revision must be a full commit")
        require(package.get("inherited", False) or name in names,
                f"{name}: direct manifest package missing from lakefile")
    for dependency in requirements:
        name, revision = dependency["name"], dependency.get("rev", "")
        package = manifest.get(name, {})
        require(bool(package), f"{name}: missing resolved dependency")
        require(bool(dependency.get("git")), f"{name}: path dependencies are not reproducible")
        require(dependency.get("git", "").removesuffix(".git") ==
                package.get("url", "").removesuffix(".git"), f"{name}: repository URL mismatch")
        commit = bool(re.fullmatch(r"[0-9a-f]{40}", revision))
        require(commit or bool(re.fullmatch(r"v\d+\.\d+\.\d+(?:-rc\d+)?", revision)),
                f"{name}: use an exact commit or version tag, not a moving branch")
        require(revision == package.get("rev" if commit else "inputRev"),
                f"{name}: requested and resolved revisions disagree")

    toolchain = (root / "lean-toolchain").read_text().strip()
    require(bool(re.fullmatch(r"leanprover/lean4:v\d+\.\d+\.\d+(?:-rc\d+)?", toolchain)),
            "Lean toolchain must name an exact release")
    provenance = json.loads((root / "scripts/provenance.json").read_text())
    sail, sp1 = provenance["sail"], provenance["sp1"]
    for name, revision in [(key, sail[key]) for key in
                           ("compilerRevision", "modelRevision", "baseSnapshot")] + [
                               (key, sp1[key]) for key in ("semanticRevision", "extractorRevision")]:
        require(bool(re.fullmatch(r"[0-9a-f]{40}", revision)), f"{name}: expected full commit")
    model_hash, model_files = tree_hash(root)
    require((model_hash, model_files) == (sail["generatedTreeSha256"], sail["generatedFiles"]),
            "generated Sail tree differs from provenance; regenerate through the owned pipeline")
    config_hash = hashlib.sha256(
        (root / "scripts/sail-config/sp1_rv64d_cfg.json").read_bytes()).hexdigest()
    require(config_hash == sail["configSha256"], "Sail platform config differs from provenance")
    profile = (root / "SP1Clean/FormalModel/CoreProfile.lean").read_text()
    semantic = re.search(r'def sp1SemanticRevision : String := "([0-9a-f]{40})"', profile)
    require(semantic is not None and semantic[1] == sp1["semanticRevision"],
            "Lean semantic revision differs from SP1 provenance")
    dumps = json.loads((root / "export/sp1dump/index.json").read_text())
    require(dumps.get("sp1Commit") == sp1["extractorRevision"],
            "SP1 dumps differ from the extractor revision")

    libraries = {library["name"]: library for library in config["lean_lib"]}
    options = {name: library.get("leanOptions", {}) for name, library in libraries.items()}
    require(options.get("SP1CoreTest") == options.get("SP1CleanTest"),
            "test libraries must carry identical Lean options")
    if "LeanRV64DRvfi" in libraries:
        expected = dict(options["LeanRV64D"])
        expected["backward"] = {"do": {"legacy": True}}
        require(options["LeanRV64DRvfi"] == expected,
                "RvfiDii options must differ only by backward.do.legacy")
        require(libraries["LeanRV64DRvfi"].get("roots") == ["LeanRV64D.RvfiDii"],
                "legacy do workaround must be confined to RvfiDii")
    for name, opts in options.items():
        if name not in {"SP1CoreTest", "SP1CleanTest", "LeanRV64D", "LeanRV64DRvfi"}:
            require("linter" not in opts and "linter" not in opts.get("weak", {}),
                    f"{name}: linters belong at package level")
    return errors


def main() -> int:
    argparse.ArgumentParser(description=__doc__).parse_args()
    try:
        errors = check(ROOT)
    except (OSError, ValueError, KeyError, TypeError) as error:
        errors = [f"invalid dependency/provenance data: {error}"]
    for error in errors:
        print(f"FAIL: {error}", file=sys.stderr)
    if not errors:
        print("PASS: dependency pins, generated provenance and Lake configuration agree")
    return bool(errors)


if __name__ == "__main__":
    sys.exit(main())
