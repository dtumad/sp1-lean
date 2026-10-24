# Generated Sail model

The LeanRV64D library is generated under `.lake/generated/sail`, outside Git and never hand-edited.
The pinned Sail compiler and
sail-riscv sources run with the checked-in SP1 platform configuration. Inputs, base snapshot,
OCaml version and output fingerprints have one owner:
[provenance.json](../../scripts/provenance.json). Lake's Sail dependency records the runtime.

## Semantic configuration

[sp1-overlay.json](../../scripts/sail-config/sp1-overlay.json) disables two devices SP1 does not
implement: CLINT and the simple interrupt generator. Their stock address windows lie inside the
native memory interval. Leaving them enabled would route permitted RAM accesses through MMIO and
make the memory-bridge lemmas false as stated.

The two keys affect four generated sites: plat_have_clint / plat_have_sig in PlatformConfig, and
clint_supported / sig_supported in ValidateConfig. Other platform restrictions remain explicit
configured-state hypotheses. In particular PMP uses the stock 16 entries with every entry OFF
as a Lean state condition, not a generator patch. Moving a condition from configuration to Lean
makes it visible; it does not remove the assumption.

## Reproduce

Run `python3 scripts/prepare_sail.py` before Lake. It checks a restored source cache against the
recorded tree fingerprint, or builds the pinned compiler and regenerates. `--from DIRECTORY`
accepts another generated tree only with that same check; `--force` exercises regeneration.
`--check` verifies existing output without downloading or generating anything.

The [generator](../../scripts/sail-config/generate_lean_rv64d.sh) requires opam, CMake, Z3,
Python, Git, a C compiler, GMP, pkg-config, zlib and m4. Its work directory and isolated opam root
default to `.lake/sail-gen`; `SAIL_GEN_DIR` overrides the directory. CI installs these prerequisites
on a cache miss. Generated sources are portable; compiler caches are specific to their platform.

| Mode | Action |
|---|---|
| --deps | Prepare the pinned OCaml/Sail toolchain |
| --make-config | Deep-merge stock generated configuration with the SP1 overlay |
| --stock | Regenerate and require byte identity with the pinned base snapshot |
| --sp1 | Regenerate with SP1 configuration and verify the recorded fingerprint |
| --generate | Generate a candidate and print its fingerprint for explicit review |

The SP1-config path currently copies the configuration into the upstream build and checks its
hash before/after generation. Replace that workaround when the selected upstream build supports
an equivalent config override without changing model identity.

## Update the pair

1. Select compatible compiler, model, base snapshot and runtime revisions. Update provenance and
   the single Lake requirement deliberately; do not run bare lake update.
2. Verify --stock, regenerate the configuration, inspect the platform delta and run --generate.
3. Review the generated diff and update generatedTreeSha256, generatedFiles and configSha256.
   scripts/check_pins.py uses a deterministic path/content tree hash; import its tree_hash helper
   when recording a newly reviewed snapshot.
4. Run --sp1 and prepare_sail.py, strict full build/tests, conformance and compiled trust checks. Expect proof updates
   where Sail internals changed; do not paper over them with new assumptions.
5. Record commands and generator environment with the PR evidence.

Sail regeneration CI independently checks configuration and byte identity. The normal pin check
requires prepared output; `--source-only` checks input pins without it in lightweight source/Rust
jobs. Fingerprints authenticate the reviewed snapshot; fresh regeneration supplies independent
evidence. Neither the preparation script nor a cache restore updates the expected fingerprint.

The compiler carries only upstream Sail #1742's module-header patch on the existing compiler
base; the runtime carries lean-sail #13. Both use published immutable revisions. Consume compatible
upstream revisions when those changes merge. The module migration preserves generated bodies.

The narrow RvfiDii legacy-do Lake library is a temporary elaboration workaround (#6), not a
generated-source modification. Coordinate its replacement with module-system support (#33);
both require a compatible runtime/generator pairing.
