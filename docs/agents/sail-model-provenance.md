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

The overlay also disables Zicntr, whose counter-reading instructions are outside the SP1 profile.
The current upstream configuration validator requires CLINT as the time source when Zicntr is
enabled. Keeping Zicntr enabled with CLINT disabled would therefore select a rejected platform.
The overlay also disables Sdtrig, which SP1 does not implement. Its new hardware-breakpoint
checks can otherwise trap before an instruction executes for register states allowed by the
existing SP1 contract. Disabling the extension preserves that domain without adding a
caller-supplied trigger-inactivity premise.
The model integration carries [sail-riscv #2097](https://github.com/riscv/sail-riscv/pull/2097), which removes the disabled branch's assertion about
`written_trigger_index`. That marker belongs to trigger bookkeeping; inspecting it when Sdtrig
is absent would still reject otherwise admissible SP1 states. Enabled trigger behavior is
unchanged. This source patch must be retired when upstream supplies the same disabled-extension
behavior; generated output continues to come exclusively from the pinned source pipeline.
The four switches affect eleven generated sites in PlatformConfig and ValidateConfig, including
the MMIO validation branches. All other stock settings, including H, remain unchanged.

Normal retirement retains upstream's interrupt refresh and event bookkeeping: `mip` is refreshed
before execution, and `written_event_index` is cleared afterward. Row effects and trace endpoints
record their exact values separately from the preserved-register frame. Repeated refreshes are
idempotent while `misa` and `hvip` remain fixed; empty and host-only segments preserve the original
values. No initial-value restriction on either bookkeeping register is required.

Other platform restrictions remain explicit
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
| --stock | Verify current stock; `SAIL_GEN_PROFILE=historical` reproduces the independent base snapshot, and `previous` runs the preceding model with the current compiler |
| --generate-stock | Generate current stock output for explicit fingerprint review |
| --legacy-sp1 / --stock-module | Generate the other two configuration/module controls |
| --sp1 | Regenerate with SP1 configuration and verify the recorded fingerprint |
| --generate | Generate a candidate and print its fingerprint for explicit review |

The SP1 configuration is passed through `SAIL_FORMAL_CONFIG_RV64D`, preserving the generated
package and namespace identity. The model integration carries sail-riscv #1861 for this CMake
interface; consume an upstream revision when it merges. The generator checks the selected
configuration's hash before and after generation and clears the override for stock controls.

## Update the pair

1. Select compatible compiler, model and runtime revisions. Update provenance and
   the single Lake requirement deliberately; do not run bare lake update.
2. Reproduce the historical stock control with `SAIL_GEN_PROFILE=historical` (a separate toolchain cache).
   Generate the previous-model stock control with the current compiler and review the compiler
   delta. Generate current stock with `--generate-stock`, review the model delta and record `currentStock`.
   Regenerate the configuration, inspect the platform delta and run `--generate`.
3. Review the generated diff and update generatedTreeSha256, generatedFiles and configSha256.
   scripts/check_pins.py uses a deterministic path/content tree hash; import its tree_hash helper
   when recording a newly reviewed snapshot.
4. Run --sp1 and prepare_sail.py, strict full build/tests, conformance and compiled trust checks. Expect proof updates
   where Sail internals changed; do not paper over them with new assumptions.
5. Record commands and generator environment with the PR evidence.

Sail regeneration CI checks four current-compiler outputs (stock/SP1 × legacy/module).
`scripts/check_sail_regeneration.py` permits exactly the eleven documented Boolean changes
and reverses only the generated module/import/exposure headers. All remaining bytes and
file inventories must agree. The historical compiler must independently reproduce the
opencompl snapshot; it owns its compiler/model/base-snapshot revisions independently of current
pins. The previous-model control shares the historical model and the current compiler, so the
compiler and model deltas are archived separately, without normalization.
These controls test reproducibility and bounded configuration changes, not compiler correctness.

Sail regeneration CI independently checks configuration and byte identity. The normal pin check
requires prepared output; `--source-only` checks input pins without it in lightweight source/Rust
jobs. Fingerprints authenticate the reviewed snapshot; fresh regeneration supplies independent
evidence. Neither the preparation script nor a cache restore updates the expected fingerprint.

The compiler carries the module-header adaptation from Sail #1742 on the active `sail2` branch.
The runtime carries lean-sail #13, the inclusive finite-range correction (#18), and explicit
loop-limit failures (#21), and ArchSem composition laws (#23). Exhausting a bounded loop produces a Sail assertion error; successful
execution proofs must not assume a loop returns normally merely because its body does.
Both integrations use published immutable revisions. Generated declarations
now live directly in `LeanRV64D`; `LeanRV64D.Defs` remains a module filename, not a declaration
namespace. The generator also adjusts supplementary files that opened the former namespace.
Consume compatible upstream revisions when these adaptations merge.

Lean 4.35 rejects a flat variant with more than 244 constructors carrying fields during layout
computation, including noncomputable declarations. The generator splits large variants into
nonrecursive chunks and exposes the original constructor names as match-pattern abbreviations.
Every alternative and its arguments remain represented, and exhaustive matches still cover all
alternatives. This is a generator-owned representation workaround; remove it when the pinned Lean
compiler supports the original flat variants. The generator's large-union regression covers the
chunk boundary with generic constructor payloads and consumer-derived structural equality. Sail
forbids recursive source types, so the chunks are emitted in dependency order without a mutual
block. The fix is proposed in Sail #1823. Sail #1824 reruns recursion analysis after mutual-recursion
specialization, removing stale termination measures only where recursion has disappeared;
this keeps the current page-table model warning-free without changing its function bodies.
Generated instruction matches and the complete model must also compile before a
replacement is accepted.

The narrow RvfiDii legacy-do Lake library is a temporary elaboration workaround (#6), not a
generated-source modification. Coordinate its replacement with module-system support (#33);
both require a compatible runtime/generator pairing.
