# AGENTS.md

Guidance for AI agents working in this repository (`sp1-clean-native`).
`CLAUDE.md` is a one-line pointer to this file so Claude Code auto-loads it.

## What this repo is

A **Clean-native, semantically-specified** formal verification of SP1's RISC-V chips, built on the
**public** Clean DSL. The stable verification boundary is the **whole chip**:

1. proof-oriented Lean gadgets (`Native/Operations/` + local `Proofs/Operations/` lemmas) implement
   semantic arithmetic and are composed as true Clean subcircuits;
2. a native `GeneralFormalCircuit` chip has its own row type and semantic contract on the
   `FormalModel/Contracts/` audit surface;
3. a native Sail bridge proves that chip contract reaches the RISC-V Sail spec;
4. extraction supplies the complete Rust chip row, `assertZero` list, interaction list, and whole-chip
   populate traces; `Faithful/ChipOracle.lean` maps the native row to the Rust row and `ChipFaithful`
   compares the two complete assertion systems and interaction multisets.

Rust operations and Lean gadgets are complementary, not corresponding proof objects. They may use
different structs and decompositions. Do not add new operation-level faithfulness anchors,
Rust-generated circuits, or operation witness batteries. The direct-to-circuit generator and
`Extracted/Circuit/` have been removed; native circuit definitions are hand-maintained under `Native/`.
**The whole-chip oracle migration is complete (2026-07): all 25 supported instruction chips have
native rows, `Extracted/ChipOracle/<Chip>.lean` oracles, and native-row `ChipFaithful` proofs**;
`Faithful/SupportedMachine.lean` ties that proof-bearing index to the exact upstream
instruction-table profile. The remaining flat `Extracted/<Op>.lean` modules and per-op/reader
`Faithful/` anchors are deliberate **shared substrate** — canonical statement targets that multiple
chip oracles reference through one-line namespace bridges — not migration debt.

This project is **independent** of `sp1-lean`. It does **not** import `SP1Foundations`/`SP1Operations`/
`SP1Chips`/`SP1Clean` (those are 4.29 oleans — cross-toolchain), and does **not** use the legacy structural `correct_*` / `SailBridge` /
`fromMain`/`toMain` pattern. Needed foundations are re-created here (`Math/` + `Model/`). Every released
theorem must be proof-complete: no `sorryAx`. Pure chip/AIR proofs should normally show only
`[propext, Classical.choice, Quot.sound]`; selected `bv_decide` lemmas and the generated Sail target's
platform hooks are separately disclosed by the axiom census.
`update_extracted.py` and `scripts/update_sp1_dumps.sh` do invoke SP1's constraint compiler and
trace-dump tooling as trusted, pin-checked Rust oracles; generated outputs are never treated as
self-authenticating.

The SP1 Rust source lives in a sibling `sp1` checkout. Regeneration points `SP1_DIR` at a clean
checkout of the pinned extraction branch described in `docs/agents/extraction.md` (a committed
descendant of the unmodified semantic tag; no uncommitted-patch mechanism). The 4.29 `sp1-lean` repo is a read-only reference for porting (a sibling
`sp1-lean` checkout); its arithmetic/Sail proofs are the thing we re-derive natively here, not import.

### Larger verified-verifier program

This repository is presently the **AIR-to-execution** workstream, not yet an implementation of SP1's
cryptographic proof verifier. Keep the eventual claim split into three independently auditable layers:

1. an executable Lean `verifyCore` that agrees with the pinned Rust verifier on structured real proofs;
2. ArkLib knowledge soundness for the transcript, LogUp GKR, zero-check, PCS, commitments, and
   Fiat--Shamir transformation, yielding an extracted full AIR witness with an explicit error bound; and
3. `sp1_air_sound`, turning that faithful full AIR witness into the official Sail execution relation.

The final `sp1_verifier_sound` must be probabilistic/knowledge-soundness-shaped; do not claim the
unconditional deterministic implication `verifyCore = true -> exists valid execution` without the
cryptographic assumptions and error term. Completeness is a separate companion theorem.

These layers are parallel workstreams and may be owned by different developers. Core, Compressed,
Plonk, and Groth16 are separate verifier targets; pin **Core** first. Parsing may initially be delegated
to a canonical Rust exporter so it does not obscure the verifier/refinement boundary.

**This workstream's current priority:** close native Clean soundness/completeness for arbitrary
bounded local execution segments, with authenticated complete boundaries, all eight constrained
host calls, native shard composition, and generic whole-ensemble export. Boot-to-HALT is an
endpoint corollary. Work from the checked end-to-end targets in `FormalModel/Shard.lean` and
`Soundness/Shard/Contract.lean`; their concrete semantic resource profile and implementation
instances remain open. Do not add compiler readiness, provider validity, grounding, or syscall
inactivity as caller premises of the final capstone.

`Model/Core/Execution{,Path,Replay,Boot,Snapshot}.lean` owns complete Sail/host/clock semantics.
Reuse its paths and finite boundaries, the shared `ExecutionCarrier`/`CoreExecutionTrajectory`,
and the existing decoder, routing, access plans, and compiler. The older `CoreShardSemanticWitness`
is a legacy ordinary/exact-Core view, not a second full-state model. Keep the native profile's
ROM/host strengthening separate from the unchanged 25 whole-chip Rust faithfulness anchors.

Current proof scope, the next obligation, durable semantic findings, and acceptance gates live in
[docs/roadmap.md](docs/roadmap.md); module ownership and trust boundaries live in
[docs/architecture.md](docs/architecture.md) and [docs/layering.md](docs/layering.md).
Update that status in one place rather than appending a development log here. The full mixed
outgoing-state/Exit theorem, all-eight-call installation, and constructive completeness remain
open. `sp1_air_sound` and `sp1_air_refinement` also remain reserved for a closed exact-upstream
refinement; only their `_of_obligations` combinators are currently declared.

## Build

- Core build: `lake build` (the default targets `SP1Core`, `ToClean`, `ToMathlib`, `ToPolyFun`:
  the generic and semantic layers plus the chip circuits and their proofs — strata 0–6 of
  `scripts/layering.txt`, reached through the root index `SP1Clean/Core.lean`). Full build:
  `lake build SP1Clean` (the umbrella index `SP1Clean.lean` = `SP1Clean.Core` + the SP1-alignment
  layers `Extracted/{ChipOracle,SystemOracle}`, `Faithful/`, `Alignment/`, `Proofs/Sail`,
  `Proofs/Completeness`, `Soundness/`, `Composition/`). **Wire every new module into
  `SP1Clean.lean`, and a core module into `SP1Clean/Core.lean` as well** — `scripts/check_root_index.sh`
  and `scripts/check_layering.sh` (check 3) gate both. PR CI runs the core; the alignment workflow
  (`.github/workflows/alignment.yml`, weekly/on demand/on `main`) runs the full build, `lake lint`,
  the full test library, the conformance gates, and both censuses.
  Passing = **0 errors AND 0 warnings**, and **no stray `info:` notes**: CI builds with
  `lake build --wfail --iofail`, so a linter warning or an `info:` note (see the `ring` note below)
  fails the job — use the same flags locally. Neither target carries `native_decide` (gated by
  `scripts/check_no_native_decide.sh`).
- Tests: `lake test` (the `SP1CoreTest` `testDriver`: the test modules whose import closure stays in
  the core). The full library `lake build SP1CleanTest` (alignment workflow) adds the anchors under
  `SP1CleanTest/Alignment/`, moved there by import closure. Together they build/elaborate the exportability battery and
  the non-vacuity/real-row satisfiability anchors — including the active official-Sail-step ↔
  deterministic-compiler ↔ circuit-event regression — and is the project's **only**
  `native_decide`. Runs on top of the cached main-library oleans (the test lib imports `SP1Clean`,
  never vice-versa). Trace
  conformance against SP1's real prover is the separate dump-anchored pipeline
  (`export/sp1dump/` + the `--testdata` generation-time gate + `scripts/run_interp_diff.sh`).
- Single file: `lake env lean SP1Clean/Proofs/Chips/AddChip/Formal.lean` (elaborates against the
  **already-built** oleans). ⚠ `lake env` only sets the environment — **it does not build anything**.
  If you have edited a dependency, its olean is stale and this command silently checks against the
  *old* one. Run `lake build <Dep.Module>` first, or finish with `lake build SP1Clean`.
  ⚠️ `lake env lean <file>` **exits 0 even on a Lean stack overflow**, and a stale cached olean can make
  downstream checks pass falsely — **always finish a phase with `lake build SP1Clean`**.
- **Build concurrency.** Elaboration is heavy (full build is ~1800+ jobs across Clean + mathlib + Sail; the
  `toBitVec64`/carry proofs are the slowest). Before starting a new build, **let the running one
  finish or kill it** (`pkill -f "lake build"` / `pkill -f "lake env lean"`). Cap at **2–3 builds at once**.
  A `run_in_background` build can outlive its shell — check with `ps -ef | grep -E "lake|lean" | grep -v lsp`
  before spawning another. The lean LSP server (`uvx lean-lsp-mcp`) also keeps several GB warm.
  **There is no `-j` option** in Lake here (only `-J/--json`; re-verified at v4.32.2) — serialise by not
  running anything else.
- **Process hygiene.** *LSP file workers* (`lean --worker …`, children of `lean --server`) leak and hold GB
  after an agent exits; `pkill -f "lean --worker"` is the correct reaper. **Never kill `lean --server` /
  `lake serve`** — that is the `lean-lsp` MCP server, and killing it drops the MCP connection for the whole
  session. *Build workers* carry no `--worker` token, so use `ps -ef | grep tstack` for build liveness, and
  `sample <pid>` (not RSS — a healthy run also plateaus at ~3.2 GB) to tell a hang from progress.
- **Toolchain:** `lean-toolchain` and mathlib are `v4.33.1`; Clean is upstream `main`
  (`fba2a29f`, module-ified — the package sets `allowNonModules = true` until the `SP1Clean/`
  tree migrates) with its `CompPoly` dependency; PolyFun is `997828ce` (its last v4.33.1
  commit); lean-sail is the documented temporary pin `dtumad/lean-sail` `sp1-pin` (= `v5` + the
  one-line `ambiguousOpen` fix of rems-project/lean-sail#14, re-pinned to upstream when that
  merges). **Every dependency is an immutable git pin** — there are no path dependencies, so a
  clean clone builds. The Sail RV64 model is the
  in-tree **generated** library `LeanRV64D/` + `LeanRV64D.lean` (its own `lean_lib`, never
  hand-edited, outside every hand-written-source guard like `Extracted/`): pinned Sail sources run
  against the checked-in SP1 platform config, written by
  `scripts/sail-config/generate_lean_rv64d.sh --install` and gated by the tree hash in
  `scripts/check_pins.sh` plus byte-identity with a fresh regeneration in
  `.github/workflows/sail-regen.yml` (`docs/agents/sail-model-provenance.md`). **Do not run bare
  `lake update`** (it may advance dependencies/toolchains) — update one `[[require]]` at a time.
  ⚠ **The generated Sail model and the `lean-sail` runtime must move together.** A v4-generated
  `LeanRV64D` tree against `lean-sail` v5 fails with `unknown namespace Sail.ConcurrencyInterfaceV2`;
  regenerate and re-pin from the same pairing (`docs/agents/sail-model-provenance.md` records the
  current one).
  Read `docs/agents/lean-sail-notes.md` before touching any dependency.
- Lake options already set in `lakefile.toml`: `--tstack=400000`; `autoImplicit = false` (every
  binder is written; the generated Sail model overrides it); `synthInstance.maxHeartbeats` is the default.
- **Lean ≥ 4.33 landmines** (`docs/agents/proof-patterns.md` § "Lean ≥ 4.33 and Clean `main`"): the
  unifier type-checks metavariable assignments at implicit transparency, so `rw`/`simp` through a
  `def` that only unfolds at default (`component.Input` vs `Inputs`, `id.Occurrence` vs the entry
  type, a `change` to a defeq-but-not-syntactic target) fails with "not type-correct under the
  implicit transparency level" — name the argument, make the typing `def` `@[reducible]`, or rewrite
  by lemma; Clean seals `structToElements`, so cells are read through `structToElements_eq`, never
  `rfl`; a `native_decide` statement carries no `let`; every hand-written `ElaboratedCircuit`
  obligation proof opens with `preserve_tactic_target`.
- There are no conventional unit tests in the main library; correctness lives in kernel-checked
  soundness/faithfulness/bridge theorems. `lake test` is the separate executable conformance layer.

## Architecture

Mirror-rust layout under `SP1Clean/`:

- **`Math/`** — general math, no SP1/Sail deps: `Word.lean` (`Word`, `toBitVec64`, `isU64`, `val_65536_*`,
  `limb_lift`), `Bitwise.lean` (`byteOp`, `reassemble_byteOp`, …), `Misc.lean`, `MulCarryChain.lean`,
  `HWord.lean`. (`GetElemFastPath.lean` moved out to `ToClean/Tactic/`; its upstream is Lean core/Std.)
- **`Model/`** — the SP1 substrate (Sail + buses): `Register.lean`, `SailWrap.lean`, `SailMemory.lean`,
  `BusMessages.lean` (the State/Memory/Program message structs + their structural per-row predicates —
  incl. `MemoryMsg.ClkBound` and the reader-level `Readers.ClkDiscipline`, the memory-clock discipline),
  `Channels.lean` (plain Clean channels: State `True`, Program `RowSpec`, Memory `isU64 ∧ ClkBound`,
  Byte `ByteRowSpec`),
  `InteractionBus/Projection/Recovery.lean`, `SP1Constraint.lean`, `ByteTable.lean`, and
  the **semantic-execution substrate** `Semantics/` — `GuestProgram.lean` (the `GuestProgram` +
  `IsInitialState`/`SailStep`/`SailChain`/`SP1Halted` Sail execution model), `ProgramCommitment.lean`
  (`progOf : ProverData → GuestProgram`, the committed program), `MicroTime.lean` (bus-clock ↔ step
  correspondence, `MemLoc`, `chainState`, `microValue`), and `Truth.lean` (`LocalStateTruth`/`LocalMemTruth`/
  `ProgTruth`, the global execution predicates derived by grounding, not channel payloads). (`Math` +
  `Model` are the former `Foundations/`, split by SP1-dependence.) `Model/Machine/{Schedule,Syscall,
  EventExecution}.lean` gives the row-dependent 8/264-tick event semantics and explicit SP1 host-handler
  boundary.
- **`Extracted/`** — the "extracted from Rust" pillar, **auto-generated, do not hand-edit**. The
  inventory: 25 whole-chip oracles (`ChipOracle/<Chip>.lean` — the chip-namespaced Rust row +
  complete `asserts`/`interactions`), 12 system tables (`SystemOracle/<Table>.lean`), the shared
  flat modules (canonical readers, the `MemoryAccess` struct carrier, shared operations that
  multiple chips' bridge lemmas cite), and the fail-closed Core manifest/provenance. No legacy
  `<Chip>Chip.lean` files remain. Extraction never emits a Clean circuit. All generated files are
  regenerated by `update_extracted.py` (kept at the repo root deliberately — it is the pipeline's
  single entry point and the path every generated header and doc cites).
- **`FormalModel/`** — the central audit surface (the "middle ground" between `Extracted` and the proofs):
  `Contracts/` holds the per-reader/operation/chip `Inputs` + semantic `Spec`s (`Readers.lean`,
  `Operations.lean`, `Chips.lean`, plus focused rich contracts such as `DivRem.lean`) and the lifted chip `Assumptions`/`ProverAssumptions`
  (`ChipAssumptions.lean` — Add/Addi/Addw/Sub/Subw/UType; the two-reason keep-list taxonomy for the
  other chips is stated in that file's module docstring). `ProverSpec` is uniformly
  `fun _ _ _ => True` (inline in each `circuit` bundle). `Trace/Witness.lean` holds the non-vacuity
  examples; reusable configured-state construction lives in `Model/Machine/ConfiguredState.lean`,
  and `Model/Core/Boot.lean` proves initialization for every checked finite image. The native
  initial-memory byte/word contracts live in `Contracts/InitialMemory{,Read}.lean`, with concrete
  sparse interval tables under `Model/Core/` and circuits in `Native/Operations/InitialMemory{Lookup,Read}.lean`;
  `Contracts/MemoryBoundary.lean` and `Contracts/OrderedInitialProvider.lean` expose the native
  providers' boot-value, query-address, and control-key contracts. Their implementations are in
  `Proofs/Chips/{InitialRamProvider,InitialRegisterProvider,OrderedInitialProvider}.lean`, with
  `Native/Operations/OrderedBoundary.lean` supplying the strict control link and
  `Soundness/InitialMemoryBoundary.lean` deriving uniqueness from endpoint balance.
  `Soundness/InitialMemoryEnsemble.lean` registers the providers and terminal table with fixed
  control endpoints; `Soundness/OrderedBoundaryEnsemble.lean` derives endpoint balance from the
  actual Clean ledger. The subsystem proves authentic records and per-location uniqueness from
  local table specifications and balance; deriving those local specifications in the enclosing
  machine and connecting grounding remain integration work. Final register/RAM circuits in
  `Proofs/Chips/{FinalRegisterProvider,FinalRamProvider,OrderedFinalProvider}.lean` instantiate the
  same ordering machinery through `Soundness/FinalMemoryEnsemble.lean`. Shared circuit and inventory
  proofs live in `OrderedMemoryProvider` and `OrderedMemoryEnsemble`; both subsystems identify their
  decoded records with the actual physical Memory ledger and derive per-location uniqueness.
  Finalizers receive value/clock guarantees from the Memory bus; last-access meaning remains a
  global grounding conclusion. These are not yet the providers of `sp1Ensemble`;
  the guest-program execution model (`GuestProgram`, `IsInitialState`, `SailStep`/`SailChain`,
  `SP1Halted`, `exitOf`) lives in `Model/Semantics/GuestProgram.lean`. Relation-level AIR/verifier
  contracts live in `Relations.lean`, `CoreProfile.lean`, `CoreAIRRelation.lean`, `Execution.lean`, and
  `Verifier.lean`; `ChipRow`-dependent decode,
  routing, and grounding arguments remain naturally in `Soundness/`.
- **`Native/`** — the "implemented native in Lean" pillar (circuit construction): `Native/Chips/<Op>Chip/Defs.lean`
  (each chip's `main` + `ElaboratedCircuit` — 22 of the 25 chips; the ShiftLeft/ShiftRight/DivRem
  `main`s live in `Proofs/Chips/<X>Chip/Defs.lean`, the documented proof-decomposition exception),
  `Native/Operations/<Op>/{Populate,RawSpec}.lean` (witness +
  native arithmetic core) + flat ops (`BitwiseU16Operation.lean`, `AddressOperation.lean`, …), and
  `Native/Readers/*.lean` (the register/state reader circuits — their `Spec`s are in
  `FormalModel/Contracts/Readers.lean`; the readers' local `SpecD`/`AssumptionsD`/`ProverAssumptionsD`
  are the **`D`-suffix convention**: the `ProverData`-threading lifts of the plain contract
  predicates, e.g. `SpecD input _ data := Spec input`, wrapping a Contracts-layer predicate into the
  `GeneralFormalCircuit` signature). Operation circuit definitions are hand-maintained in
  `Native/Operations/<Op>/Defs.lean` when they are not flat single-file operations.
- **`Proofs/`** — the "proven sound/complete" pillar: `Proofs/Chips/<Op>Chip/{Formal,Complete,…}.lean`
  (each chip's Sail bridge and machine contracts, `Bridge.lean`/`Contracts.lean`, live under
  `Alignment/Chips/<Op>Chip/` with their namespaces unchanged, because they import the machine
  layer and belong to the alignment build target)
  (soundness/completeness/`circuit` + the Sail bridge; the `Spec` is in `FormalModel/Contracts/Chips.lean`,
  the ALU chips' `Assumptions`/`ProverAssumptions` in `Contracts/ChipAssumptions.lean`),
  `Proofs/Operations/<Op>/Formal.lean` (the `FormalAssertion` soundness/completeness). Flat receiver
  infra (`ByteChip`/`ProgramChip`/`MemoryProvider`) sits in
  `Proofs/Chips/`. Complex chips may decompose proofs without changing their public chip boundary.
  DivRem is the reference: `FormalModel/Contracts/DivRem.lean` defines four semantic families,
  `Proofs/Chips/DivRemChip/Cases.lean` proves circuit-independent evidence-to-ISA lemmas, and the sole
  heavy arithmetic seam is the whole-chip `evidenceSoundness` theorem in `Formal.lean`.
- **`Faithful/`** — the "proven faithful" pillar: `ChipOracle.lean` plus the 25 whole-chip
  native↔Rust anchors (reconfigure-based oracles; the dump-anchored trace gate audits the
  reconfigure maps cell-for-cell). The per-operation/reader anchor files that remain are shared
  substrate: their lemmas are the canonical statements the chip anchors cite via namespace
  bridges (each has ≥2 live importers — verified in the 2026-07 retirement sweep).
- **`SP1CleanTest/`** (top-level, **not** under `SP1Clean/`) — the **test library**, the sole home of
  `native_decide` and the `lake test` target (`testDriver`). It imports the main `SP1Clean` library and
  is never imported by it, so the default `lake build SP1Clean` stays `native_decide`-free (enforced by
  `scripts/check_no_native_decide.sh`; `native_decide` trusts the whole compiler — since v4.32 the census
  shows this as generated `._native.native_decide.ax_*` constants, the successors of the named
  `Lean.ofReduceBool`/`Lean.trustCompiler` axioms). Contents: `Exportable.lean` (the
  `#assert_exportable` battery using the canonical `Model/SP1Field.lean` `SP1Prime`), `NonVacuity.lean` /
  `NonVacuityReal.lean` (satisfiability anchors for the chip `Assumptions` — the real-row battery
  builds rows through `TraceGenTests/EventPopulate.lean`), `Audit/` (the joint-premise regression),
  and `TraceGenTests/{TraceGenerator,EventPopulate,Conformance}.lean` — the
  **circuit-as-trace-generator** substrate (`circuitTraceRow(Mapped)`, the event mirrors, the shared
  prime), consumed by the anchors above and by the exporter's per-chip spot check.
  **Trace conformance against SP1's real prover is the dump-anchored pipeline, not a `native_decide`
  battery** (2026-08 retirement of the legacy 21 anchors): committed SP1 dumps (`export/sp1dump/`,
  sole writer `scripts/update_sp1_dumps.sh` at the extraction pin) + the fail-closed generation-time
  gate in `scripts/witgenExport.lean --testdata` (every event row recomputed via
  `FlatOperation.witgen` + the symbolic row map and matched cell-for-cell, all 25 chips) + the Rust
  reference-interpreter differential (`scripts/run_interp_diff.sh`). The gate re-runs in the
  alignment workflow only (`check_witgen_export.sh --regen` in `test-full`; the exporter imports the
  umbrella, which PR CI does not build) — **a PR that touches the pins, `ToClean/`, or the exporter
  runs `scripts/check_witgen_export.sh --regen` locally before merging**, since PR CI cannot.
- **`Soundness/`** — the whole-machine layer: `RowView.lean` carries the live normalized
  `StateAccess`/`ProgramAccess` vocabulary, while `TypedState.lean`, `TypedProgram.lean`, and
  `TypedMemory.lean` read the actual Clean interaction ledger (the obsolete parallel
  `*Consistency.lean` lookup shadows were retired);
  `ChipRow.lean` (the `ChipKind` structure-of-functions — each chip registers one `kind`, carrying a
  `name` = its SP1 `MachineAir::name`) + `ChipRegistry.lean` (`allChipKinds`); `SP1Ensemble.lean`
  (`sp1Ensemble` — a plain Clean `Ensemble`, 25 chips + 30 boundary/provider tables: six Byte
  providers at positions 25–30, all 17 fixed Range widths `0..16` at 31–47, Program at 48, Memory
  init/final at 49/50, MemoryBump (51), StateBump (52), Halt (53), and SyscallInstrs (54)); the full native
  ensemble therefore has 55 tables,
  plus the separate state-boundary verifier. Exact transport recounts Byte/Range/Program
  multiplicities from the actual Clean interaction ledger of every non-preprocessing native table;
  it does not copy the full exact cluster's multiplicities. The raw exact Byte/Range/Program
  assertion lists are empty: `CoreAIR.PreprocessedBinding` only records the named matrix/PCS-opening
  premise, to be discharged by ArkLib; it proves neither row-local meaning nor provider selection.
  `PreprocessedProviderContract` is the
  explicit caller-supplied per-row local-semantics premise. A caller-supplied
  `CanonicalPreprocessedInventory` selects carriers
  source-backed by their matching exact matrix/Range-width block and separately supplies projected-key
  `Nodup`; zero-demand raw keys may be omitted. The recount contract states nonzero-demand
  Byte/Program coverage, nonpositivity, and canonical capacity. `freshRowsByKey` is a
  declarative/regression helper, not the construction path. PCS/program identity, State/Memory
  balance, and semantic binding stay separate and explicit. The recount derives Byte (including
  Range) and Program integer balance; the global contract retains all-channel count bounds and
  State/Memory integer balance. The timed/ranked
  grounding engine;
  `WitnessDecode.lean` (the deterministic typed row decoder), `LocalExecution.lean` (grounded ordered
  rows → a genuine shard-local Sail chain), and `AIR.lean` (the honest native witness relation plus
  proved `supported_core_witness_grounding` and `supported_core_native_sound`); the
  grounding-adapter/contract stack that proves `supportedCore_orderedRows_dynamic` from per-chip
  obligations — `GroundingAdapter.lean` (the `advance`→timed-engine-record adapter: `RowWiring`,
  `stepFact_of_advance`/`frameFact_of_advance`, `rowWiring_rtype`), `ChipContracts.lean`
  (the `ChipGroundingContracts` bundle + registry-wide proved instances),
  `AlignedCarrier.lean` (+ `AlignsWith` in `TimedGrounding.lean`, the ordinary↔aligned `RowFacts`
  carrier transports), and `TimeExtraction.lean` (the `pull_lt_push` payoff from the memory-channel
  `ClkBound`); and the typed interaction/Memory bridge (`TypedInteractions.lean`, `TypedMemory.lean`;
  exact evaluated chip pulls → timed facts/live operands); and the
  auditable instruction-coverage layer — `Coverage.lean` (+ the opcode enum itself at
  `Model/Opcode.lean`, namespace `SP1Clean.Soundness` per the decoupling rule) (the `Opcode → chip → Sail`
  routing table mirroring SP1's `tracing.rs`/`RiscvAir`). The former `InstructionTrace.lean` name-only
  row-routing shadow and `Completeness.lean` routing scaffold were retired in favor of witness decoding
  and timed grounding. The converse is now the proof-independent all-25 compiler under
  `Proofs/Completeness/{InstructionEvent,ExecutionCompiler,NativeTraceCompiler}.lean` plus the
  stratum-10 `Soundness/NativeCompleteness.lean` capstone: it constructs all 55 tables and proves
  constraints/seven-channel balance on `SupportedCoreNativeAdmissibleShardRelation`. Widening that
  compiler domain remains named semantic-readiness/footprint work. Soundness and completeness now
  share `SupportedCoreShardExecutionRelation` and the single
  `CoreProfile.WithinOrdinaryRowLimit` policy; `NativeShardTraceTotal` is the exact remaining
  condition for unconditional correctness and public-language equality. No unconditional equality
  is claimed yet. The bespoke
  `MachineSoundness`/`MachineConsistency` `TraceValid` capstone was retired 2026-06-05.
  `Soundness/CoreAIR.lean` is the exact v6.4.0 deterministic boundary: its `_of_obligations`
  combinators consume the paired 34+6-table `CoreAIR.Current.ShardRelation` and expose the unclosed
  field-by-field proof bundle plus an explicit external loader/platform context.
  The frozen Eulerian-path interface (`GatedVm/`, `TargetVm.lean`, `AdvanceDispatch.lean`, the
  `Soundness/Decode.lean` walk half) was deleted 2026-08 — its scheduled post-seam retirement; the
  live-path survivors are `Walk.lean`'s graph core, `RowEffectDefs.lean`'s `RefinesAt`/`RowEffect`
  interface, and `Soundness/Decode.lean`'s hoist/evidence half. Audit harness: `scripts/run_audit.sh`
  (pins + sorry gates + the `#print axioms` census via `scripts/gen_axiom_probe.py`).
- `Soundness/RowView.lean` (the reader-agnostic `RowView`/`AdapterView` row-view infra the bus layer reads —
  formerly the top-level `Trace.lean`). The design rationale for the whole-chip semantic boundary is in
  `docs/architecture.md`. The root index is `SP1Clean.lean` — **wire every new module's import there**.

**Namespaces are decoupled from directory paths, below the pillar root** — a file's `namespace` (e.g.
`SP1Clean.AddChip`, `SP1Clean.Word`) does **not** track its directory, so files can be moved between
pillars without changing any fully-qualified name (only `import` lines and tooling path-globs follow the
move). Keep that.
⚠ **The pillar root is the exception, and it is gated.** If the first `namespace` names a pillar
(`SP1Clean.Model`, `SP1Clean.Soundness`, …) it must be the pillar the file's stratum expects —
`scripts/check_layering.sh` fails the build otherwise. The decoupling is what let
`Faithful/ExtractedInteractionModel.lean` sit in the wrong pillar for months *while declaring
`namespace SP1Clean.Extracted`*, which put `Interaction.toAccess` out of reach of the completeness
layer. Where the namespace deliberately records intended vocabulary rather than placement (as
`Model/Opcode.lean` does), that is an entry in `scripts/layering_allowlist.txt` with a reason, not a
silent divergence. Full contract: `docs/layering.md`.

**Lake libraries** (`lakefile.toml`, eight of them, one option set): `SP1Core` (root index
`SP1Clean/Core.lean`, strata 0–6 — the PR-CI build), the umbrella `SP1Clean` (root index
`SP1Clean.lean`, everything — the alignment build), the three upstream-destined libraries
`ToMathlib`/`ToPolyFun`/`ToClean`, the generated Sail model `LeanRV64D`, and the two **test**
libraries `SP1CoreTest` (the `testDriver` → `lake test`; globs `SP1CleanTest.Core.+` +
`SP1CleanTest.TraceGenTests.+`) and `SP1CleanTest` (glob `SP1CleanTest.+`, the alignment
anchors included). The test libraries hold the exportability/non-vacuity anchors and the
trace-generator substrate; they import `SP1Clean` but are **not** part of the umbrella, so
`lake build SP1Clean` never compiles them (keeping the main build `native_decide`-free). Every
option is package-level (`[leanOptions]`); no library carries linter flags of its own, and a
module's owning library (Lake: the last declared one matching it; a globless library matches
everything under its root) only decides which identical configuration it is built with. To build
one layer, build a module (`lake build SP1Clean.Math.Word`) or the core; there are no per-pillar
targets. Isolation is **by convention** — Lake does
not forbid cross-layer imports within one package; the auto-gen guard is the `Extracted/`
"do not hand-edit" headers + the sole writer `update_extracted.py` (and, for the export trees, the
sole writers `scripts/witgenExport.lean` / `scripts/update_sp1_dumps.sh` + their byte-identity gates).

- **`ToPolyFun/`** (top-level, own `lean_lib`, in `defaultTargets`) — upstream-destined PolyFun
  material, same contract as `ToMathlib`/`ToClean`: imports only PolyFun, declared in PolyFun's own
  namespaces (`PFunctor.DynSystem.Prefix.append`, `ReachableIn.add`/`split`, `Labeled.Trace`), each
  file stating its gap against upstream. The machine vocabulary used anywhere in this tree is
  PolyFun's (`Labeled`, `Prefix`, `ReachableIn`); nothing is re-defined locally.
  `ToClean/Air/Realizes.lean` (`Air.Flat.Realizes`, a Clean ensemble realizing a PolyFun `Labeled`
  machine, with `Realizes.statement_iff` as the one statement shape) is the Clean side;
  `SP1Clean/FormalModel/ShardMachine.lean` and `SP1Clean/Soundness/Shard/Machine.lean` are the SP1
  instances (`sp1Machine`, the `Labeled` bundle of the existing `executionSystem`; `executes_iff`;
  `statement_iff_of_realizes`).
- **`ToClean/`** and **`ToMathlib/`** (top-level, own `lean_lib`s, in `defaultTargets`) — the
  **upstream-destined** libraries, modelled on VCVio's `ToMathlib/`. `ToClean` holds material bound
  for the Clean DSL; `ToMathlib` holds material bound for Mathlib. **Import rule (load-bearing):
  `ToMathlib` imports only Mathlib; `ToPolyFun` imports only PolyFun; `ToClean` imports Clean (and
  may import `ToMathlib` and `ToPolyFun`, since Clean plans to import PolyFun); NONE may import
  `SP1Clean`.** That is what keeps them genuinely contributable and makes the terminal
  step of an accepted PR a plain deletion plus a repoint of importers to `Clean.*`/`Mathlib.*`.
  Declare things in the namespace they would occupy **upstream** (e.g. `witnessVectorIR` lives in
  `namespace Circuit` with a matching `export`, beside Clean's own `witnessVector`), so acceptance
  changes no call site. Each file's docstring must state the **gap against upstream** — what exists
  there, what is missing, and why — because that text becomes the PR description. Both libraries
  run under the same package-wide linter set as the core (material heading upstream gets no
  relaxation), are covered by every source guard, and are gated by `scripts/check_root_index.sh`.
  **All three are module-system libraries** (`requiresModuleSystem = true`; a non-module file in
  them is a warning and, under `--wfail`, a failure), each file in its upstream's header idiom so
  acceptance is a copy: `module` / `public import …` / `public section` for Mathlib-bound theorem
  files; `@[expose] public section` for PolyFun- and Clean-bound definition files (Clean's
  `Circuit/Formal.lean` shape — `SP1Clean/` proofs unfold these by `rfl`/`simp only
  [circuit_norm]`); `public meta section` for tactic/simproc files (`IteDecide`,
  `GetElemFastPath`); a mixed file adds `public meta import Lean` and keeps the meta code in the
  same exposed section (`StructEvalLemmas`). A `private` declaration used inside an exposed
  definition is an error in module mode — make it public. The `SP1Clean/` and test trees stay
  non-module (`allowNonModules = true` per library) until their own migration.

**Restructure status (updated 2026-07-27; whole-chip oracle migration completed the same day).**
Landed in the 2026-07 release-readiness campaign: the full 25-chip `Extracted/ChipOracle/`
migration (native rows everywhere, zero legacy chip files, the `MemoryAccess` struct carrier, the
reader-family oracle config), the release-readiness audit (zero BLOCKERs across the 25-chip spec
review, substrate, relation level, Rust-faithfulness spot checks, and Clean-idiom sweep — the
full findings log lived at `docs/audits/2026-07-release-readiness.md` through commit `14c926bd`
and is retrievable from git history; its durable disclosures are inline in the verification
report and `docs/agents/extraction.md`), the docs pruning, and the external verification report
(`docs/verification-report.md`). Previously landed: the `Math`/`Model` split, list-only `Extracted/`
consolidation (including system tables, manifest, and provenance), the `FormalModel/Contracts/` audit surface (all `Spec`s +
the ALU chips' `Assumptions`/`ProverAssumptions`), the `Native/`+`Proofs/` five-pillar re-bucket of
`Chips`/`Operations`/`Readers`/`WitnessTests`, and all six per-pillar layer libraries. Every registered
chip soundness/completeness theorem, DivRem evidence theorem, structural circuit law, grounding
contract, and whole-chip faithfulness proof is closed. `scripts/run_audit.sh` gates zero proof
deferrals. The exact v6.4.0 Core relation and conditional `_of_obligations` combinators are landed;
their explicit refinement bundle is not yet instantiated. The obsolete nine DivRem per-op soundness files and
their shared tail were retired in favor of the four-family evidence contract. A large proof-cleanup
campaign (2026-06-22 / 06-23) golfed ~109
hand-written files (−591 lines) while preserving axiom-cleanliness, plus substrate-hoist refactors
(`Word.isU64_four`, Faithful `val_16`/`bool_iff` dedup → `ChipTactics`). Upstream `main` was merged in
2026-06-23 (#100 hard-gates `skipKernelTC` and removes overrides; #101 fleshes out the immediate-type Sail
bridges; #102 makes the jalr/jal/branch specs explicit about divisibility / LSB-clearing). The 2026-08
release-audit pass closed the recorded `Assumptions`-lift plan at its true extent: UType joined the five
ALU chips on `Contracts/ChipAssumptions.lean`, and the rest are a **stated keep-list**, not pending work —
the hint/helper-dependent chips (Mul/Bitwise/Lt/Branch/Jal/Jalr/DivRem/ShiftLeft/ShiftRight) reference
`Defs`-layer witness plumbing, and the memory/x0 chips' whole contract blocks (`Inputs` + `Spec`) are
Native-resident pending the "Spec homing" backlog item (see the ChipAssumptions module docstring and
`docs/architecture.md` § deliberate layering exceptions). The same pass renamed the ten suffix-less
`Faithful/` anchors to `<X>Chip.lean`, named the micro-time window constants with their Rust provenance,
and completed the root index (now gated by `scripts/check_root_index.sh`). The trace *arguments*
(`RefinesAt`/`RowEffect`/routing) are `ChipRow`/`RowView`-dependent and so remain in `Soundness/` —
their natural layer — rather than being forced below it.
A bespoke-trail → Clean `VmTables` migration was investigated and **rejected**
— Clean's VM engine yields verifier-guarantees with no explicit execution walk, while the SP1 argument
needs a balance-derived ordered trail, so re-basing adds obligations without removing the
SP1-specific trail machinery (see `docs/architecture.md`).

**Legacy 55-table structural-bus grounding (closed for its stated slice).** Channels communicate the field tuples and
multiplicities that SP1 actually constrains; they do not assert reachability. `VmChannel` and the earlier
semantic-channel spike were retired. State has local guarantee `True`, Program carries `RowSpec`, Memory
carries `isU64 ∧ ClkBound` (value + a bounded 24-bit access timestamp), and Byte carries `ByteRowSpec`.
`LocalStateTruth`/`ProgTruth` are conclusions of the timed
grounding engine from bus balance, boundary/provider facts, program commitment, strict schedule rank, and
the 25 chip `advance` lemmas. No chip `ProverAssumptions` threads either global truth. The current capstone
layers distinguish native supported-machine refinement, extracted AIR faithfulness, full SP1 AIR
soundness, and the eventual ArkLib verifier theorem; see `docs/roadmap.md` for the separate native and exact targets.
The memory-bus closed forms, `GroundingAdapter`, all 25 `ChipGroundingContracts`, aligned-carrier
transports, RAM/same-location grounding, and per-position assumptions/readiness are proved. Remaining
work is to derive this native relation's semantic boundary premise from the exact upstream system
tables. `SupportedCoreNativeRelation` currently carries **three** conjuncts — the ensemble algebra, that
boundary binding, and the interim `SyscallTableInactive` (`Soundness/GroundingInternal.lean`). The
third is a placeholder rather than a claim, and is disclosed as one: the `SyscallInstrs` chip is
proved and its table registered at ensemble position 54, but the timed grounding engine does not yet
walk a syscall row's three register touches, so `noActiveRows` restricts the relation to shards whose
syscall table is inactive, and `haltTablePresent` keeps the Halt table the sole Exit contributor.
Both fields go when those two things change — the first with the engine's mixed-row carrier, the
second with the terminal-row policy for the full syscall table. Shards with an active syscall row are outside this legacy relation, and the relation says so rather than assuming it away.
An *earlier* third conjunct (`SupportedCoreMemoryTimestampRangeRelation`, the
pulled-record `clk_high < 2 ^ 24` bound) was deleted in the timestamp-bound derivation: it is now derived from
the produced side of the capstone's own per-location Memory balance, unblocked by moving the bound
out of `ChipGroundingContracts.rowAligned`'s premises and into the per-touch antecedent of its slot
conjunct.

Everything is **field-generic** over a prime field — the standard variable block is:
```lean
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
```

## Clean-native principles (non-negotiable)

**Read Clean's own docs — they are the upstream authority for this whole project.** Our proof-style notes
below are SP1-specific *instances* of principles Clean already documents generally; when a technique here
feels ad-hoc, the general rule is in Clean's docs.

*Where to find them.* Browse upstream at **<https://github.com/Verified-zkEVM/clean>** (the `doc/` folder +
`Clean/Air/README.md` + the repo-root `AGENTS.md`), or read the copy Lake installs in-tree under
**`.lake/packages/Clean/`** (e.g. `.lake/packages/Clean/doc/performance-problems.md`). Prefer these over any
local checkout: Clean is a pinned **git** dependency, and a local sibling path must never be baked into
permanent docs or into `lakefile.toml`. (The pin can still lag upstream `main`; if a doc named below is
missing from `.lake/packages/Clean`, read it on GitHub.)

**The Clean pin is upstream `main`** (`fba2a29f5e36420d797c1de118ac9f11f23b819e`, 2026-09-16); the
2026-08 fork (`dtumad/clean` `sp1-integration`) was retired in the 2026-09 toolchain move — its
two modifying changes are re-derived as pure additions (`ToClean/Circuit/AgreesBelowWithData.lean`,
`ToClean/Circuit/WitgenShare.lean`; Clean PR #450 remains the upstream proposal for the first,
#453 for the second was closed unmerged 2026-09-21 — the sharing pass is ours to keep). The
**standing split** still applies: a change that MODIFIES an existing Clean declaration cannot be
shimmed in `ToClean/` (downstream Clean theorems refer to Clean's declaration, not ours) and needs
an upstream PR — pin a fork branch only for the life of that PR, documented as such; a **pure
addition** stays in `ToClean/` (no pin bump; acceptance is a plain deletion + repoint).
`docs/agents/clean-upstream.md` records the retired fork, the PR queue, and the exit condition of
any temporary pin; `docs/release-audit.md` discloses the pins.

Read, in priority order (paths relative to the Clean repo root — i.e. `.lake/packages/Clean/<path>` in-tree,
or `<path>` on GitHub):
- `doc/performance-problems.md` — the `whnf`-into-expensive-values doctrine (make dangerous values opaque;
  cross spellings by syntactic rewriting, not unification), the 9 fix patterns, the kernel-size-cliff
  completeness recipe (`circuit_proof_start_core`), and the **"keep hypothesis types folded"** section (our
  "pass the `Spec` folded" fix). Read this **before any nontrivial proof work**, and first when you hit a
  `whnf`/heartbeat/`(kernel) deep recursion` blowup.
- `doc/proving-guide.md` — opening/middle/closing tactic moves; the "what (not) to unfold" list.
- `AGENTS.md` (Clean's own) — subcircuit-boundary discipline (bundle a proof boundary, inline a non-boundary,
  never leave an unbundled `Circuit` parent proofs treat abstractly), helper-lemma discipline (helpers are
  for real math, not for unpacking `ConstraintsHold`), spec-states-meaning discipline, and the
  `ElaboratedCircuit` explicit-`elaborated`-field performance rule.
- `Clean/Air/README.md` — the flat-AIR channel/ensemble/`Balance.lean` model our grounding engine builds on
  (incl. the "guarantees-to-requirements-reversal" theorem — the general form of our currency circularities).
- Secondary: `doc/witgen-authoring.md` (the exportable witness IR), `doc/conventions.md` (local style that
  differs from Mathlib).

These are the keepers from sp1-lean's "faithful sub-circuit composition" discipline; violations are bugs.

1. **Compose true Clean subcircuits, not inline constraints.** A chip's `main` invokes each
   sub-operation through its bundled `circuit` — `let _ ← <SubOp>.circuit ⟨…⟩` (the
   `GeneralFormalCircuit` `CoeFun` application) or `assertion <SubOp>.circuit ⟨…⟩` — both of which
   compose it as a genuine subcircuit boundary (Clean's `subcircuit` combinator is the underlying
   mechanism). A gadget that uses another gadget composes it the same way. Never inline a
   sub-operation's constraints.
2. **One `main`, one `Spec` per file.** Each `Native/Operations/<Op>` and `Native/Chips/<Op>Chip/Defs.lean`
   exposes exactly one `main`, with one `Spec` (in `FormalModel/Contracts/`) plus the `circuit` glue (in
   `Proofs/`), and references sub-operation Specs *by direct field
   application*, never by re-wrapping low-level constraints.
3. **Specs are semantic, not structural.** The `Spec` states what the row *means* (a `toBitVec64` equation,
   `is_real`-gated), not a restatement of the constraint list. No `InlinedSpec` / `inlinedSpec_iff_spec`
   bridging helpers — they only exist when `main` and `Spec` were defined in mismatched forms; the fix is to
   align them.
4. **Axiom-clean target.** After each artifact, check `#print axioms <decl>` (or the `lean_verify` MCP tool) is
   only `[propext, Classical.choice, Quot.sound]` (bv_decide may add generated
   `._native.bv_decide.ax_*` constants — the v4.32.2 form of the former
   `Lean.ofReduceBool`/`trustCompiler`) — and
   **no `sorryAx`**.

## Proof-style quick notes

- `circuit_proof_start` (from `Clean.Utils.Tactics`) is the **first** tactic in soundness/completeness proofs;
  any `have`/`set_option` must come after it, or it errors "can only be used on Soundness/Completeness".
  (`haveI`/`letI` in a proof are a linter finding since Mathlib v4.33 — write `have`/`let`.)
- Imports precede the module doc-comment (the module system requires it, and it keeps every file
  in the shape Clean and Mathlib use).
- **Linters — two kinds, one policy.** *Syntactic* linters run during `lake build`
  (option-gated); *environment* linters run as a separate `lake lint` pass over the built
  environment. The policy for both: **the practices these linters enforce are adopted.** Every
  finding is debt to fix, not a preference to negotiate; a permanent exception exists only for an
  extenuating circumstance stated at the site (typically an identifier that must mirror an
  external one — a Rust field, a Sail function) and is spelled `@[nolint <linter>]` on the
  declaration or `set_option linter.<x> false in` on the command, with a comment saying why.
  - **Syntactic.** The package enables **Mathlib's standard linter set** once, for every library:
    `weak.linter.mathlibStandardSet = true` in `lakefile.toml` `[leanOptions]` (plus
    `linter.style.admit`, which is not a set member). Two mechanics make this the whole story:
    `weak.` means the option is ignored where it is unregistered (the generated Sail model imports
    no Mathlib), and Lean resolves an unset linter option as *explicit value ⊳ `linter.all` ⊳
    linter-set membership ⊳ default*, so the generated `Extracted/` modules and the `*Vectors`
    test batteries — which carry `set_option linter.all false` — are outside the set without any
    per-library flags. The `weak.linter.<x> = false` lines in `lakefile.toml` are **temporary
    opt-outs**, each with its measured count: the sites get fixed in the lint burn-down
    (`docs/roadmap.md` § Lint debt) and the line is deleted at count 0. Enforcement is
    `lake build --wfail --iofail` in CI. The non-negotiable file-level suppressions —
    `unusedSectionVars`/`unusedSimpArgs` (structurally necessary in circuit proofs) and the
    generated files' `linter.all false` — stay.
  - **Environment (`lake lint`).** The driver is Batteries' `runLinter` (`lintDriver =
    "batteries/runLinter"`, the same as Mathlib, cslib and PolyFun): every default `@[env_linter]`
    (`docBlame`, `defsWithUnderscore`, `unusedArguments`, `simpNF`, …) over the declarations of
    the four roots `SP1Clean`, `ToClean`, `ToMathlib`, `ToPolyFun`. It needs built oleans: `lake
    lint` (full tree, the alignment workflow) or, on a core build, `lake exe runLinter --no-build
    SP1Clean.Core ToClean ToMathlib ToPolyFun` (PR CI). `scripts/nolints.json` is the
    **burn-down list**: `scripts/update_nolints.sh` regenerates it (Batteries' `--update` handles one
    root at a time; the script runs it per root and merges), every entry is a debt, and CI
    fails on any finding not in it — so no new debt enters. Generated declarations are fixed in
    the emitter (`update_extracted.py` emits docstrings, camelCase definition names, and
    `@[nolint …]` where the Rust signature forces an unused argument or a mirrored name), not by
    hand. Names: definitions are `lowerCamelCase`/`UpperCamelCase` (Mathlib's convention, the
    `defsWithUnderscore` linter); snake_case is reserved for identifiers that mirror an external
    one and carries the `@[nolint defsWithUnderscore]` exception.
- **Docstrings.** Every declaration has one (`docBlame` is the gate). Terse and clear: one or two
  lines stating what the declaration *is now* — no history, no narrative of how it came to be
  (that belongs in git and the audit docs). A docstring grows beyond a few lines only with a
  reason. Where a family is uniform (the 25 chips' `circuit`/`main`/`Spec`), say it once in the
  module docstring and keep the per-declaration line short.
- **This repo does not raise elaboration budgets.** Hand-written Lean carries **zero**
  `set_option maxHeartbeats`, matching upstream Clean (none in 44,603 lines), and two measured structural
  `maxRecDepth` sites; every other site is on a generated definition.
  `scripts/check_option_escapes.sh` (the CI `guards` job + `run_audit.sh`) **prohibits** both options: any
  site not named in `scripts/option_escapes_allowlist.txt` fails the build. It is not a ratchet and not a
  budget — a ratchet permits a new hatch as long as an old one leaves; this does not. When a proof blows
  up (heavy `toBitVec64`/carry rw chains are the usual suspects), **fold it** — see
  `docs/agents/proof-patterns.md` § "Elaboration budgets and option escapes". The allowlist is a
  last resort with a four-part bar, not an allowance.
- **Never write the phrases `set_option maxHeartbeats` or `set_option maxRecDepth` into a Lean comment or
  docstring under `SP1Clean/` / `SP1CleanTest/`.** The guard greps for the **full `set_option …` phrase** and
  does not parse Lean, so a comment quoting a whole directive scores as a live site and fails the build.
  (The bare option name in prose is harmless — "the depth bump", or even "maxRecDepth" alone, is fine.)
  Record a measured ladder without the directive: "the former 8M ceiling was ~200× over".
- **Dropping `by exact` on a `def`'s Prop-valued field can be load-bearing *opacity*.** A tactic block becomes
  an opaque auxiliary proof constant; the bare term inlines and `isDefEqDelta` unfolds it into every consumer.
  One such −1-line golf took a downstream module from **260s to >1230s**. A/B-time the *downstream* consumers,
  not the edited file (`docs/agents/proof-patterns.md`).
- **Never `set_option (debug.)skipKernelTC`.** It bypasses the kernel's type-check re-run — the trust anchor
  for an axiom-clean proof — so it is **CI-gated** (`scripts/check_no_skipkerneltc.sh`, run by the audit and a
  standalone CI `guards` job; any hit in `SP1Clean/**/*.lean` fails the build). If a goal blocks on a kernel
  deep-recursion / `2^64`-unfold error, the fix is to factor the expensive compute into an **abstract-`BitVec`
  helper** proved once over variables (the `srl_toNat`/`sra_toNat` pattern), then apply it symbolically — never
  silence the kernel. See `docs/agents/proof-patterns.md` §"Bit-shift chip soundness" (the `2^64` bullet) for
  the worked fix.
- **Never `native_decide` in the main `SP1Clean/` library.** It discharges goals by running compiled code,
  trusting the **whole compiler** (surfaced in the census as generated
  `._native.native_decide.ax_*` constants — formerly the named `Lean.ofReduceBool`/
  `Lean.trustCompiler` axioms) — so headline soundness
  theorems would no longer be `[propext, Classical.choice, Quot.sound]`-clean. It is **CI-gated**
  (`scripts/check_no_native_decide.sh`, run by the audit + the `guards` job; any hit in `SP1Clean/**/*.lean`
  fails the build). Conformance checks that genuinely need it live in the separate top-level `SP1CleanTest`
  library (`lake test`); to disclose a new one, put the anchor there, not in `SP1Clean/`.
- `mul_eq_zero` won't fire on `ZMod p` (a `Nat.rec` Mul-instance quirk) — derive booleanness via
  `inv_mul_cancel₀` / a `bool_of_mul_pred`-style lemma instead.
- `Word` is an `abbrev` for `Vector` — `w.toBitVec64` dot-notation fails; write `Word.toBitVec64 w`.
- **The Sail `-i` token — space your negations.** Sail declares GLOBAL `infixl:65 " +i "/" -i "/" *i "/" ^i "`
  (`Sail/Sail.lean`, integer ops, used 1300+× in the generated LeanRV64D model so they can't be scoped). The
  four tokens are active in every file that transitively imports the generated Sail model — the whole
  bridge/Soundness/semantics side, and any proof file that reaches `Model/Semantics/` or `Model/SailWrap.lean` —
  and there the lexer greedily tokenizes `<op>i` inside `-input_is_real` /
  `i₀+i` as the operator → `unexpected token '-i'; expected term`. So keep the habit everywhere: a space (or parens) whenever an
  operator is immediately followed by an `i`: **`- input_is_real`** / `-(input_is_real)` (never `-input_is_real`),
  **`i₀ + i`** (never `i₀+i`), `2 ^ i`, `x * input`. (The space *before* the operator is untouched and still
  distinguishes binary-op from unary/application, so this is semantically null. The spaced Sail operator
  ` +i ` — the `i` followed by a space — is the one form you must NOT break.)
- Prefer targeted `simp [...] at h` over `simp_all` (it leaks into unrelated hypotheses).
- **Don't leave `ring`'s `info:` note in the build.** On some goals `ring` runs its `ring1` pass, which
  *fails* and emits `Try this: ring_nf` / "ring works primarily in commutative rings …", then closes via
  the `ring_nf` fallback — so the proof passes but leaks an `info:` note that clutters the build output.
  Close those goals with the tactic that actually works, no note: `simp` for the `is_real` binary gate
  (`is_real * (is_real - 1) === 0`) and `interval_cases`-carry goals, `ring_nf` where it closes, or the
  explicit lemma (`sub_eq_add_neg`, `zero_mul`/`mul_zero`). A clean build has zero `info:` notes too.
- **`ElaboratedCircuit` field obligations should almost never have a hand-written proof — make the default
  tactics close them.** `localLength_eq`/`output_eq`/`subcircuitsConsistent`/`channelsLawful` each have a
  Clean default tactic (`simp only [circuit_norm, seval]`); the goal is always to let it succeed by adding
  the right `circuit_norm` lemmas, then **omit** the field — not to override it. Recipe: every circuit
  exposes its `channelsWithGuarantees`/`channelsWithRequirements`/`localLength` as `@[circuit_norm]`
  `rfl`-lemmas (`channelsWith*_eq`/`localLength_eq`, each behind `set_option linter.unusedSectionVars
  false in`) right after its `elaborated` instance; the generic list/prop closers are tagged `circuit_norm`
  once in `Model/Channels.lean`. A missing default-tactic close means a missing `circuit_norm` lemma,
  not a reason to hand-write the field. These lemmas also tidy `circuit_proof_start`; mind the soundness
  requirement-tail caveat. Full recipe: `docs/agents/proof-patterns.md` "ElaboratedCircuit field obligations".
- **When a proof is slow, extract over *opaque* arguments — and check what the extraction can still see.**
  This is the single highest-yield move (`docs/agents/proof-patterns.md` § "Compile-time and kernel
  performance"). The cost hides in
  places the goal text does not show: in the local *context* rather than the goal, in a `have`'s *type*
  rather than its proof, in the *order* of two tactic steps, in a struct *literal* where `fromElements`
  belonged, in rewrites that each renormalise a large context. The fix is to interpose an opaque variable,
  never to make the expensive step cheaper. Corollary: extracting a block into a `have` **inside the same
  proof** buys nothing, because it keeps the whole context — so "extraction moved nothing" is not evidence
  of irreducibility unless the extraction actually took the context away.
- **Ladder before you believe a cause you found by reading code.** A structural hypothesis promoted on a
  code-read predicts nothing until a measured ladder confirms it: a mechanism can be genuine, verifiable,
  and irrelevant — including one that is upstream Clean's own documented performance rule (measured delta:
  0.008%). Measure first; keep the timing transcript with the review artifact rather than as a
  permanent point-in-time document.
- Full landmine list + the witnessed-`FormalCircuit` recipe: `docs/agents/proof-patterns.md`.

## MCP servers

`.mcp.json` declares `lean-lsp` (live goal/diagnostic state from the Lean LSP); it is deliberately
committed so any checkout gets the server without setup. It launches via `uvx`, so `uv`
must be on `PATH` — install with `curl -LsSf https://astral.sh/uv/install.sh | sh` if missing. Local
enable/permissions are in `.claude/settings.local.json` (`enableAllProjectMcpServers: true`). Restart the agent
after installing or toggling.

## docs/

- **Clean's own docs (the upstream authority; read first)** — upstream at
  <https://github.com/Verified-zkEVM/clean>, or in-tree under `.lake/packages/Clean/`: `doc/performance-problems.md`
  + `doc/proving-guide.md` (proofs/perf), `AGENTS.md` (subcircuit/spec/`ElaboratedCircuit` discipline),
  `Clean/Air/README.md` (channels/ensembles/balance). See the "Read Clean's own docs" callout under
  "Clean-native principles" (incl. the path-dependency-is-temporary note).
- `docs/README.md` — index + "what to read first" + the one-role-per-doc split.
- `docs/overview.md` — the ten-minute reader-facing orientation: current theorem, coverage table,
  trust base, limitations.
- `docs/verification-report.md` — the self-contained external technical report (the only doc
  allowed to be long); its citations are machine-checked by `scripts/check_report_citations.sh`.
- `docs/architecture.md` — the chip-centered native/Sail/Rust-oracle/trace chain and theorem layering,
  including the deliberate layering exceptions.
- `docs/roadmap.md` — current native shard targets, implementation order, findings, and release
  gates; exact Core refinement and ArkLib are separate follow-ups.
- `docs/goal-overview.md` — the completed-state contract (verifier + completeness targets). Not
  current status; never cite it as such.
- `docs/release-audit.md` — the honest-claim / trust-boundary report (axiom census and zero-deferral gate;
  regenerate with `scripts/run_audit.sh`). The census is **split by library**: the main scope diffs
  `docs/snapshots/axiom-census.txt` (needs the `SP1Clean` oleans; CI `audit` job runs
  `--main-only`), the test scope diffs `docs/snapshots/axiom-census-test.txt` (needs `lake test`
  first; CI `test` job runs `--test-only`); the no-flag default runs both. The harness leaves the
  tree **clean on a pass**: it diffs each fresh census against its committed snapshot and fails on
  drift; only an explicit `scripts/run_audit.sh --update` rewrites the snapshot(s) for the scope(s)
  run (inspect and commit the delta — a moved auto-generated `bv_decide` `ax_N_M✝` index is
  hygienic). It also runs `check_pins.sh`, `check_root_index.sh`, `check_current_docs.py`,
  `check_release_surface.py`, and `check_report_citations.sh` as gates, so none need a separate
  invocation.
- `docs/agents/lean-sail-notes.md` — the v4.33.1 environment, the git dependency pins (incl. the
  temporary lean-sail pin and its exit), the Sail code-generation workaround, and the
  `lake update` trap.
- `docs/agents/clean-upstream.md` — the Clean pin (upstream `main`), the retired 2026-08 fork and
  how its changes became `ToClean/` additions, the modification-vs-addition split rule, and the
  upstream PR queue with the measurement behind each entry.
- `docs/agents/sail-model-provenance.md` — the in-tree generated `LeanRV64D` library's provenance: the
  two-key SP1 config and its four generated sites, why stock upstream makes the memory-bridge
  lemmas false, the regeneration pipeline, and the re-pinning procedure.
- `docs/agents/proof-patterns.md` — the witnessed-`FormalCircuit` soundness/completeness recipe +
  concrete landmines + the binding **Golf & cleanup discipline** section. It records the
  source-compatibility, audit-surface, proof-performance, and elaboration-option rules that override
  generic mathlib cleanup advice. The `mathlib-quality` plugin is a discovery rubric here, not an
  authority to change public statements, privatise audit declarations, broaden `simp`, or unfold
  performance-sensitive definitions.
- `docs/agents/porting-recipe.md` — step-by-step checklist to port a new chip from the Add/Bitwise template.
- `docs/agents/extraction.md` — the constraint-extraction pipeline (compiler → Python → Lean DSL).
- Generate compile profiles on demand with `scripts/profile_compile.sh` (per-module category split)
  and `scripts/build_semantics.py` (cost joined to layers and headline-claim closures); keep
  point-in-time timings with the review artifact that uses them rather than in the maintained
  documentation set (`docs/audits/2026-09-build-semantics.md` is the current one).
- `docs/snapshots/axiom-ledger.md` — machine-checked `#print axioms` inventory per theorem (point-in-time
  snapshot; re-generate before release).
