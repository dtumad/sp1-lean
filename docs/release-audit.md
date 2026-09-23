# SP1 v1.0 release audit

Snapshot date: 2026-08-06, re-audited on the Lean v4.31 -> v4.32.2 + Sail v4 -> v5 migration, and
re-audited on 2026-09-19 for the full-state capstone branch (see the
[branch review](audits/2026-09-19-capstone-branch-review.md)). The
compiled trust reports are regenerated under `.lake/build/trust/`; the committed trust policy
states permitted dependencies. Rerun the commands below before citing this report for another commit.

## Executive assessment

The repository has a closed, nontrivial native AIR-to-Sail theorem for all 25 supported Core
instruction tables. Every registered instruction chip has:

- native Clean soundness and completeness;
- a bridge to the generated RISC-V Sail semantics;
- a whole-chip proof against the complete extracted Rust assertion system; and
- a whole-chip proof against the complete active Rust interaction multiset on every locally
  accepted reconstructed row in the codec image, modulo permutation and zero-multiplicity entries.

The repository does not yet have a closed theorem from the paired exact upstream Core relation
(34 execution and six Memory-boundary tables) to Sail. Local exact-to-native assembly is now
proved. The remaining gap is deriving the explicit
global balance/count, preprocessing and program authentication, memory-boundary semantics, and
application-level semantic binding needed to instantiate the unclosed
`CoreAIRRefinementObligations` structure. The available
`sp1_air_*_of_obligations` declarations are conditional composition lemmas.

No main-library proof is deferred. This audit found no `sorry`, `stop`, project `axiom`, or `sorryAx`.

## Audited sources

| Component | Audited value |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.33.1` |
| SP1 semantic source | `f66b4bff51d0ccff51d152e0f7f66b2ffedf3529` |
| SP1 description | `v6.4.0` |
| SP1 extraction branch | `b5616f908c393d6050970630871f69afe233a21c` (`dtumad/lean-extraction`, `v6.4.0-10-gb5616f908`) |
| mathlib pin | `0df444a360eaa60ab8c11dca51a86af692955474` (tag `v4.33.1`) |
| Clean pin | `fba2a29f5e36420d797c1de118ac9f11f23b819e` (upstream `main`, 2026-09-16; the 2026-08 fork is retired — see below) |
| CompPoly pin | `a09455a22fea4623a2a1c5b363cf6efc61486a83` (tag `v4.33.1`; Clean's own dependency, Apache-2.0) |
| Generated Sail model | sha256 `7426b9c3d35d1b625a1aa2a16248f8015f70acb80699dca3df552e8db2291af7` (161 files) — the in-tree `LeanRV64D/` + `LeanRV64D.lean` |
| Sail compiler source | `41694abd58b27b687af5db275810dfeb8a88cfc0` (rems-project/sail, `sail2`) |
| sail-riscv model source | `61266bd4dede6c7dd6e903e52dc80bcbf644b1b8` (riscv/sail-riscv, `master`) |
| SP1 Sail config | sha256 `41311181e4cad458c21b01a0160a0087b407ee15e616243013169d52d3c1a854` (`scripts/sail-config/sp1_rv64d_cfg.json`) |
| lean-sail pin | `bde9ecc665b663bbdb29afb11fb6634870fdc7df` (`dtumad/lean-sail` `sp1-pin` = tag `v5` + the one-line `open` disambiguation of rems-project/lean-sail#14 — **temporary**, see below) |
| PolyFun pin | `997828ce4c04ccdc01f5f199069e26a6195ef6e7` (upstream `main`, its last v4.33.1 commit) |

Every dependency is an immutable git pin — `lake-manifest.json` records no `path` entries, so a clean
clone reproduces this graph. The Sail RV64 model is the in-tree **generated** library
`LeanRV64D/` + `LeanRV64D.lean` (never hand-edited): the pinned Sail compiler + sail-riscv sources
above run against the schema-shaped SP1 platform config, written by
`scripts/sail-config/generate_lean_rv64d.sh --install` and gated two ways — the tree hash above
(`scripts/check_pins.sh`, local) and byte-identity with a fresh regeneration from the pins
(`.github/workflows/sail-regen.yml`, on every change to the generator, config, or tree, and
monthly). It equals the opencompl base `11d8fa21` except the four platform-value sites the two-key
config sets (PMP-off moved to a Lean-side hypothesis, 2026-08); the installing commit carries the
provenance record (`docs/agents/sail-model-provenance.md`). The former `riscv-lean` (`RISCV`)
dependency was retired 2026-09-20: the RV64 reference functions the chip specs use are
`SP1Clean/Model/RV64Semantics.lean`, the monad-free Sail write values are
`SP1Clean/Model/SailPure.lean`, and the equalities between them are proved in
`SP1Clean/Proofs/Sail/RV64Bridge.lean`, so the ISA-equivalence chain has no third-party link.

**`Clean` is upstream again.** From 2026-08 to 2026-09 the DSL was pinned to a fork
(`dtumad/clean` `sp1-integration`, base upstream `0e53b9f2`) carrying two modifying changes; the
2026-09 toolchain move retired it. Both changes are now pure additions in this repository's
`ToClean/` library, so no Clean declaration is modified: `ToClean/Circuit/AgreesBelowWithData.lean`
(the data/hint-preserving `AgreesBelowWithData` predicate, its `…ComputableWitnessesWithData`
obligations and `FormalCircuitBase.computableWitnessesWithData_implies` — the fork's strengthening of
Clean's `AgreesBelow`, needed rather than convenient: Clean PR #450's
`not_computable_from_cells_alone` shows the unstrengthened obligation is **false** for any witness
program reading `FExpr.dataGet`) and `ToClean/Circuit/WitgenShare.lean` (`WitgenIR.share`
with its proven `WitgenIR.eval_share`, the subterm-sharing pass that takes the DivRem witness
programs' wire format from 1.22 GB to 1.04 MB). Clean PR #450 remains the upstream proposal for
the first; its acceptance deletes that file and repoints its importers. #453 (the sharing pass)
was closed unmerged on 2026-09-21, so `WitgenShare.lean` is a permanent `ToClean/` addition.

**`lean-sail` is a documented temporary pin.** `dtumad/lean-sail` branch `sp1-pin` is tag `v5`
plus one line — `open PreSail` → `open Sail.ConcurrencyInterfaceV1.PreSail` in `Sail/Sail.lean`,
the namespace the `open` already resolved to — because Lean 4.33's `ambiguousOpen` linter warns on
the original and the build runs `--wfail`. It is rems-project/lean-sail#14; the pin returns to
upstream when that merges (the exit condition recorded in `docs/agents/lean-sail-notes.md`). No
generated-model or proof consequence: the generated `LeanRV64D/` tree is unchanged.

**Upstreaming remains separate from the reproducible pinned baseline.** The 2026-09 re-pin left the
axiom census unchanged apart from renamed probes. The generated Sail model uses a project-hosted
configuration, as disclosed above. The retired fork, the PR queue, and the standing rule for what
may be a temporary fork pin versus `ToClean/` are recorded in `docs/agents/clean-upstream.md`.

The extraction branch is a descendant of the semantic source with that source as its merge base, and
every extraction change is an ordinary commit on it — there is no uncommitted-patch mechanism. The
diff under `crates/core/machine/src` changes only reflection imports/derives needed to expose row
shapes; it does not change an AIR equation or trace-population function. The generator verifies the
merge base, the changed-file allowlist, the derive-only machine diff, and a clean worktree before it
writes any artifact. Changes to `IntoShape`, the constraint compiler, and the symbolic IR are a
separate pinned trusted-extractor surface: their paths are fail-closed by the allowlist and their
bytes by the exact commit, but the gate does not label them semantically inert.

The [capstone assessment](audits/2026-09-capstone-assessment.md) records the 2026-09-08 reproduction,
confirmed repairs, remaining proof obligations, and limits of that review.

## Verification stack and status

| Layer | Main artifact | Result |
|---|---|---|
| Native chip semantics | 25 `GeneralFormalCircuit`s | closed soundness and completeness |
| ISA refinement | 25 `ChipKind.advance` bridges | closed for the supported RV64IM routes |
| Whole-chip AIR faithfulness | `supportedChipFaithfulness` | exact 25-table coverage |
| Native machine grounding | `supported_core_witness_grounding` | closed |
| Native AIR-to-Sail | `supported_core_native_sound` | closed, shard-local, explicit boundary premises |
| Full-state local shard capstone | `Soundness.Shard.statement_iff` | conditional on unfilled soundness and compiler targets; the installed 87-table checkpoint derives the execution path from raw constraints and balance |
| Exact Rust AIR relation | `CoreAIR.Current.Relation` | complete 34/6-table list-level relation |
| Exact Rust AIR-to-Sail | `sp1_air_sound_of_obligations` | conditional; bundle not instantiated |
| Cross-shard execution | `SP1ExecutionRelation` | target relation specified; no soundness theorem yet |
| Core verifier | `VerifierBoundary.PerfectExtraction` composition API | cryptographic proof not implemented here |
| Native ensemble completeness | `supported_core_native_functionalCompleteness` | closed for the deterministic all-25 compiler on its explicit admissible semantic image |
| Broader semantic-language completeness | shared capacity-bounded ordinary semantic relation | alignment closed; `NativeShardTraceTotal` remains open, so correctness and language equality are conditional |

`supported_core_native_complete` is the existential projection of a proof-independent functional
compiler. It computes all native physical rows, refreshes, Memory boundaries, and canonical
Byte/Range/Program providers from the supplied semantic execution; constraints and all seven channel
balances are proved. Its explicit admissible source still requires the named event-validity,
provider-semantic, and actual-footprint facts. Soundness and completeness now share the ordinary
semantic relation and `CoreProfile.WithinOrdinaryRowLimit`. `NativeShardTraceTotal` is the remaining
implication from that bounded ordinary source to compiler readiness and physical capacity.
The correctness and language-equality theorems explicitly consume it. The compiler still emits
only a padding Halt row and an empty SyscallInstrs table.

## Closed 55-table statement

This is the retained ordinary/HALT theorem. The newer complete-state local-shard target is
specified in `SP1Clean/FormalModel/Shard.lean` and `SP1Clean/Soundness/Shard/Contract.lean`;
its resource profile and soundness/compiler instances remain unfilled. The installed mixed AIR
already derives an actual execution path and final PC/clock/frontier agreement, but not the full
outgoing snapshot or all-eight-call completeness. See [the roadmap](roadmap.md).

`supported_core_native_sound` consumes:

```text
native public-input equality
+ all native Clean constraints
+ seven-channel balance (State, Byte, Program, Memory, Exit, Syscall, PublicValues)
+ committed Program and provider/boundary semantics
+ Memory provider uniqueness
```

It does **not** consume a pulled-timestamp range premise: the `< 2^24` bound on every pulled
Memory record's high clock limb is derived inside the capstone from the per-location Memory
balance (`pushGood`/`pullGood` in `SP1Clean/Soundness/AIR.lean`).

It does, however, currently consume one interim premise beyond the ensemble relation and the
semantic boundary binding: `SyscallTableInactive`, which restricts the certified set to shards whose
`SyscallInstrs` table is inactive and whose Halt table still carries the Exit hand-off. That is a
disclosed placeholder for work in flight — the syscall chip is proved and registered, but the
grounding engine does not yet walk a syscall row's memory touches — not a derived fact.

and produces:

```text
a successful shard-local Sail execution
of the statement's program
between the public PC and clock endpoints
(constructed by the proof from exactly the active decoded rows)
```

The exported target relation also carries a finite Memory boundary, its well-formedness, and
agreement with location contents at both endpoints. Exact correspondence to decoded physical rows
lives in the intermediate `supported_core_witness_grounding` theorem. The capstone does not derive
its provider/boundary premises from the exact upstream system
tables. The endpoint/program scope restrictions are in the relation definitions, rather than prose
assumptions.

The conclusion is now a **dichotomy**: `SupportedCoreSailRelation` is an `OrdinaryRun` (the run
above, with committed exit code zero) or a `HaltedRun` (a normally-retiring prefix reaching a
genuine `SP1Halted` state — the pc at a committed `ECALL` word, `t0` holding the canonical `HALT`
code, `a0` the committed exit code — parked at `haltPc` one 264-tick syscall window later). Which
branch holds is decided by the Exit hand-off's algebra alone, not by an added hypothesis. The
theorem still consumes **no boot hypothesis**; boot reachability appears only in the separate
single-shard corollary `supported_core_boot_to_halt_single_shard`, whose premise
`SupportedCoreBootHaltRelation` names the boot boundary explicitly.

Two disclosures attach to the halting branch:

* **The Halt table is native and unanchored.** The Rust oracle it would be anchored against does
  exist — `Extracted/SystemOracle/SyscallInstrs.lean`, extracted like every other, and already
  consumed by `Faithful/CoreAIR.lean` — so what is missing is the `ChipFaithful` anchor, not the
  oracle. The anchor cannot be stated in its present form, because `ChipFaithful` equates two
  *complete* assertion systems and two *complete* interaction multisets, and these are not the same
  table: SP1's row is a multi-arm dispatcher whose interaction list carries `IsZero` selectors for
  syscall codes `0`, `3`, `16`, `26`, and `240`, and which sends on the global `.syscall` bus that
  `HaltChip` does not use. `HaltChip` implements the code-`0` arm
  alone. What lines up — and is the review evidence — is the skeleton: the Rust row computes
  `clk + 264` and reads its three registers at clock offsets `+4`, `+3`, `+2`, exactly the window
  and offsets `HaltChip` uses for `x5`/`x10`/`x11`, with a matching bus shape (2 State, 1 Program,
  6 Memory). Closing this needs a *gated projection* anchor — agreement on rows whose syscall-code
  selector is `HALT` and whose excluded-bus terms vanish. The ensemble now registers the full
  syscall chip, but the restriction relation for the separate Halt chip remains reviewed prose.
* **A 16-bit exit-code profile restriction — ours, not SP1's.** The halt row pins `a0`'s upper
  three limbs to zero, so only a 16-bit exit code can satisfy it. This is a *strengthening* of the
  AIR (an honest prover of a larger exit code cannot produce a satisfying halt row), disclosed here
  rather than hidden in the contract. It is **not** forced by the single-cell `reduce()`: SP1's own
  halt arm constrains `op_b` to be a valid field element — upper limbs zero, and limb 1 bounded by
  a `U16CompareOperation` against `32512 = 0x7F00` — which caps `reduce(op_b)` at exactly
  `p - 1 = 2130706432`, so upstream the decode never wraps. Our restriction exists only because
  `HaltChip` omits that compare; reproducing it widens the profile to SP1's own ~31-bit range and
  removes this disclosure entirely.

The **compiler** direction does not yet emit a live halt row, so the totality-conditional
correctness and language-equality statements are relative to
`SupportedCoreNativeOrdinaryShardRelation` — and `SupportedCoreBootHaltRelation` has no constructed
inhabitant yet.

## Faithfulness audit

The exact instruction profile contains 25 tables. `Faithful/SupportedMachine.lean` stores 25 actual
`ChipFaithful` propositions and their proofs. It proves:

- the certificate length equals the native registry length;
- its table-name order equals the native registry's physical order; and
- its table tags are a permutation of `CoreProfile.instructionTables`.

Each `ChipFaithful` proposition is bidirectional for local assertions **after** an arbitrary
extracted Rust row is decoded and reconstructed as its canonical native physical row. It is not
merely a claim about rows produced by the honest witness generator, but it also does not quantify
over every possible physical native assignment outside that codec image. Interaction equality is
proved on every locally accepted reconstructed row, modulo permutation and zero-multiplicity
entries.

The system tables are handled differently: their complete generated lists are used directly in the
exact relation. StateBump and MemoryBump retain native chips and whole-table faithfulness anchors.
The rest do not acquire artificial row-wise native counterparts, because the native ensemble uses a
proof-oriented provider interface (30 provider/boundary tables alongside the 25 instruction chips —
a 55-table Clean ensemble). The provider family contains six Byte-op tables, all 17 Range widths
`0..16`, Program, MemoryInit, MemoryFinalize, MemoryBump, StateBump, Halt, and SyscallInstrs; the complete Range family
closes the provider side of honest shift-row lookups. `SP1Clean/Composition/{PreprocessedProviders,
MemoryBoundary,SystemTables,ProviderSegment,CoreEnsemble}.lean` now constructively connects the two
local interfaces under a caller-supplied `CanonicalPreprocessedInventory` and proves all 55 native
tables plus the verifier row satisfy their constraints.
Byte/Range/Program counts are recounted from the actual Clean interaction ledger of the verifier,
25 transported instruction tables, MemoryInit/MemoryFinalize, both bumps, a padding Halt table,
and an empty SyscallInstrs table rather than copied from
the larger exact cluster. The raw exact Byte/Range/Program assertion lists are empty.
`CoreAIR.PreprocessedBinding` only records the named matrix/PCS-opening premise, to be discharged by
ArkLib; it proves neither row-local meaning nor provider selection. `PreprocessedProviderContract`
is the explicit caller premise for row-local semantics. Source main
multiplicities are not reused and raw projected keys are not assumed unique. The caller-supplied
`CanonicalPreprocessedInventory` selects carriers backed by the matching source matrix/Range-width
block and explicitly carries projected-key `Nodup`; zero-demand raw keys may be omitted. The recount
contract separately states nonzero Byte/Program-key coverage, skeleton nonpositivity, and canonical
capacity. `freshRowsByKey` is only declarative/regression support. PCS/program identity,
State/Memory balance, and semantic binding remain separate and explicit. The recount derives Byte
(including Range) and Program
integer balance; the global contract retains all-channel count bounds and State/Memory integer
balance. The remaining exact Core refinement task is global across those contracts and the named
public-range and Global→Memory transformations.

## Exact AIR coverage

The generated runtime manifest and hand-readable profile agree on:

- 34 execution-cluster tables and every main/preprocessed width;
- 6 memory-boundary-cluster tables and every width; and
- 160 base-field public-value cells.

The exact execution cluster contains:

- Program, Byte, and Range preprocessed tables;
- 25 instruction tables; and
- SyscallCore, SyscallInstrs, MemoryBump, StateBump, MemoryLocal, and Global.

The separate memory-boundary cluster contains Program, Byte, Range, MemoryGlobalInit,
MemoryGlobalFinalize, and Global.

The current Rust Core machine sources do not use `is_first_row`, `is_last_row`, or transition-window
selectors. Consequently the list-only row extraction does not omit a separate transition family at
this pin. This is a source-review fact and must be repeated on every pin change.

`CoreAIR.Current.Balance.Valid` requires equality of natural send/receive multiplicities. This is
stronger than a bare field-sum equality and is the correct source for execution soundness. The future
ArkLib theorem must show why verifier acceptance extracts that stronger relation.

## COMMIT provenance

The report distinguishes three statements:

1. the program executed and halted;
2. every COMMIT row that occurs contains the correct digest word; and
3. all eight COMMIT rows occur.

The AIR layer is responsible for the second statement (the obligations bundle's
`publicCommitOperand`/`deferredCommitOperand` fields — stated, not yet discharged). It also supplies
the one-way row-to-flag implications and the public-values transition laws (all three, like the
operand fields, are stated obligations — not yet discharged from the exact tables). Together with recursion's
ledger continuity, `finalCommitRowsMatch_of_execution` proves that every existing row is tied to the
terminal digest; it never infers row existence from a flag. Program correctness of the standard halt
wrapper provides the third statement. The verification key prevents program substitution only after
its program binding is proved.

The base shard and execution relations therefore require no wrapper assumption.
`SP1CommitCoveredExecutionRelation` is an optional strengthening derived from
`UsesStandardHaltWrapper` or `CommitCoveringVerifyingKey`.
`completeCommitDigestMatches_of_coveredExecution` proves all eight covered rows match the terminal
digest. Neither program condition currently proves that the digest hashes a modeled output byte
stream.

## Proof and axiom audit

`scripts/run_audit.sh` performs:

- manifest-resolved pin reporting, gating any present `.lake` checkout against the manifest;
- recorded-value cross-checks (`scripts/check_pins.sh`: lakefile ↔ manifest ↔ this report's pin
  table ↔ `CoreProfile.sp1SemanticRevision`, plus generated-model provenance);
- root-index completeness (`scripts/check_root_index.sh`), maintained-document/link/module-docstring
  freshness (`scripts/check_current_docs.py`), report-citation resolution
  (`scripts/check_report_citations.sh`), and an independent exact 25-chip release inventory
  (`scripts/check_release_surface.py`);
- a zero-tolerance source proof-deferral scan;
- a zero-tolerance project-axiom scan;
- `skipKernelTC` and main-library `native_decide` guards;
- an elaboration-budget escape-hatch prohibition (allowlist-gated); and
- the [compiled-library trust policy](trust-policy.md), covering private declarations and
  transitive dependencies in every production/test source module. Unknown axioms and `sorryAx`
  fail; named existing Sail and native-bitvector exceptions remain explicit.

CI runs source/pin/coverage gates in its lightweight `guards` job. The `build-full` job builds
`SP1Clean`, the `To*` libraries and `SP1CleanTest`, runs the full audit, and uploads its main/test
reports. Local `--main-only` and `--test-only` audit flags select the corresponding built scope.
No per-theorem inventory, snapshot update, or committed declaration count is required.

Current policy classes are:

| Class | Interpretation |
|---|---|
| `propext`, `Classical.choice`, `Quot.sound` | accepted Lean/mathlib logical baseline |
| generated `bv_decide` constants | compiler-trusted certificate checking at named existing bit-vector proof owners |
| Sail platform hooks | external operations present in the generated official model |
| generated `native_decide` constants | compiler-trusted tests, confined to `SP1CleanTest/` |
| `sorryAx` | forbidden; current count is zero |

The Sail model's hooks include reservation, floating-point, randomness, and platform termination
operations. The supported ordinary instruction path does not intend to execute most of them, but a
theorem whose target is the complete generated interpreter inherits dependencies from that target and
its reduction lemmas. The policy and generated reports disclose this boundary instead of describing the headline theorem
as depending only on three logical axioms.

The test library's `native_decide` occurrences (the exportability battery's prime instance, the
`NonVacuity.lean` chip-assumptions witnesses, the `NonVacuityReal.lean` real-row satisfiability
battery, and the independent-audit joint-premise regression) are confined there; none are in the
main library, and none are imported by the soundness theorem. Trace conformance against SP1's
real prover no longer uses `native_decide` at all: it is the dump-anchored pipeline — committed
`chip_traces` dumps at the extraction pin (`export/sp1dump/`, byte-reproducible), the fail-closed
generation-time gate in `scripts/witgenExport.lean --testdata` (every event row of all 25 chips
recomputed and matched cell-for-cell), and the independent Rust interpreter differential.

## Trusted or externally assumed components

| Boundary | Why it is present | Closure plan |
|---|---|---|
| SP1 constraint compiler/exporter | translates Rust AIR expressions to Lean lists | pin/diff/hash checks plus independent `ChipFaithful` proofs |
| Generated Sail platform hooks | official model leaves platform operations external | narrow the model interface or prove concrete platform refinements |
| Two-key generated Sail config | `clint`/`simple_interrupt_generator` disabled at four generated value sites — devices SP1 does not implement, whose stock defaults make the memory-bridge lemmas false as stated | stays config-generated; the generation pins and config hash are gated by `check_pins.sh` |
| `SailConfigured` platform state | the theorems' initial-state hypotheses select SP1's platform on the Lean side: machine mode, no enabled interrupts, `MPRV`/`mseccfg`/PMM off, no HTIF, PMP all-OFF (`h_pmp_off`), and the single RWX PMA region `[2^16, 2^48)` | discharge per-field from SP1's boot/ELF-load contract; the PMA window and PMP-off are the platform selection itself (verification-report §3.2) |
| Native semantic boundary relation | native provider tables must mean the selected program/state | derive from exact Program/Memory/Global system tables |
| `SyscallHandler` | Sail does not implement SP1 host syscalls | `ExecutableSyscallHandler.haltOnly` is now a *concrete* handler for the one claimed syscall (`HALT`), so the halting conclusion rests on a named executable host semantics rather than an opaque relation; every other syscall evaluates to `none` for that handler; the separate inline handler has broader local semantics, without an active-syscall soundness capstone |
| Native `HaltChip` | SP1's ECALL row is a multi-arm dispatcher (`IsZero` selectors for syscall codes 0/3/16/26/240) that also sends on the global `.syscall` bus, which the standalone Halt circuit does not use; `HaltChip` implements the `HALT` arm alone | the Rust oracle exists (`Extracted/SystemOracle/SyscallInstrs.lean`) but no `ChipFaithful` anchor does — whole-row assertion/interaction equality is false between an arm and its dispatcher; the restriction relation is reviewed prose. Close it with a gated-projection anchor and integrate the full syscall table into grounding |
| Native-only public-value buses | Clean localizes public inputs to the verifier row. Native chips therefore communicate values that Rust constrains directly through Exit/PublicValues messages. The instruction anchors exclude these additional kinds; the full syscall anchor instead states an explicit `PublicValueBinding` and an interaction permutation with added messages. | Exit already has the verifier pull and Halt producer. PublicValues still needs an authenticated provider, and active syscalls need an extended terminal-row policy. The local faithfulness theorem does not discharge either integration obligation. |
| 16-bit exit codes | the halt row pins `a0`'s upper three limbs to zero so the single committed `exit_code` cell decodes back to `a0`. Ours, not upstream's: SP1's halt arm bounds `op_b` to a valid field element (`U16CompareOperation` vs `32512`), capping `reduce(op_b)` at `p - 1`, so it never wraps | reproduce SP1's compare instead of pinning limb 1 — widens to upstream's ~31-bit range and retires this row |
| Canonical inline syscall words | The native predicate checks the complete 64-bit register, while the pinned Rust executor dispatches after truncation to 32 bits. Successful Rust dispatch does not imply this predicate. | Retain it as an explicit supported-profile restriction or widen the semantics with a reviewed AIR/host correspondence proof. |
| Native eight-code guard | `CoreSyscallChip` adds a sound/complete fixed lookup of the full prior x5 value to the original syscall instruction circuit. Its raw-constraint theorem needs no Memory guarantees; the canonical fixed-table realization is independent of prover data. | This strengthened component is not yet installed in the 59-table assembly and makes no host-effects or additional Rust-faithfulness claim. WRITE still needs authenticated x12 and buffer reads; HINT_READ needs authenticated padded writes, with the executor's untraced zero-clock convention addressed separately. |
| Preprocessed commitment | verifying key must bind the Program/provider trace | discharge in PCS/ArkLib layer |
| Exact natural balance | execution needs a real multiset, not modular equality | extract with LogUp/GKR soundness and bounds |
| Shard ledger cryptography | cumulative sums and deferred proofs are recursive-proof facts | prove in recursion/verifier layer |
| Standard halt wrapper | needed only for all-eight COMMIT coverage | prove from exact committed ROM |
| Opcode enum and routing source mirror | `SP1Clean/Model/Opcode.lean`'s 53 names/discriminants are kernel-checked against the generated, pin-checked `Extracted/OpcodeTable.lean` artifact by `opcodeTable_matchesExtracted`; the single `supportedChips` descriptor still mirrors `tracing.rs`'s opcode→chip dispatch by hand, while the coverage proofs tie that descriptor to the 25-chip registry and exhaust the extracted opcode alphabet | extract the routing dispatch itself on a future SP1 pin; until then review the one descriptor against `tracing.rs` |

These are theorem inputs or tool/model trust boundaries, not undisclosed Lean axioms.

## Open correctness work

The critical remaining proof is not another instruction chip. It is:

```text
exact instruction tables
  + exact system tables
  + exact public/preprocessed data
  → eventful Sail shard relation
```

Specifically:

- discharge `ExactNativeGlobalContract` from the exact interaction argument: all-channel count
  bounds, State/Memory/Exit integer balance, and the semantic program/boundary binding;
- authenticate and construct the source-backed preprocessing inventory, and close the named
  Range13→Range16 and raw-Global→typed-Memory transformations (the 25 instruction tables and
  complete 30-table provider/system tail are already constructed under those explicit contracts,
  using manufactured padding Halt and empty SyscallInstrs tables);
- prove the mixed ordinary/syscall schedule and exact syscall transcript;
- instantiate `CoreAIRRefinementObligations`;
- compose authenticated shards from boot to HALT; and
- integrate ArkLib with a probabilistic knowledge-soundness theorem.

See [`roadmap.md`](roadmap.md) for the dependency order.

## Reproduction

Run from the repository root:

```bash
lake build --wfail --iofail SP1Clean ToClean ToMathlib ToPolyFun SP1CleanTest
lake test
lake lint
scripts/run_audit.sh
```

The final command validates the compiled libraries against `scripts/trust_policy.json`, writing
only ignored diagnostic reports under `.lake/build/trust/`. The retired `--update` flag fails;
trust exceptions require explicit policy review. No clean-commit stamp is needed to inspect
work in progress, and reports identify the revision and whether tracked inputs differ.

Missing modules, scanner errors, incomplete coverage, proof deferrals, project axioms, forbidden
kernel bypasses, main-library native decision proofs, unapproved native-bitvector proof owners,
and other unknown axioms make the audit fail. The capstone's statement/definition manifest and
extraction/model provenance are checked independently of the axiom policy.
