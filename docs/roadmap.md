# Roadmap

## Native Clean core

The [fork issues](https://github.com/dtumad/sp1-lean/issues) own current progress and next PRs;
[#12](https://github.com/dtumad/sp1-lean/issues/12) tracks the semantic foundations batch.
This document records the durable contract, proof boundaries, semantic findings, and acceptance gates.

The capstone is a sound and complete native Clean AIR for **bounded local RISC-V execution
segments**, with complete Sail/host boundaries and all eight concrete host calls. A segment can
continue, halt, or be empty. Boot-to-HALT is an endpoint corollary. Instruction dispatch, physical
row order, padding, and ledger bookkeeping belong inside the proof.

The intended public statement is:

```text
nativeShardEnsemble(context, source, target).Statement(canonicalHeader)
  ↔ ∃ events, boundedNativeExecution(context, source, target, events)
```

`source` and `target` are the existing `Model.Core.ExecutionSnapshot`; `events` is the existing
`Machine.ExecutionEvent` list. Execution means `Model.Core.ExecutionPath` through the official
Sail state, concrete host state, and clock. The count of semantic events, their 8/264-tick cost,
and physical table heights are distinct. Padding contributes no semantic step.

The checked statement spine is now in
[`FormalModel/Shard.lean`](../SP1Clean/FormalModel/Shard.lean). It requires a checked source and
literal equality with the complete outgoing realization, and ordinary write-byte permission
at every replayed source. Its identity, composition, clock,
and stopped-source laws are proved using the existing path. The AIR and compiler target types in
[`Soundness/Shard/Contract.lean`](../SP1Clean/Soundness/Shard/Contract.lean) reuse `CompleteEnsemble`
and `EnsembleCompiler`, with a conditional equivalence law. **They are not instantiated capstones.**
`Profile` is an explicit, uninstantiated semantic-domain parameter; fixing and enforcing it is
part of the work below. It must never become a caller-supplied readiness or compiler-totality bundle.

The AIR side must remain exactly raw Clean constraints, fixed lookups, and balanced channels.
Do not add execution correctness, provider authenticity, ordering, or grounding as conjuncts to
make soundness hold. Source validity, canonical public fields, complete endpoint agreement, and
the resource restrictions on the semantic side must be checked or derived by the ensemble.

Faithfulness to the pinned SP1 Rust AIR is a separate theorem. Preserve the 25 whole-chip anchors;
native ROM protection and host strengthening do not acquire upstream faithfulness automatically.
The capstone does not prove a cryptographic verifier or acceptance of recursive-proof requests.

## Proved surfaces and open boundaries

| Surface | What is proved | Remaining boundary |
|---|---|---|
| Whole instructions | All 25 native chip contracts, Sail bridges, and whole-chip Rust faithfulness anchors | Preserve these while changing ensemble wrappers |
| Full-state semantics | `ExecutionPath`, paired replay, split/join, PolyFun equivalence, finite snapshot comparison, semantic boot/HALT corollaries | AIR certification of both complete boundaries |
| Source and program | Checked finite source, complete registers/configuration/ROM, fixed Program provider, physical fetch/decode agreement | Shared active-clock/resource profile |
| Mixed ledger and grounding | Exhaustive CPU order, complete instruction/host Memory accounting, aligned touches, bounds, refresh elimination, shared carrier and actual replay | Extend the installed host inventory |
| Installed mixed soundness | `HostHintReadCPU.source_execution_with_memory` derives a real local path with ordinary write permission, exact active event multiset, final PC/clock, all native register/RAM values, absence beyond native RAM, all Sail bookkeeping observations, complete host reconstruction with the supplied optional exit, and the public Exit value for a newly halted endpoint | Complete supplied-target equality |
| Memory endpoint | Complete final and untouched values, executable target comparison equivalent to every GPR and literal Sail RAM equality, native target-value checks, and a complete finite change inventory | Install the checks and enforce complete change coverage in the verifier |
| Sail bookkeeping | The installed path preserves runtime/other registers and derives all three bookkeeping slots: source-controlled retirement count, increment flag, and nextPC from the semantic host suffix and final PC | Bind these observations to the supplied target |
| Host inventory | HALT, ENTER, COMMIT, COMMIT_DEFERRED, HINT_LEN, HINT_READ are installed; source-backed hint bytes and padded reads are authenticated | WRITE, VERIFY, new-node/word authorization and allocation history |
| Host endpoint | Final hints and banks agree with CPU replay; other host fields are preserved; the supplied optional exit equals actual replay status, whose new HALT code equals the public Exit field | Bind the remaining fields of the complete outgoing instance |
| Commitment banks | Both physical histories equal the corresponding CPU subsequences, including update arguments and clocks; their endpoints equal the actual replayed banks | Include these equalities in the complete outgoing snapshot |
| Constructive completeness | Existing 55-table ordinary compiler with explicitly narrower admissibility; many mixed component constructors | Full local-segment compiler total on the independent semantic profile |
| Export | Generic typed ensemble export/checker, component witness IR, Rust reference consumer | Complete mixed ensemble inventory and event-to-all-tables compiler export |
| Exact upstream / verifier | Paired 34+6-table exact relation and conditional refinement combinators | Closed exact refinement bundle; cryptographic knowledge soundness separately |

The current mixed witness has 87 physical tables plus its singleton verifier. The selected
`HostHintQueueBoundary.ensemble` installs the source-hint resources and both bank terminals.
Its `bankFinal : HostState` parameter checks the two banks and optional exit status; it is **not**
a complete outgoing-state commitment. Bank and terminal agreement with the CPU replay are proved.
Queue cursors and bank endpoints remain internal implementation data.
WRITE and VERIFY are excluded by this instance's actual receiver inventory, not proved as active
cases. This restricted instance is an implementation checkpoint, not the final capstone domain.

The former 55-table `supported_core_native_sound` and ordinary completeness results remain useful
and audited. Their `SemanticBoundaryBinding`, syscall-inactivity, and readiness premises do not
carry over as acceptable assumptions of the new theorem. The 59-table boot assembly and the
checked-source/protected assemblies are retained implementation layers, not alternative public
execution models.

## Implementation order and acceptance

Development and review take place in the [fork](https://github.com/dtumad/sp1-lean), using small
PRs based on its current `main`. The first complete instance is the existing native ensemble.
Architecture improvements may precede proof completion when they migrate concrete consumers and
preserve existing claims; an alternative `RiscvAir` implementation is not on the critical path.

| Campaign | Tracker | Delivery order |
|---|---|---|
| A: native capstone | [#12](https://github.com/dtumad/sp1-lean/issues/12) | Audit contract and coverage register → ROM/fetch/write policy → concrete resources → shared carriers/adapters → full boundary → WRITE/VERIFY and allocation → mixed compiler → closed realization/composition |
| B: reusable RISC-V architecture | [#16](https://github.com/dtumad/sp1-lean/issues/16) | Consumer-driven abstractions for A; later the alternative `RiscvAir` instance against the same contract |
| C: export and verified replacement | [#29](https://github.com/dtumad/sp1-lean/issues/29), whole ensemble [#28](https://github.com/dtumad/sp1-lean/issues/28) | Complete ensemble/compiler export → lookup-free backend fixtures and challenges → replacement contract → fixed-profile whole-ensemble cost |
| Maintenance | [#6](https://github.com/dtumad/sp1-lean/issues/6), [#33](https://github.com/dtumad/sp1-lean/issues/33), [#41](https://github.com/dtumad/sp1-lean/issues/41) | Durable Sail fix, module migration, and measured residual hotspots; only block A when a concrete dependency requires them |

The build campaign #43 is complete. The plug-in map from #24 has landed. Campaign A absorbs #20's
remaining claim/consumer decisions: retain the active full-state frontier in the existing build
and CI coverage, retain the cheap exact-refinement stack and the 25 chip anchors, and migrate
constructors needed by the mixed compiler with their consumers. A module absent from today's
headline closure is not thereby dead. Retire other scaffolding only after checking imports,
tests, export consumers and documented release claims, and preserving any released result by an adapter.
The [coverage register](overview.md#coverage-register) owns exclusions and their exit criteria;
[architecture](architecture.md) separates semantic choices, reusable ledger arguments and local
implementation obligations.

Work from the checked end-to-end targets downward. Each change must identify which target it
advances and finish with the appropriate build/test/audit evidence. Do not introduce a second
execution carrier to make a local proof convenient.

| Milestone | Implementation | Completion criterion |
|---|---|---|
| Statement and ownership | Use `FormalModel.Shard.Executes` and the existing generic AIR interfaces; keep the resource parameter visibly open | Checked targets exist (done); concrete profile and canonical header below still required |
| Semantic resource policy | Fix active clock phase/ranges, actual ordinary-store byte permissions, finite host/queue identity bounds, and channel-count capacity in one semantic profile | Soundness derives every restriction from the AIR; every permitted semantic execution fits; identities need no active-clock phase |
| Complete outgoing boundary | Use the proved bank/CPU agreement; prove complete final Sail/register/RAM/runtime/host agreement; bind the full target and terminal Exit | A changed untouched register/byte, host field, bank, PC/clock, or exit cannot retain acceptance; target equality is a conclusion |
| Full host inventory | Install WRITE/VERIFY effects, x12 and RAM reads, request/reply binding, hook/hint prepends, authenticated allocations and node words | All eight calls grounded on the same evolving host; no static-source-queue or syscall-inactivity restriction |
| Terminal policy | Remove legacy padding participation; active mixed HALT uses the canonical syscall handler, and receipt/replay agreement is proved | Nonhalting and empty shards need no dummy HALT; stopped states permit only identities; genuine HALT binds Exit |
| Constructive completeness | Adapt existing routing, transition views, access plans, schedules, providers and row constructors to this exact full-state relation | `CompilerTarget` inhabited without proof inputs or caller readiness/footprint/totality premises; accepted candidates compile and compiled candidates are valid |
| Native composition | Use complete snapshot equality at cuts, prove each piece satisfies its own profile, reuse semantic split/join | Separately certified shards compose; splitting/recompilation handles bounds; boot-to-HALT is a corollary |
| Complete export | Instantiate `EnsembleExport` for the final facade and export the data-only event/provider compiler | Lean/Rust agree on complete tables, fixed lookups, public verifier, interactions and generated witnesses, including padding |
| Review and handoff | Consolidate modules after their consumers use the facade; audit assumptions, negative cases, docs and provenance | One reviewable combined branch/PR with the closed statement and reproducible gates |

**First hardening work:** close the ROM/fetch/store-policy gap and replace the free `Profile`
parameter with data-only resource limits and a fixed derived admissibility predicate. Preserve
the one `ExecutionPath`, prove fetch agreement and policy preservation, and establish nonempty
semantic fixtures before claiming a concrete profile. Generic `Realizes.admissible` remains a
general predicate; it is the concrete native domain that must be independently fixed.

Host dispatch now checks the complete ECALL word in actual Sail memory as well as the committed
program. The finite snapshot interpreter uses the same byte check, and its soundness/completeness
commuting theorems are retained. Installed host/HALT grounding derives the new guard from its
existing ROM invariant, without an additional capstone premise. Regressions reject missing zero
bytes, each corrupted code byte, and corruption at a continuation.

`InstructionWrite` computes ordinary write spans from the decoded instruction and incoming base
register, using the shared access-plan arithmetic. Its byte policy counts same-value stores and
uses the exact SB/SH/SW/SD width rather than the enclosing RAM cell. All four store-chip adapters
bind their AIR-authorized writes to this independent policy at the actual PC and live operands.
`HostHintReadCPU.GroundingCarrier.romLoaded_prefix` derives ROM preservation at every successful
prefix of the installed mixed replay from the checked source and AIR permissions. Regressions
cover signed offsets, all four widths, partial-cell writes beside ROM, malformed footprints,
and a same-value store accepted by the unprotected AIR but rejected by the protected AIR.
The native `Executes` contract now requires `ExecutionPath.WritesPermitted`, which observes the
incoming state at every ordinary occurrence using the shared replay. Even a resource `Profile`
of `True` cannot admit a same-value ROM store. Permission composes and splits at the actual
complete boundary; empty identities and non-writing instructions remain permitted. The raw
`ExecutionPath` is unchanged. `GroundingCarrier.writesPermitted` derives the policy from the
installed mixed AIR at each actual incoming state; `source_execution_with_memory` retains it
alongside all existing endpoint observations. The registry proof covers all 25 chips through
their existing contracts and grounded readiness. ROM preservation/fetch agreement on the
independent semantic domain (including branch/JALR edges), and the remaining free resource
limits, are still open. Installed-AIR preservation does not discharge those semantic obligations.

The shared fetch/dispatch and retirement-tail proofs live below the circuits in
`Model/Semantics/Sail{StepReduction,Fetch,Retirement}`. The existing chip bridges consume these
same declarations. `ExecutionSourceValid.fetch_eq` identifies a committed current instruction
with official Sail fetch from the complete realized source; it requires no successor fetch.
The arbitrary-step preservation laws remain the next semantic proof obligation in #12.

`ExecutionPath.ordinaryHalt_trace` and `ordinaryHalt_trajectory` connect the complete path to the
legacy fixed-handler view over the ordinary/HALT fragment. The installed AIR's
`source_execution_ordinaryHalt` derives that trace from `source_execution` and retains its complete
path, permissions, physical inventory and endpoint conclusions. Agreement holds through the last
covered boundary; the two trajectory definitions deliberately differ after the tape. Mixed host
calls retain the single evolving host/clock in paired replay.

**Next boundary work:** bind the complete supplied outgoing snapshot to the already-derived
Sail/register/RAM/runtime/host endpoint. For Memory, install the proved native final-value checks
and enforce coverage of every computed source-to-target change; then bind the complete
Sail register map (including key presence), bookkeeping/runtime and host fields.
Terminal receipt/replay agreement is closed.
`HostHintReadCPU.source_execution_with_memory` identifies every integer register and aligned RAM
cell below `2^48`, including locations absent from the final inventory, and excludes entries outside
that range. It retains complete host reconstruction, Sail runtime/other-register frames, and all
three bookkeeping observations. The source's official machine-mode filter controls `minstret`,
which advances by the ordinary-event count modulo `2^64`; host calls add no retirement. An empty
ordinary inventory preserves the incoming increment flag. `nextPcAfter` uses the semantic tape's
trailing host PCs and public final PC, preserving incoming nextPC when there is no ordinary event.
Thus the endpoint formulas require no exposed instruction-row order or new caller premise.

`HostHintReadBookkeeping` derives those formulas from the same grounded chip effects and paired
replay. `Model/Core/SailBookkeeping` owns the data-only observations; it does not introduce a second
execution model. `MemorySnapshot.checkFinal` compares all final-record values with the target and
checks preservation everywhere else using the finite supports of both sparse memories.
`GroundingCarrier.checkFinal_iff` proves this executable check equivalent to every integer-register
observation and literal Sail RAM equality on the installed replay. Record bounds and uniqueness
are derived from its original AIR. The combined `source_execution_with_memory` theorem now retains
this equivalence on the same execution without a new caller premise; its final assembly lives in
`HostHintReadFinalSnapshot`, while the location/frame proofs stay in `HostHintReadFinalMemory`.
The comparison includes low RAM, absent outside-window keys,
and changes at locations omitted from the final inventory; obsolete sparse history is immaterial.
Its positive and negative regressions exercise the data check, not an installed boundary circuit.
`FinalRegisterValue` and `FinalRamValue` now authenticate target values through fixed lookups,
with proved semantic contracts and proof-independent constructors. Source and target fixed tables
have distinct export identities; both use the same byte/word lookup implementation. The RAM check
authenticates every byte, while the original RAM finalizer retains alignment/address provenance.
`FinalMemoryReceipt` composes that original finalizer without changing its width, assertions,
lookups, or old ledgers, and publishes its complete record on a separate register or RAM channel.
Exact producer/consumer receipt equations are proved. Circuit regressions check all assertions,
fixed lookups and Byte semantics, and reject forged values, partial-word mutations and missing,
duplicate, wrong-clock or wrong-kind receipts. All four circuits export; this is a component and
handoff fixture, not an installed mixed-AIR boundary.
`MemorySnapshot.changes` computes the unique finite set of all changed native locations from both
snapshots, including low RAM. Its membership theorem and `checkFinal_iff_changes` prove that target
value authentication plus coverage of this computed set is exactly the complete endpoint check.
The next installation must enforce these demands in the verifier and connect the actual final
inventory to the target checkers. It must retain their extra Byte demands: preservation of the old
Memory/State ledgers does not establish projected Byte balance. Neither the endpoint check nor
change coverage may become a caller premise of the final capstone.
Complete supplied-target equality is still not checked by the ensemble. The native
verifier now checks `bankFinal.exitCode` through a separate complete-word terminal receipt and
requires an already-stopped source to preserve its exact optional exit.
`HostTerminalLedger.receipts` derives the complete HALT-word inventory from raw constraints and
balance. `HostHintReadTerminal.legacy_rows_nil` excludes legacy active events from the actual
carrier. Full HostCall matching then connects those words to the same CPU tape, and
`ExecutionPath.exit_receipts` proves its semantic terminal law for arbitrary local paths.
`GroundingCarrier.final_terminal` concludes `target.host.exitCode = bankFinal.exitCode` without
an extra source-running or event-semantic premise. The combined theorem now uses that supplied
status directly in its reconstructed host, covering running, newly halted, and stopped identities.
`HostHintReadCPU.GroundingCarrier.final_exit` now binds every newly halted endpoint's concrete 32-bit code to
the public Exit field without modular aliases. `LocalCoreExit` classifies the complete physical
ledger and applies the existing generic gated-unit balance theorem. The wrapper and appended
host components preserve this projection even though they do not preserve Memory balance.
The mixed assembly now constrains the legacy table to padding and routes active HALT through
`HostHaltChip`, which emits the terminal receipt. The old local assembly is unchanged. The padding
wrapper projects every original row and channel, so the existing mixed execution proof still
applies. Full installed-AIR regressions cover syscall HALT above the legacy 16-bit limit,
HALT-zero, forged public codes, duplicate producers, and an extra padding producer.
`rejectsSuppliedExitStatus` replaces the reproduced gap: changing the supplied exit to `none` or
`some 7` after HALT-zero is rejected. `terminalIdentity` checks running/stopped identities,
unchanged wide exit codes, fabricated HALT-zero, and attempts to restart a stopped source.
The syscall HALT fixture needs no legacy row; continuing/empty witnesses still need the legacy
padding emission. Removing that participation rule remains open.
Work on the semantic capacity/profile definition alongside this only where needed to fix the
public boundary; it may not narrow the intended all-eight-call language to today's installation.

The full boundary verifier must take source/target snapshots as public instance data, with a
canonical bounded header, and derive private queue/bank endpoints internally. A caller must not
supply a queue path, bank history, finite target-realization proof, or grounded execution. Whether
those complete instance data later become succinct authenticated commitments is a separate layer.

## Model and module ownership

- `Model/Core/Execution{,Path,Replay,Boot,Snapshot}.lean` owns full machine/host/clock execution.
  `FormalModel/Shard.lean` gives its native shard contract; it adds no state or trace representation.
- `Model/Machine/ExecutionEvent` vocabulary is shared. `EventExecutionTrace` and
  `CoreShardSemanticWitness` remain the legacy ordinary/exact-Core views. They lack the complete
  evolving host and must not be asserted equivalent to full snapshots without an explicit adapter.
- `InstructionChipId`, `InstructionRouting`, `SP1TransitionView`, and existing access plans remain
  the common identities, decoder/routing and compiler views. Never copy an opcode dispatch table.
- `ExecutionCarrier` and `CoreExecutionTrajectory` own physical occurrence transport and replay.
  Native, local and host grounding use the same carrier, including the event walk derived from
  State balance. Their theorem entry points remain instance adapters; the native ordinary/HALT
  handler view still needs a whole-path adapter to the full stateful execution contract.
  Local/protected/host projections share these. Ledger projections retain every relevant occurrence;
  State projection alone does not justify projecting Memory or Byte balance.
- `Soundness/Shard/` is the public assembly/contract home. Move live implementation families only
  after establishing their consumers; keep namespaces stable and separate moves from proof changes.
  Existing `Proofs/Completeness/` remains the compiler owner. Do not create another obligations framework.
- Retire duplicate scaffolding only after migrating consumers and preserving documented release claims. Preserve exact-Core
  contracts and old audited theorems unless an equivalent replacement is proved.

The fork campaign issues own current status and next actions. This roadmap owns the durable
contract and acceptance gates. Architecture owns module roles and trust boundaries; the verification report owns external claims and evidence. `AGENTS.md` supplies working
rules, not a second progress log. Historical development details remain available in git history.

## Semantic findings to retain

- Full boundary equality includes absent Sail register keys, all RAM bytes, runtime counters/output,
  host I/O and requests/replies, both banks, exit status, and clock. Equal PC/clock or equal touched
  Memory inventories is insufficient. Sparse snapshots compare their full realizations extensionally.
- Zero-time source records are local seeds at arbitrary shard clocks. They do not assert historical
  last-access times. Refresh elimination does not prove truth about rewritten historical events.
- Active CPU clocks use phase 1 modulo 8. Range-only source validation is broader; empty identities
  remain legal at any checked source clock. The full profile must account for field/count bounds as
  well as CPU steps: a short host trace can still allocate or access many bytes.
- Store permission concerns every byte actually written, including same-value writes. Preservation
  of ROM contents alone is weaker. HINT_READ writes mandatory final padding even for aligned or empty
  hints; a final written byte at `2^48 - 1` is allowed when the one-past endpoint is `2^48`.
- Record binding alone does not imply canonical field encoding. Queue cursor balance alone admitted
  swapped markers/repeated addresses; node length, every word marker, destination, and byte permission
  must all be authenticated. Fresh allocation must authorize complete bytes, not just a node identity.
- Duplicate instruction/handler pairs can balance HostCall alone. CPU ordering excludes them. WRITE's
  extra x12 pair is lost by projecting to the original syscall table; retain the full mixed Memory ledger.
- The old unrestricted HINT_LEN assembly admitted a forged return plus matching final record. The
  installed source-hint replay now derives the return from actual queue history. WRITE-generated queues
  still need authenticated allocation integration; the older assembly is not an alternative capstone.
- Running (`none`) and HALT-zero (`some 0`) are different host states. The current Exit code alone
  cannot certify that distinction; endpoint binding must authenticate terminal status as well as value.
- Legacy HALT imposes a 16-bit exit domain and currently needs an inactive HALT row even in a nonhalting
  fixture. The intended native syscall HALT accepts canonical below-characteristic 32-bit exits.
- Native commitment banks support repeated overwrites. The pinned SyscallInstrs COMMIT constraints
  compare against fixed public digests; a faithful exact refinement needs an explicit compatible domain
  or a different target. Do not remove native overwrites to disguise this difference.
- Native host observations are explicit: ENTER returns zero; VERIFY records a proof request, not
  cryptographic acceptance; hook replies are request-bound inputs. The pinned minimal executor's
  deferred/VERIFY behavior and native observations are distinct comparison obligations.
- Rust untraced hint writes reset access clocks to zero. Native authenticated host timing is separate.
  Empty unaligned WRITE byte coverage can differ from Rust's untraced aligned reads. Preserve these
  findings when defining exact refinement and conformance scope.

## Capstone integration and review

The eight-PR predecessor history is already contained in the fork's `main`. Do not replay it.
Open reviewable fork PRs for the milestones above, with semantic changes separate from mechanical
moves and proof-performance work. Keep instruction faithfulness and dump-conformance gates.
Every full-stack change carries `ci:alignment` before merge. Each PR names the target advanced,
the exact semantic/assumption change (if any), and its closed proofs and validation evidence.

Before publication, construct mixed compiled local shards with memory, host effects, nonzero banks,
and queue allocations across cuts; compose them from boot through HALT. Include continuing shards,
empty/stopped identities, reversed/padded physical tables, repeated touches, clock carries and
capacity edges. Negative fixtures must mutate full boundaries, codes/returns, missing/duplicate rows,
queue words/allocations, permissions, and Exit. Inspect the propositions themselves as well as tests.

Every implementation milestone ends with:

```bash
lake build --wfail --iofail SP1Clean SP1CleanTest
lake test
lake lint
scripts/run_audit.sh
```

Require zero errors, warnings, stray `info:` notes, proof deferrals, kernel bypasses, and main-library
`native_decide`. Run the [compiled-library trust policy](trust-policy.md) on current oleans and
review the capstone contract manifest when its definitions change. Independently review dependency
changes; adding ordinary declarations needs no trust registration or committed census update. Final publication also needs
complete ensemble/witgen export checks, existing Rust dump/interpreter conformance, regeneration
checks at unchanged pins, and fresh-build CI. The PR must state the actual theorem, native profile,
trust base, and remaining exact/cryptographic work, linking the eight predecessor PRs.

## Separate follow-ups

**Exact SP1 Core refinement.** Keep `sp1_air_refinement` and `sp1_air_sound` reserved until a closed
`CoreAIRRefinementObligations` construction exists. Today's `_of_obligations` results consume the
paired 34-table execution and six-table memory-boundary relation. Remaining work includes fixed
Byte/Range/Program meaning and coverage, source-backed canonical inventory/uniqueness, count bounds,
State/Memory balance, system ordering and public/global boundary meaning, and the semantic loader
binding. Empty preprocessing assertion lists do not establish these facts. Program identity and
initial global memory values depend on authenticated preprocessing/verifying-key commitments;
exact byte-address boundary order also needs alignment/consumability before it yields native cell
uniqueness. Range13-to-Range16 and raw Global-to-typed-Memory changes are not literal ledger
permutations. Do not assume COMMIT-row existence from an operand constraint on rows that exist.

**Verified verifier.** Pin Core first. An executable Lean verifier/Rust agreement theorem, ArkLib
knowledge soundness with a cryptographic error bound, and AIR-to-Sail interpretation are independent
layers. No unconditional deterministic `verifyCore = true → valid execution` claim. Compressed,
Plonk, Groth16, and succinct boundary commitments are separate targets.

**Sharing and cleanup.** The leanerVM review supports sharing generic Clean/PolyFun machinery,
not replacing this execution/host model. Keep generic additions in `ToClean`/`ToMathlib`; modifications
to existing Clean declarations follow the documented upstream workflow (`docs/agents/clean-upstream.md`).
No dependency re-pin is authorized by this roadmap. Nonblocking cleanup includes contract homing, measured proof
factorization, and long-line linting; avoid combining those broad changes with boundary proofs.

**Lint debt (2026-09-20 baseline).** The package runs Mathlib's standard syntactic linter set and
Batteries' full environment-linter set (`AGENTS.md` § Linters); every finding below is debt to
fix, not an accepted exception, and the numbers are the burn-down baseline. Environment linters
(`scripts/nolints.json`, 4 235 entries): `docBlame` 2 808 (2 001 hand-written, 807 generated),
`defsWithUnderscore` 979 (699 / 280 — rename to camelCase; keep snake_case only where an identifier
mirrors a Rust or Sail one, with `@[nolint defsWithUnderscore]` at the site), `unusedArguments` 432
(284 / 148 — mostly the `localLength_eq`/`channelsWith*_eq` rfl-lemmas' section variables and the
`D`-suffix contract lifts), `simpNF` 12, `simpComm` 4. Generated declarations are fixed in
`update_extracted.py`, never by hand. Syntactic linters (temporary `weak.linter.<x> = false`
opt-outs in `lakefile.toml`, unique sites / files): `style.longLine` 10 578 / 722, `style.show`
326 / 75, `style.whitespace` 218 / 10, `flexible` 191 / 64, `style.multiGoal` 25 / 5,
`style.openClassical` 21 / 21, `style.emptyLine` 15 / 5, `unusedDecidableInType` 10 / 5;
`style.header` (~950 files, the Mathlib copyright header — adopt once the header form for this
dual-licensed tree is chosen); `style.longFile` (32 hand-written files over 1 500 lines, linter left
at its default of off). Work the list down by directory in small PRs, core first, each ending with
`scripts/update_nolints.sh`; delete an opt-out line the moment its count is 0.

Pin changes remain separate reviewed work: follow [extraction](agents/extraction.md),
[Sail provenance](agents/sail-model-provenance.md), and [Clean upstream](agents/clean-upstream.md).
