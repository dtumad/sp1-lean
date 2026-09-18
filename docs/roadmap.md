# Roadmap

## Native Clean core

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
literal equality with the complete outgoing realization. Its identity, composition, clock,
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

## Current state

| Surface | What is proved | Remaining boundary |
|---|---|---|
| Whole instructions | All 25 native chip contracts, Sail bridges, and whole-chip Rust faithfulness anchors | Preserve these while changing ensemble wrappers |
| Full-state semantics | `ExecutionPath`, paired replay, split/join, PolyFun equivalence, finite snapshot comparison, semantic boot/HALT corollaries | AIR certification of both complete boundaries |
| Source and program | Checked finite source, complete registers/configuration/ROM, fixed Program provider, physical fetch/decode agreement | Shared active-clock/resource profile |
| Mixed ledger and grounding | Exhaustive CPU order, complete instruction/host Memory accounting, aligned touches, bounds, refresh elimination, shared carrier and actual replay | Extend the installed host inventory |
| Installed mixed soundness | `HostHintReadCPU.source_execution_with_banks` derives a real local path, exact active event multiset, final PC/clock/frontier values and both final banks from raw constraints/balance | Full outgoing snapshot and Exit |
| Host inventory | HALT, ENTER, COMMIT, COMMIT_DEFERRED, HINT_LEN, HINT_READ are installed; source-backed hint bytes and padded reads are authenticated | WRITE, VERIFY, new-node/word authorization and allocation history |
| Commitment banks | Both physical histories equal the corresponding CPU subsequences, including update arguments and clocks; their endpoints equal the actual replayed banks | Include these equalities in the complete outgoing snapshot |
| Constructive completeness | Existing 55-table ordinary compiler with explicitly narrower admissibility; many mixed component constructors | Full local-segment compiler total on the independent semantic profile |
| Export | Generic typed ensemble export/checker, component witness IR, Rust reference consumer | Complete mixed ensemble inventory and event-to-all-tables compiler export |
| Exact upstream / verifier | Paired 34+6-table exact relation and conditional refinement combinators | Closed exact refinement bundle; cryptographic knowledge soundness separately |

The current mixed witness has 87 physical tables plus its singleton verifier. The selected
`HostHintQueueBoundary.ensemble` installs the source-hint resources and both bank terminals.
Its `bankFinal : HostState` parameter currently binds only the two banks; it is **not** a complete
outgoing-state commitment. Queue cursors and bank endpoints remain internal implementation data.
WRITE and VERIFY are excluded by this instance's actual receiver inventory, not proved as active
cases. This restricted instance is an implementation checkpoint, not the final capstone domain.

The former 55-table `supported_core_native_sound` and ordinary completeness results remain useful
and audited. Their `SemanticBoundaryBinding`, syscall-inactivity, and readiness premises do not
carry over as acceptable assumptions of the new theorem. The 59-table boot assembly and the
checked-source/protected assemblies are retained implementation layers, not alternative public
execution models.

## Implementation order and acceptance

Work from the checked end-to-end targets downward. Each change must identify which target it
advances and finish with the appropriate build/test/audit evidence. Do not introduce a second
execution carrier to make a local proof convenient.

| Milestone | Implementation | Completion criterion |
|---|---|---|
| Statement and ownership | Use `FormalModel.Shard.Executes` and the existing generic AIR interfaces; keep the resource parameter visibly open | Checked targets exist (done); concrete profile and canonical header below still required |
| Semantic resource policy | Fix active clock phase/ranges, actual ordinary-store byte permissions, finite host/queue identity bounds, and channel-count capacity in one semantic profile | Soundness derives every restriction from the AIR; every permitted semantic execution fits; identities need no active-clock phase |
| Complete outgoing boundary | Use the proved bank/CPU agreement; prove complete final Sail/register/RAM/runtime/host agreement; bind the full target and terminal Exit | A changed untouched register/byte, host field, bank, PC/clock, or exit cannot retain acceptance; target equality is a conclusion |
| Full host inventory | Install WRITE/VERIFY effects, x12 and RAM reads, request/reply binding, hook/hint prepends, authenticated allocations and node words | All eight calls grounded on the same evolving host; no static-source-queue or syscall-inactivity restriction |
| Terminal policy | Replace legacy HALT participation with the full syscall HALT path and the native canonical exit range | Nonhalting and empty shards need no dummy HALT; stopped states permit only identities; genuine HALT binds Exit |
| Constructive completeness | Adapt existing routing, transition views, access plans, schedules, providers and row constructors to this exact full-state relation | `CompilerTarget` inhabited without proof inputs or caller readiness/footprint/totality premises; accepted candidates compile and compiled candidates are valid |
| Native composition | Use complete snapshot equality at cuts, prove each piece satisfies its own profile, reuse semantic split/join | Separately certified shards compose; splitting/recompilation handles bounds; boot-to-HALT is a corollary |
| Complete export | Instantiate `EnsembleExport` for the final facade and export the data-only event/provider compiler | Lean/Rust agree on complete tables, fixed lookups, public verifier, interactions and generated witnesses, including padding |
| Review and handoff | Consolidate modules after their consumers use the facade; audit assumptions, negative cases, docs and provenance | One reviewable combined branch/PR with the closed statement and reproducible gates |

**Next proof work:** complete outgoing-state agreement and its verifier binding.
`HostHintReadCPU.source_execution_with_banks` now closes the bank-history step on the same
execution path: complete HostCall matching plus strict CPU/bank clocks identifies each update
subsequence, and the existing host interpreter gives its final bank. No caller bank/CPU order or
successful replay premise is added. Preserve this theorem while deriving complete final
Sail/register/RAM/runtime/host equality and Exit agreement. Work on the semantic capacity/profile
definition alongside this only where needed to fix the public boundary. A profile restriction
may not silently narrow the intended all-eight-call language to fit today's installation.

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
  Local/protected/host projections share these. Ledger projections retain every relevant occurrence;
  State projection alone does not justify projecting Memory or Byte balance.
- `Soundness/Shard/` is the public assembly/contract home. Move live implementation families only
  after establishing their consumers; keep namespaces stable and separate moves from proof changes.
  Existing `Proofs/Completeness/` remains the compiler owner. Do not create another obligations framework.
- Retire duplicate scaffolding only after migrating consumers and census probes. Preserve exact-Core
  contracts and old audited theorems unless an equivalent replacement is proved.

The roadmap owns current status and next actions. Architecture owns module roles and trust
boundaries; the verification report owns external claims and evidence. `AGENTS.md` supplies working
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

`dtumad/core-verification-capstone` already contains the eight-PR predecessor history. Continue on
this combined branch with reviewable commits; do not replay the stack or squash away provenance
merely to produce one PR. Keep the original instruction faithfulness and dump-conformance gates.

Before publication, construct mixed compiled local shards with memory, host effects, nonzero banks,
and queue allocations across cuts; compose them from boot through HALT. Include continuing shards,
empty/stopped identities, reversed/padded physical tables, repeated touches, clock carries and
capacity edges. Negative fixtures must mutate full boundaries, codes/returns, missing/duplicate rows,
queue words/allocations, permissions, and Exit. Inspect the propositions themselves as well as tests.

Every implementation milestone ends with:

```bash
lake build SP1Clean
lake test
lake lint
scripts/run_audit.sh
```

Require zero errors, warnings, stray `info:` notes, proof deferrals, kernel bypasses, and main-library
`native_decide`. Add public declarations to the axiom inventory, independently review dependency
changes, then regenerate committed snapshots from committed source. Final publication also needs
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
to existing Clean declarations follow the documented fork/upstream workflow. No dependency re-pin
is authorized by this roadmap. Nonblocking cleanup includes contract homing, measured proof
factorization, and long-line linting; avoid combining those broad changes with boundary proofs.

Pin changes remain separate reviewed work: follow [extraction](agents/extraction.md),
[Sail provenance](agents/sail-model-provenance.md), and [Clean upstream](agents/clean-upstream.md).
