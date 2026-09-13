# The audit surface

*Machine-checked by `scripts/check_audit_surface.sh` (run by `scripts/run_audit.sh` and the CI
`guards` job): every declaration named below must still exist at the file named beside it. Adding a
premise, or removing one, changes this table — that is the point.*

## Why this list exists, and why it is short

The external PR #110 review (§9) states the right criterion, and it is not "theorems versus lemmas".
For a closed theorem `T` in an environment with no `sorryAx` and no project axiom, write `Stmt(T)`
for the constants reachable from `T`'s **type** and `Prf(T)` for those reachable from its **value**.
Everything in `Prf(T) \ Stmt(T)` is a proof-only artefact: if it were wrong the kernel would have
rejected `T`. The entire risk of *proving the wrong thing* lives in `Stmt(T)` and in the ambient
instance context.

That is what makes auditing this repository tractable. The review measured the split for
the then-current (model-scheduled) `supported_core_native_sound` — the headline has since moved
to the plain-Sail statement, which only shrinks the statement closure: 13,943 constants in the proof closure, 10,665 in the statement
closure, of which 7,487 are proof-typed (inert for meaning) — leaving **3,178 data/definition-typed
constants across 243 modules** as the real surface, and confirming the repository's own claim that
`FormalModel/Contracts/` is where it concentrates.

This file is the human-sized version: the definitions where a defect would be undetectable by the
kernel, each with the question it decides. Reading these, plus `FormalModel/Contracts/` and the 25
`Native/Chips/*/Defs.lean`, is reading the part that can be *wrong* rather than merely unproved.

## The claim itself

| Declaration | File | Question it decides |
|---|---|---|
| `WitnessRelation.Relation` | `SP1Clean/FormalModel/Relations.lean` | What a statement/witness relation is |
| `Relation.restrict` | `SP1Clean/FormalModel/Relations.lean` | How capacity/profile domains refine one relation without changing its witness representation |
| `SP1Prime` | `SP1Clean/Model/SP1Field.lean` | The one concrete KoalaBear characteristic used by exact/test instantiations |
| `WitnessRelation.Sound` | `SP1Clean/FormalModel/Relations.lean` | Direction and shape of the soundness claim |
| `WitnessRelation.Complete` | `SP1Clean/FormalModel/Relations.lean` | Direction and shape of the completeness claim |
| `WitnessRelation.FunctionalCompleteness` | `SP1Clean/FormalModel/Relations.lean` | The proof-independent reverse witness map; no witness-preservation law is implicit |
| `WitnessRelation.Correct` | `SP1Clean/FormalModel/Relations.lean` | Both existential directions, hence public-language equality rather than witness inversion |
| `ExecutionState` | `SP1Clean/Model/Core/Execution.lean` | Complete Sail/host/clock continuity, including RAM and terminal status; not yet an authenticated AIR boundary encoding |
| `ExecutionSnapshot` | `SP1Clean/Model/Core/ExecutionSnapshot.lean` | Complete finite boundary data, including all Sail registers and runtime/host state |
| `ExecutionSnapshot.equivalent_iff` | `SP1Clean/Model/Core/ExecutionSnapshot.lean` | Whether finite comparison is literal equality of complete realized execution states |
| `memorySnapshot_realizes` | `SP1Clean/Model/Core/ExecutionSnapshot.lean` | Whether initialized full snapshots supply the existing source providers' complete register/RAM observations |
| `ExecutionSnapshot.hostStep?` | `SP1Clean/Model/Core/HostSnapshot.lean` | Which host transition is computed directly from finite source data |
| `ExecutionSnapshot.hostStep?_realize` | `SP1Clean/Model/Core/HostSnapshot.lean` | Whether sparse host execution agrees with the Sail adapter on the full state, including padded writes |
| `ExecutionSnapshot.hostStep?_sound` | `SP1Clean/Model/Core/HostSnapshot.lean` | Whether successful finite host execution yields the genuine semantic transition |
| `ExecutionSnapshot.hostStep?_complete` | `SP1Clean/Model/Core/HostSnapshot.lean` | Whether successful Sail host execution has a computed finite successor without a readiness witness |
| `MemorySnapshot.Realizes` | `SP1Clean/Model/Core/MemorySnapshot.lean` | All integer registers and every supported byte agree with Sail; excludes other Sail/host/clock state and is not an added ensemble premise |
| `equivalent_iff` | `SP1Clean/Model/Core/MemorySnapshot.lean` | Finite executable comparison is exact RAM/register equality, including untouched locations and zero-default gaps |
| `SnapshotSpec` | `SP1Clean/FormalModel/Contracts/SnapshotMemory.lean` | Canonical zero-time local source record authenticated against a fixed finite snapshot; no historical timestamp claim |
| `circuit` | `SP1Clean/Proofs/Chips/SnapshotRegisterProvider.lean` | Fixed lookup binds the register index and all four value limbs; soundness, completeness, and a total semantic-index constructor |
| `circuit` | `SP1Clean/Proofs/Chips/SnapshotRamProvider.lean` | Authenticated arbitrary source RAM and exact aligned-address constructor domain; boot is a specialization |
| `circuit` | `SP1Clean/Proofs/Chips/OrderedSnapshotProvider.lean` | Existing canonical ordering wrapper instantiated for snapshot records, with internal constructor obligations discharged |
| `ExecutionStep` | `SP1Clean/Model/Core/Execution.lean` | Normal official-Sail retirement or concrete stateful host execution, with no transition from a halted source |
| `ExecutionSegment` | `SP1Clean/Model/Core/ExecutionPath.lean` | Exactly the requested number of local semantic steps, independent of boot, HALT, padding, and AIR witness layout |
| `executionSystem` | `SP1Clean/Model/Core/ExecutionPath.lean` | The equivalent PolyFun finite-path view; directions are actual semantic steps |
| `replayHost?` | `SP1Clean/Model/Core/ExecutionReplay.lean` | Checks the full event against actual interpreter observations and threads the next host state |
| `replayStep?` | `SP1Clean/Model/Core/ExecutionReplay.lean` | Replays source/event data; ordinary success still needs normal-retirement evidence, unlike the host success equivalence |
| `BootToHalt` | `SP1Clean/Model/Core/ExecutionBoot.lean` | Boot and terminal status as endpoint conditions on the same local semantic segment; not yet a native AIR corollary |
| `SupportedCoreStatement` | `SP1Clean/FormalModel/Execution.lean` | The one program/public-boundary statement shared by both proof directions |
| `CoreProfile.WithinOrdinaryRowLimit` | `SP1Clean/FormalModel/CoreProfile.lean` | The one numeric Core row-budget policy used by both witness representations |
| `SupportedCoreNativeRelation` | `SP1Clean/Soundness/AIR.lean` | The hypothesis side: the ensemble algebra, the semantic boundary binding, and the interim `SyscallTableInactive` placeholder |
| `SupportedCoreNativeShardRelation` | `SP1Clean/Soundness/AIR.lean` | The same native relation restricted to the pinned active-row budget |
| `supported_core_native_sound` | `SP1Clean/Soundness/AIR.lean` | The headline theorem: the plain-Sail conclusion, no model parameter, no schedule hypothesis |
| `supported_core_native_sound_scheduled` | `SP1Clean/Soundness/AIR.lean` | The model-scheduled corollary — the shard-composition seam |
| `supported_core_native_shard_sound` | `SP1Clean/Soundness/AIR.lean` | Capacity-aligned soundness into the one canonical semantic relation |
| `SupportedCoreLocalExecutionRelation` | `SP1Clean/FormalModel/Execution.lean` | What the model-scheduled conclusion actually says |
| `SupportedCoreSailRelation` | `SP1Clean/FormalModel/Execution.lean` | The plain-Sail conclusion, now a dichotomy: an `OrdinaryRun` (a normally-retiring run between the committed endpoints at eight ticks per step, committed exit code zero) or a `HaltedRun` (a normally-retiring prefix reaching a genuine `SP1Halted` state, parked at `haltPc` one syscall window later) — with, in both, a well-formed Memory boundary agreeing with real location content at both ends |
| `SailSegmentWitness.HaltedRun` | `SP1Clean/FormalModel/Execution.lean` | Exactly what a halting shard is claimed to be |
| `SupportedCoreHaltGrounding` | `SP1Clean/Soundness/GroundingInternal.lean` | The halted grounding certificate: the eight-tick prefix, the one live Halt row, and its pulled operands' currency |
| `haltedSail_of_haltGrounding` | `SP1Clean/Soundness/HaltExecution.lean` | How that certificate becomes a genuine `SP1Halted` Sail state |
| `SupportedCoreNativeOrdinaryShardRelation` | `SP1Clean/Soundness/AIR.lean` | The halt-free sub-relation the deterministic compiler still targets — the exact scope of the totality-conditional correctness statements |
| `supported_core_boot_to_halt_single_shard` | `SP1Clean/Soundness/BootHalt.lean` | The first whole-execution claim: from the entry point with zeroed registers to a genuine `SP1Halted` state carrying the committed exit code, on one shard that both boots and halts |
| `SupportedCoreBootHaltRelation` | `SP1Clean/Soundness/BootHalt.lean` | Exactly what that corollary assumes: the ensemble algebra, a *boot* semantic boundary, and a live Halt row |
| `SailSegmentWitness` | `SP1Clean/FormalModel/Execution.lean` | The proof-free run/boundary carrier of the plain-Sail conclusion |
| `exists_populated_memoryBoundary` | `SP1Clean/Soundness/MemoryBoundaryTruth.lean` | How the boundary is populated: per canonically-addressed, genesis-backed committed finalize record — the two population filters are named follow-up, not soundness gaps |
| `ShardStartState` | `SP1Clean/FormalModel/Execution.lean` | What the conclusion pins about the shard's start state (public pc, ROM, configuration) |
| `supportedCoreLocalExecution_of_sailRelation` | `SP1Clean/FormalModel/Execution.lean` | The no-strength-lost adapter from the plain-Sail form back to the model-scheduled form |
| `Machine.CoreShardSemanticWitness` | `SP1Clean/Model/Machine/Shard.lean` | The one proof-free program/Memory-boundary/initial-state/event carrier shared by native and exact Core |
| `CoreShardSemanticWitness.evaluatedTrace` | `SP1Clean/Model/Machine/Shard.lean` | The total proof-independent evaluator consumed by the trace compiler |
| `CoreShardExecutionRelation` | `SP1Clean/FormalModel/CoreShard.lean` | The one semantic relation skeleton specialized by native and exact Core |
| `CoreShardContract` | `SP1Clean/FormalModel/CoreShard.lean` | The narrow extension hook: five explicit fields, no defaults — every trivial instantiation is a visible choice |
| `SupportedCoreShardExecutionRelation` | `SP1Clean/FormalModel/SupportedShard.lean` | The normal-retirement, 25-route, capacity-bounded specialization shared by both native directions — its case is boundary, ordinary execution, or terminal canonical halt |
| `ExecutableSyscallHandler.haltOnly` | `SP1Clean/Model/Machine/Shard.lean` | The concrete host semantics of the supported profile: the canonical HALT parks the machine at `haltPc`, every other syscall is outside the profile |
| `EventExecutionTrace.HaltsWith` | `SP1Clean/Model/Machine/EventExecution.lean` | What "the shard halts with this exit code" means: terminal canonical-HALT syscall + `SP1Halted` one step before it |
| `SupportedHaltingTrace` | `SP1Clean/FormalModel/SupportedShard.lean` | The supported halting discipline: supported ordinary prefix within the row budget; the terminal transition's laws travel in the shared case |
| `SupportedCoreOrdinaryShardExecutionRelation` | `SP1Clean/FormalModel/SupportedShard.lean` | The syscall-free sub-language the deterministic compiler targets — the totality-conditional correctness/language-equality statements are relative to it |
| `SP1TransitionView` | `SP1Clean/Model/Semantics/TransitionView.lean` | The one proof-free fetch/decode/route/access projection shared by both directions |
| `projectSP1Transition?` | `SP1Clean/Model/Semantics/TransitionView.lean` | How an operational transition is projected, including the explicit optional access-plan result |
| `SupportedSP1Transition` | `SP1Clean/FormalModel/SupportedShard.lean` | What “supported” requires of each transition, expressed through that shared view |
| `LocalSegmentMatchesBoundary` | `SP1Clean/FormalModel/Execution.lean` | How the conclusion is pinned to the public endpoints |

## Which machine is being verified

| Declaration | File | Question it decides |
|---|---|---|
| `sp1Ensemble` | `SP1Clean/Soundness/SP1Ensemble.lean` | The 55-table native machine and its seven channels |
| `haltTable` | `SP1Clean/Soundness/BumpDecode.lean` | Which physical table witnesses a halting shard (stable index 53) |
| `sp1Tables` | `SP1Clean/Soundness/SP1Ensemble.lean` | The 25 instruction tables |
| `sp1ProviderTables` | `SP1Clean/Soundness/SP1Ensemble.lean` | The 30 provider/boundary tables and their order |
| `sp1StateVerifierMain` | `SP1Clean/Soundness/SP1Ensemble.lean` | The boundary row, incl. its public-limb range checks |
| `SP1StateBoundary` | `SP1Clean/FormalModel/Contracts/PublicValues.lean` | What is public: the range-checked State-endpoint limbs, the `exit_code` cell now bound by the Exit hand-off, and the still-unconstrained `is_execution_shard`/digest cells awaiting COMMIT semantics |
| `HaltChip.Spec` | `SP1Clean/FormalModel/Contracts/SystemChips.lean` | What one Halt row means: the `+264`/`haltPc` State edge, the committed `ECALL` fetch, `t0 = HALT`, and the 16-bit exit-code pinning of `a0` |
| `Channels.exitChannel` | `SP1Clean/Model/Channels.lean` | The fifth bus and its deliberately trivial local guarantee (its whole content is balance) |
| `witness_exitMessages_eq` | `SP1Clean/Soundness/ExitAccounting.lean` | What Exit balance forces: exactly one physical Halt row, whose hand-off message *is* the committed `exit_code` |
| `witness_exit_code_zero_of_haltFree` | `SP1Clean/Soundness/ExitAccounting.lean` | Why an ordinary shard's committed exit code must be zero |
| `supportedChip_fetchDiscriminantShape` | `SP1Clean/Soundness/FetchDiscriminant.lean` | Why no instruction row can claim the `ECALL` opcode — the per-chip step that recovers decode-only Program truth from the re-based committed-fragment provider |
| `ChipKind` | `SP1Clean/Soundness/ChipRow.lean` | The per-chip interface (`chipSpec`, `advanceReady`, `view`, `advance`) — 25 registrations |
| `RowEffect` | `SP1Clean/Soundness/RowEffectDefs.lean` | What each row is proved to *do* |
| `ValueOperandsBound` | `SP1Clean/Soundness/RowEffectDefs.lean` | How a row's operands are tied to machine state |

## The assumed semantic boundary

The image-authenticated boot assembly and the local snapshot assembly derive the following boundary
facts directly. Neither has yet replaced the older execution theorem whose assumptions are listed
below. The local assembly's complete Sail/host endpoint binding and timed grounding remain open.

| Declaration | File | Question it decides |
|---|---|---|
| `BootFor` | `SP1Clean/FormalModel/Contracts/NativeCoreBoundary.lean` | Which initial clock and PC the new verifier constrains |
| `ensemble` | `SP1Clean/Soundness/NativeCoreEnsemble.lean` | Which physical tables, channels, and verifier form the new assembly |
| `initial_records_authentic` | `SP1Clean/Soundness/NativeCoreBoundaries.lean` | Whether raw AIR constraints and balance authenticate boot memory |
| `initial_records_locations_nodup` | `SP1Clean/Soundness/NativeCoreBoundaries.lean` | Whether the actual ledger forbids duplicate initial locations |
| `program_row_committed` | `SP1Clean/Soundness/NativeCoreBoundaries.lean` | Whether physical Program rows match the checked ROM and official Sail |
| `ExecutionSourceValid` | `SP1Clean/Model/Core/SourceExecution.lean` | Complete source initialization/configuration, program and ROM validity, and PC/clock ranges |
| `checkExecutionSource_iff` | `SP1Clean/Model/Core/SourceExecution.lean` | Whether the finite source checker is exactly its semantic contract |
| `SourceFor` | `SP1Clean/FormalModel/Contracts/LocalCoreBoundary.lean` | How the actual source PC/clock is bound into the public incoming State token |
| `SourceFor.clock` | `SP1Clean/FormalModel/Contracts/LocalCoreBoundary.lean` | Whether field decoding recovers the source clock without aliases |
| `SourceFor.pc` | `SP1Clean/FormalModel/Contracts/LocalCoreBoundary.lean` | Whether three PC limbs recover the actual checked Sail PC |
| `source_state_encoding` | `SP1Clean/Soundness/LocalCoreSourceGrounding.lean` | Whether raw local AIR constraints and balance bind the incoming State message to the complete source |
| `initialStateTruth` | `SP1Clean/Soundness/LocalCoreSourceGrounding.lean` | Whether the checked source supplies State truth on any trajectory starting there |
| `memoryInitialFrontier_content` | `SP1Clean/Soundness/LocalCoreSourceGrounding.lean` | Whether physical source records authenticate actual complete-state Sail contents |
| `memoryInitialFrontier_liveOK` | `SP1Clean/Soundness/LocalCoreSourceGrounding.lean` | Whether local genesis currency and source-timestamp admissibility follow without semantic premises |
| `view_spec` | `SP1Clean/Soundness/FinalMemoryEnsemble.lean` | Whether finalizer contracts follow from raw constraints and Byte guarantees before Memory grounding |
| `memoryBoundary_records_perm` | `SP1Clean/Soundness/CoreMemoryBalance.lean` | Shared reduction of complete-message balance with unit boundary records to an exact permutation |
| `final_records_canonical` | `SP1Clean/Soundness/LocalCoreFinalBoundary.lean` | Whether the local assembly authenticates final addresses independently of value/clock currency |
| `final_records_locations_nodup` | `SP1Clean/Soundness/LocalCoreFinalBoundary.lean` | Whether local final ordering excludes repeated locations across all finalizer rows |
| `final_memory_interactions` | `SP1Clean/Soundness/LocalCoreFinalBoundary.lean` | Whether final records are exactly the physical negative Memory ledger |
| `memory_interactions` | `SP1Clean/Soundness/LocalCoreMemory.lean` | Whether the local source/interior/final decomposition retains every actual Memory interaction |
| `memory_records_perm` | `SP1Clean/Soundness/LocalCoreMemory.lean` | Whether source records plus all interior pushes permute to final records plus all interior pulls |
| `memory_frontier_balance` | `SP1Clean/Soundness/LocalCoreMemory.lean` | Whether unique source/final frontiers satisfy the timed engine's per-location equation without semantic premises |
| `program_pull_committed_of_sources` | `SP1Clean/Soundness/CoreProgramBalance.lean` | Whether checked ROM is the sole possible producer under actual count-bounded Program balance |
| `ExecutionRow.edge_eq_facts` | `SP1Clean/Soundness/CoreExecutionRow.lean` | Whether both assemblies use identical State edges and Memory row facts |
| `verifier_state_interactions_of_main` | `SP1Clean/Soundness/CoreTableProjection.lean` | Whether a verifier preserving the standard State circuit emits exactly the two public endpoints |
| `program_pull_committed` | `SP1Clean/Soundness/LocalCoreProgram.lean` | Whether every active local fetch authenticates ROM/Sail membership without execution truth |
| `instructionRows_constraints` | `SP1Clean/Soundness/LocalCoreDecode.lean` | Whether decoding retains original cells and raw constraints |
| `executionRows_memory_balance` | `SP1Clean/Soundness/LocalCoreRows.lean` | Whether all mixed instruction occurrences and refresh pairs satisfy exact Memory frontier balance |
| `state_endpointBalanced` | `SP1Clean/Soundness/LocalCoreState.lean` | Whether the actual local State ledger authenticates both endpoints |
| `executionRows_ordered` | `SP1Clean/Soundness/LocalCoreOrder.lean` | Whether raw constraints and balance construct an exhaustive mixed State walk |
| `ordered_rows_timing` | `SP1Clean/Soundness/LocalCoreOrder.lean` | Whether the local walk preserves the incoming clock residue and exact event widths |
| `hintReturnNeedsHostBinding` | `SP1CleanTest/Core/LocalCore.lean` | Concrete AIR-valid forged HINT_LEN return against the supplied finite host; records the remaining host-result binding obligation |
| `SourceValid` | `SP1Clean/Model/Core/SourceSnapshot.lean` | Finite program/decoding validity, x0, and all source ROM bytes, including untouched code |
| `checkSource_iff` | `SP1Clean/Model/Core/SourceSnapshot.lean` | Whether executable source validation is exactly the semantic contract |
| `ensemble` | `SP1Clean/Soundness/LocalCoreEnsemble.lean` | The 59-table assembly with a complete source and its bound incoming PC/clock |
| `verifier` | `SP1Clean/Soundness/LocalCoreEnsemble.lean` | Which source configuration/ranges, actual incoming token, and inventory endpoints are constrained |
| `source_records_authentic` | `SP1Clean/Soundness/LocalCoreBoundaries.lean` | Whether raw AIR constraints and balance authenticate arbitrary source records |
| `source_records_locations_nodup` | `SP1Clean/Soundness/LocalCoreBoundaries.lean` | Whether the actual local ledger forbids duplicate source locations |
| `source_memory_interactions` | `SP1Clean/Soundness/LocalCoreBoundaries.lean` | Whether the physical source Memory ledger is exactly the decoded unit pushes |
| `public_boundary` | `SP1Clean/Soundness/LocalCoreBoundaries.lean` | Whether raw constraints and balance imply canonical public fields and finite source validity |

The public premise `SemanticBoundaryBinding` is regrouped for reading: three commitment facts
(program well-formedness, `Commit.StatementFor`, the committed initial clock), the 3-field
`ShardStartState`, the code/data-separation contract, and the 4-field external bundle
`ProviderBindingContracts`. The commitment/start-state conjuncts follow from a configured initial
state, a committed program, and a canonical `ProverData` choice; the bundle is the assumed core.
`InitialBoundaryFacts` is the equivalent flat proof-layer carrier the timed-grounding engine
consumes — `semanticBoundaryBinding_iff` is the kernel-checked equivalence, superseding the
earlier prose observation that "seven of eleven fields are derivable". (The PR #110 review
tabulated a twelfth premise, `MemoryPullTimestampHighBound`; it is *derived* from the produced
side of the capstone's own per-location Memory balance and no longer exists as a declaration.)

| Declaration | File | Question it decides |
|---|---|---|
| `SemanticBoundaryBinding` | `SP1Clean/Soundness/ProviderBindings.lean` | The regrouped public boundary premise |
| `ProviderBindingContracts` | `SP1Clean/Soundness/ProviderBindings.lean` | The four-field assumed core: provider content + uniqueness |
| `InitialBoundaryFacts` | `SP1Clean/Soundness/ProviderBindings.lean` | The equivalent flat proof-layer carrier |
| `semanticBoundaryBinding_iff` | `SP1Clean/Soundness/ProviderBindings.lean` | The recorded equivalence between the two |
| `ProgramProviderBound` | `SP1Clean/Soundness/ProviderBindings.lean` | Program-table content (assumed; §7.3 — needs C1) |
| `MemoryInitProviderBound` | `SP1Clean/Soundness/ProviderBindings.lean` | Memory-init content at the boundary |
| `MemoryInitProviderUnique` | `SP1Clean/Soundness/ProviderBindings.lean` | One init record per location — not derivable from balance |
| `MemoryFinalizeProviderUnique` | `SP1Clean/Soundness/ProviderBindings.lean` | One finalize pull per location — likewise |

The uniqueness pair is the sharpest residual — Clean balance cannot force it,
upstream's mechanism is the MemoryGlobal strictly-increasing-address chain this ensemble omits, and
the premise is stated per `locOf` (8-byte cell) while that chain orders exact byte addresses. That
granularity gap is recorded on the definitions themselves.

## Whether the target is the real Sail model

| Declaration | File | Question it decides |
|---|---|---|
| `GuestProgram` | `SP1Clean/Model/Semantics/GuestProgram.lean` | What a "program" is, and its guards |
| `SailStep` | `SP1Clean/Model/Semantics/GuestProgram.lean` | One step of the real generated interpreter |
| `SailRetiresNormally` | `SP1Clean/Model/Semantics/GuestProgram.lean` | Excludes trap/illegal/wait exits by recording the official `Retire_Success` branch |
| `SailChain` | `SP1Clean/Model/Semantics/GuestProgram.lean` | A multi-step run |
| `SailRetireChain` | `SP1Clean/Model/Semantics/GuestProgram.lean` | A multi-step run in which every step retires normally; downgrades via `toSailChain` |
| `SailConfigured` | `SP1Clean/Model/Semantics/GuestProgram.lean` | Which platform state is assumed (incl. the single RWX PMA region) |
| `ConfiguredDecode` | `SP1Clean/Model/Semantics/GuestProgram.lean` | The one word/instruction decode fact shared by Program truth and shard semantics |
| `SailCodeMemoryCompatible` | `SP1Clean/Model/Semantics/GuestProgram.lean` | The code/data separation contract — self-modifying code excluded by assumption |
| `SP1MachineModel` | `SP1Clean/Model/Machine/Execution.lean` | The clock model |
| `SP1MachineModel.UsesOrdinarySchedule` | `SP1Clean/Model/Machine/Execution.lean` | Which schedule the conclusion is quantified over |
| `decodedInROM` | `SP1Clean/Model/Semantics/Decode.lean` | The decode correspondence |
| `instrToProgramRow` | `SP1Clean/Model/Semantics/Decode.lean` | How a decoded instruction projects to a Program row |
| `Commit.progOf` | `SP1Clean/Model/Semantics/ProgramCommitment.lean` | How the program is bound to prover data |
| `Commit.CanonicalEncoding` | `SP1Clean/Model/Semantics/ProgramCommitment.lean` | The range/singleton conditions that make decoding canonical |
| `Commit.StatementFor` | `SP1Clean/Model/Semantics/ProgramCommitment.lean` | The committed-program statement |

## Faithfulness to Rust, and the transport

| Declaration | File | Question it decides |
|---|---|---|
| `ChipFaithful` | `SP1Clean/Faithful/ChipOracle.lean` | What "faithful to Rust" means |
| `ChipOracle` | `SP1Clean/Faithful/ChipOracle.lean` | The generated Rust side of the comparison |
| `FaithfulPropFor` | `SP1Clean/Faithful/SupportedMachine.lean` | That an anchor is bound to *its own* table's theorem |
| `CanonicalPreprocessedInventory` | `SP1Clean/Composition/PreprocessedProviders.lean` | Caller-supplied provider carriers + projected-key `Nodup` |
| `PreprocessedProviderContract` | `SP1Clean/Composition/PreprocessedProviders.lean` | Caller-supplied row-local provider semantics |
| `PreprocessedProviderRecountContract` | `SP1Clean/Composition/PreprocessedProviders.lean` | Coverage, nonpositivity, canonical capacity |
| `ExactNativeGlobalContract` | `SP1Clean/Composition/CoreArtifact.lean` | What the artifact still assumes globally |
| `CoreAIR.ShardWitness` | `SP1Clean/FormalModel/CoreAIRRelation.lean` | The paired execution and Memory-boundary exact witness; neither cluster can be omitted from the capstone source |
| `CoreAIR.Current.ShardRelation` | `SP1Clean/Faithful/CoreAIR.lean` | Exact 34+6-table validity on that paired witness |
| `CoreAIRExternalContext` | `SP1Clean/Soundness/CoreAIR.lean` | The total decoder and six loader/platform/program facts that are not AIR consequences |
| `CoreAIRRefinementObligations` | `SP1Clean/Soundness/CoreAIR.lean` | The 12-field exact AIR-to-common-shard proof bundle (`executionCase` open) |
| `sp1_air_refinement_of_obligations` | `SP1Clean/Soundness/CoreAIR.lean` | The pinned-SP1Prime deterministic map from the paired exact source to the common shard relation |
| `System.localValid_of_relationFor` | `SP1Clean/FormalModel/CoreAIRRelation.lean` | The stable eliminator from an exact cluster relation to one row's complete local validity |

## Exact Core system-table semantics

The generated `Extracted/SystemOracle` lists are the sole complete interaction ledgers. The
hand-written semantic layer names typed messages and proves that selected generated endpoints use
them; it does not maintain a second list that could drift from extraction.

| Declaration | File | Question it decides |
|---|---|---|
| `Channels.SyscallMsg` | `SP1Clean/Model/BusMessages.lean` | The one nine-field v6.4.0 Syscall tuple shared by producer and consumer |
| `transportMemoryBumpRow_input` | `SP1Clean/Composition/CoreSystemSemantics.lean` | Which native MemoryBump input the exact row reconstructs |
| `transportStateBumpRow_input` | `SP1Clean/Composition/CoreSystemSemantics.lean` | Which native StateBump input the exact row reconstructs |
| `SyscallCoreView` | `SP1Clean/Composition/CoreSystemSemantics.lean` | All ten SyscallCore columns grouped around the shared message |
| `syscallCore_assertions_iff` | `SP1Clean/Composition/CoreSystemSemantics.lean` | Complete local SyscallCore assertion semantics: exactly selector binarity |
| `syscallCore_syscall_receive_mem` | `SP1Clean/Composition/CoreSystemSemantics.lean` | The typed message is the exact generated Syscall receive |
| `syscallCore_rowFacts_of_relation` | `SP1Clean/Composition/CoreSystemSemantics.lean` | Exact execution validity fans the local contract out to every SyscallCore row |
| `SyscallInstrsSyscallView` | `SP1Clean/Composition/CoreSystemSemantics.lean` | The Syscall message and `send_to_table` byte projected from a 65-column instruction row |
| `syscallInstrs_syscall_send_mem` | `SP1Clean/Composition/CoreSystemSemantics.lean` | The same typed message is the exact generated Syscall send |
| `MemoryLocalView` | `SP1Clean/Composition/CoreSystemSemantics.lean` | All twenty MemoryLocal columns and their typed Memory endpoints |
| `memoryLocal_assertions_iff` | `SP1Clean/Composition/CoreSystemSemantics.lean` | Complete local MemoryLocal assertions: selector binarity plus both byte recombinations |
| `memoryLocal_memory_endpoints_mem` | `SP1Clean/Composition/CoreSystemSemantics.lean` | The typed initial/final messages are the exact generated Memory receive/send |
| `memoryLocal_rowFacts_of_relation` | `SP1Clean/Composition/CoreSystemSemantics.lean` | Exact execution validity fans the complete local contract out to every MemoryLocal row |

| Core table | Landed semantic projection | Still required for full refinement |
|---|---|---|
| MemoryBump | Exact native row transport and decoded input | Per-location order/timestamp consequences after provider balance |
| StateBump | Exact native row transport and decoded input | Sparse-clock State ordering after balance |
| SyscallCore | Complete local assertions and typed Syscall receive | Cross-table transcript consistency and handler meaning |
| SyscallInstrs | Typed Syscall send with its generated table byte | Full instruction-row law and transcript consistency |
| MemoryLocal | Complete local assertions and typed Memory endpoints | Range, per-location order, and Global-record meaning |
| Global | No semantic reinterpretation in this unit | Public boundary and cumulative interaction facts |

## The completeness direction

| Declaration | File | Question it decides |
|---|---|---|
| `SupportedCoreTraceWitness` | `SP1Clean/Proofs/Completeness/Assembly.lean` | What a supplied trace is |
| `compileExecution` | `SP1Clean/Proofs/Completeness/ExecutionCompiler.lean` | The proof-independent chronological all-25 compiler |
| `compileLocatedTransitions?_exists_of_views` | `SP1Clean/Proofs/Completeness/ExecutionCompiler.lean` | Why the chronological fold itself is total once each retained shared view compiles |
| `SupportedCoreShardExecutionValid.compileExecution?_exists_of_instructionEventsReady` | `SP1Clean/Proofs/Completeness/ExecutionCompiler.lean` | Why common semantic validity already discharges fetch/decode/image/route projection, leaving only one-row event readiness |
| `nativeTrace` | `SP1Clean/Proofs/Completeness/NativeTraceCompiler.lean` | The unique 55-table trace produced from a statement and execution |
| `NativeTraceReady` | `SP1Clean/Proofs/Completeness/NativeTraceCompiler.lean` | The remaining named semantic/representation facts about that exact compiler output |
| `NativeTraceAdmissible` | `SP1Clean/Proofs/Completeness/NativeTraceCompiler.lean` | The residual compiler/output predicate, without copied semantic validity or row budget |
| `NativeShardTraceTotal` | `SP1Clean/Proofs/Completeness/NativeTraceCompiler.lean` | The one domain-closure theorem still separating bounded completeness from full correctness |
| `NativeStateRowProjection` | `SP1Clean/Proofs/Completeness/NativeTraceCompiler.lean` | The sole physical-row projection seam for State instruction accesses |
| `NativeMemoryRowProjection` | `SP1Clean/Proofs/Completeness/NativeTraceCompiler.lean` | The two physical-row projection seams for instruction and MemoryBump accesses |
| `NativeMemoryGenesis` | `SP1Clean/Proofs/Completeness/NativeTraceCompiler.lean` | The field-free initial-memory fact, before any Clean provider representation |
| `NativeProgramRowProjection` | `SP1Clean/Proofs/Completeness/NativeTraceCompiler.lean` | The physical Program pulls' link to retained compiler decodes |
| `nativeTrace_stateAgreement` | `SP1Clean/Proofs/Completeness/NativeStateAgreement.lean` | State projection plus generated boundaries/bumps yields the complete State ledger |
| `nativeTrace_memoryLedgerPermHandoffChains` | `SP1Clean/Proofs/Completeness/NativeMemoryAgreement.lean` | Physical Memory tables regroup to the canonical per-location histories |
| `nativeTrace_memoryInitProviderBound` | `SP1Clean/Proofs/Completeness/NativeMemoryAgreement.lean` | Field-free Memory genesis grounds the generated init-provider rows |
| `nativeTrace_programProviderBound` | `SP1Clean/Proofs/Completeness/NativeProgramAgreement.lean` | Retained decode agreement grounds the generated Program-provider rows |
| `NativeTraceReady.semanticBoundary` | `SP1Clean/Proofs/Completeness/NativeBoundaryAgreement.lean` | The derived Program/Memory provider facts joined with the exact semantic boundary |
| `SupportedCoreNativeAdmissibleShardRelation` | `SP1Clean/Proofs/Completeness/NativeTraceCompiler.lean` | The canonical semantic source restricted only by facts about its deterministic compiled trace |
| `supported_core_native_functionalCompleteness` | `SP1Clean/Soundness/NativeCompleteness.lean` | The proof-independent semantic-execution-to-AIR witness map |
| `supported_core_native_shard_functionalCompleteness` | `SP1Clean/Soundness/NativeCompleteness.lean` | The same map into the capacity-aligned native relation |
| `supported_core_native_complete` | `SP1Clean/Soundness/NativeCompleteness.lean` | Existential whole-ensemble completeness on the admissible image |
| `sp1Ensemble_statement_of_supported_execution` | `SP1Clean/Soundness/NativeCompleteness.lean` | The direct Clean `Ensemble.Statement` consequence |
| `anchorExecution_admissible` | `SP1CleanTest/Audit/NativeCompletenessNonVacuity.lean` | A concrete zero-event common shard witness jointly inhabits every admissibility premise |
| `anchorExecution_yields_airWitness` | `SP1CleanTest/Audit/NativeCompletenessNonVacuity.lean` | The functional capstone returns its literal compiled 55-table witness |
| `activeView_compiled_event_exists` | `SP1CleanTest/Audit/ActiveNativeCompleteness.lean` | The official-Sail self-jump's projected input compiles to the exact JAL circuit event used by the active trace |
| `activeExecution_semantic` | `SP1CleanTest/Audit/ActiveNativeCompleteness.lean` | A genuine one-transition Sail execution inhabits the shared supported-shard semantic relation |
| `activeTrace_bounded_roundTrip` | `SP1CleanTest/Audit/ActiveNativeCompleteness.lean` | The nonempty circuit-built AIR witness lies in the bounded native relation and soundness reconstructs a semantic witness |
| `SupportedCoreGeneratedTraceRelation` | `SP1Clean/Soundness/AIRCompleteness.lean` | The lower generated-trace assembly boundary, kept distinct from semantic completeness |

Completeness now covers the deterministic compiler's full 55-table admissible image: all 25 instruction
families, refresh-aware StateBump/MemoryBump placement, canonical Byte/Range/Program closure, both
Memory boundary tables, the State verifier row, constraints, and all seven channel balances.  It is
still narrower than the common bounded semantic relation. Its compiler domain needs
access-plan success (notably complete source/target RAM cells), registry-wide event-validity,
Memory-genesis, representation-agreement, and interaction-footprint theorems. Configured-state
decode stability is no longer on that list: it is attached to the shared `SP1TransitionView` by
`SupportedSP1Transition` and is derived registry-wide. Soundness and completeness now use the
same bounded native/semantic relation pair; `NativeShardTraceTotal` is the single remaining
condition for the proved `supported_core_native_shard_correct_of_totality` and its language-equality
corollary. No abstract certificate or existential AIR witness hides those facts, and unconditional
public-language equality remains reserved until that transparent condition is closed.

## Outside this list

`EnsembleWitness.Constraints` and `BalancedChannels` decide what "the AIR is satisfied" means, but
they live upstream in Clean (`Clean/Air/FlatEnsemble.lean`, `Clean/Air/Balance.lean`) and are pinned
by the Clean dependency, not by this repository. The generated `Extracted/**Oracle**` column
structures, `asserts` and `interactions` lists are the Rust side of faithfulness; they are
auto-generated and gated by `update_extracted.py` plus the regeneration workflow, not audited by
hand. Both are named here so a reader knows they were considered and placed, not forgotten.
