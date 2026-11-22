import Lean
import SP1Clean.Export.InstalledBumpTables
import SP1Clean.Export.WriteProbeCapacity
import SP1Clean.Proofs.Completeness.MemoryVersionHistory
import SP1CleanTest.Alignment.Core.MixedStateBumpEdges
import SP1Clean.Soundness.Shard.Contract
import SP1Clean.Proofs.Completeness.PublicHeader
import SP1Clean.Proofs.Completeness.MixedAccessFrontier
import SP1Clean.Proofs.Completeness.MixedInstructionBuckets
import SP1Clean.Proofs.Completeness.WriteObservations
import SP1Clean.Export.InstalledVerifierCapacity
import SP1Clean.Proofs.Completeness.HistoricalHintCapacity
import SP1Clean.Soundness.HostRegisteredCalls
import SP1Clean.Export.ShortShardChain
import SP1CleanTest.Alignment.Core.FixedRamCapacity
import SP1Clean.Export.FixedImageCapacity
import SP1Clean.Export.FixedHintCapacity
import SP1Clean.Proofs.Completeness.HintReadLedger
import SP1Clean.Proofs.Completeness.HintReadCapacity
import SP1Clean.Export.InstalledHintCompleteness
import SP1Clean.Proofs.Completeness.ObservationCapacity
import SP1Clean.Proofs.Completeness.HintInventory
import SP1Clean.Proofs.Chips.HostControlPopulate
import SP1Clean.Proofs.Completeness.ObservationData
import SP1Clean.Proofs.Completeness.MixedInstructionTables
import SP1Clean.Proofs.Completeness.MixedSyscallRows
import SP1Clean.Proofs.Completeness.WriteObservationCuts
import SP1Clean.Export.CompiledOrdinaryPreset

/-! # Compiled native capstone contract audit

The examples pin the currently conditional target types, independently spelling out the raw
acceptance and complete-state interpretation. They do not instantiate the missing targets.
The command writes a dependency manifest to `CAPSTONE_SURFACE_OUT`: declaration types and
definition bodies are followed, but theorem proof bodies are not. External declarations form
the boundary supplied by the immutable dependency pins. Structural fingerprints detect drift;
they are not cryptographic commitments or a substitute for reviewing the definitions.

Run through `scripts/check_capstone_contract.py`, which builds the dependency first, checks
completion and diagnostics, and diffs the manifest. No main-library declaration is introduced.
-/

open SP1Clean SP1Clean.Semantics SP1Clean.Machine SP1Clean.FormalModel.Shard
  SP1Clean.Soundness.Shard Air.Flat

section Contract

variable {p : ℕ} [Fact p.Prime]
variable (ensemble : Ensemble (ZMod p) SP1PublicIO) (limits : ResourceLimits)
  (commitments : CommitmentStatement) (image : ProgramImage) (source target : ExecutionSnapshot) (header : SP1PublicIO (ZMod p))

example (heights : List ℕ) : ensemble.Statement Balance.logUp header heights ↔
    ensemble.interactionsFit Balance.logUp heights ∧
    ∃ witness : EnsembleWitness ensemble,
      witness.publicInput = header ∧ witness.heights = heights ∧
        witness.Constraints ∧ witness.Balanced Balance.logUp := Iff.rfl

example : SoundnessTarget ensemble limits commitments image source target =
    (∀ publicInput heights, True → ensemble.Statement Balance.logUp publicInput heights →
      ∃ events, (sp1Machine p image).Trace source.realize events target.realize ∧
        publicInput = SP1StateBoundary.ofExecution source target commitments ∧ ExecutionSourceValid image source ∧
        nativeProfile limits p image source target events ∧
        ExecutionPath.ReleaseLinks (policy p image) image.program source.realize events ∧
        commitments.WellFormed p ∧ commitments.Matches events) := rfl

example : CompilerTarget ensemble limits commitments image source target =
    EnsembleCompiler ensemble Balance.logUp (List ExecutionEvent)
      (fun publicInput events => (sp1Machine p image).Trace source.realize events target.realize ∧
        publicInput = SP1StateBoundary.ofExecution source target commitments ∧ ExecutionSourceValid image source ∧
        nativeProfile limits p image source target events ∧
        ExecutionPath.ReleaseLinks (policy p image) image.program source.realize events ∧
        commitments.WellFormed p ∧ commitments.Matches events) := rfl

-- Together the targets are exactly a realization of the SP1 machine.
example (sound : SoundnessTarget ensemble limits commitments image source target)
    (compiler : CompilerTarget ensemble limits commitments image source target) :
    Realizes (sp1Machine p image) ensemble Balance.logUp (boundary source target)
      (admissible limits commitments image source target) :=
  ⟨sound, compiler⟩

example (sound : SoundnessTarget ensemble limits commitments image source target)
    (compiler : CompilerTarget ensemble limits commitments image source target) :
    (∃ heights, ensemble.Statement Balance.logUp (SP1StateBoundary.ofExecution source target commitments) heights) ↔ ∃ events, ReleaseStatementExecution limits p commitments image source target events :=
  SP1Clean.Soundness.Shard.statement_iff sound compiler

end Contract

section NativeTraceContract

open SP1Clean.Soundness SP1Clean.Channels SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
variable {image : ProgramImage} {source target : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)}
  {commitments : CommitmentStatement} {header : SP1PublicIO (ZMod p)}

-- Pin the headline theorem's application surface independently of its proof.
attribute [local irreducible] HostObserved.ensemble
example (fresh : (CommitmentDeclaration.source (p := p) commitments).circuit.name ∉
      (installed image source target final).tables.map (·.circuit.name))
    (registered : CommitmentDeclaration.channel.toRaw ∈
      (installed image source target final).channels)
    (heights : List ℕ)
    (accepted : (CommitmentEnsemble.install commitments
      (installed image source target final) fresh registered).Statement .logUp header heights) :
    SailTrace commitments image source target final header :=
  sail_trace accepted

example :
    SailTrace commitments image source target final header ↔
      ExecutionSourceValid image source ∧ header.SourceFor source ∧ SailBoundary.Spec source target header ∧
        CommitmentBoundary.Spec commitments header ∧
        ∃ (events : List ExecutionEvent) (actual : ExecutionState),
          (sp1Machine p image).Trace source.realize events actual ∧
          commitments.Matches events ∧
          (∀ event ∈ events, HostReceiptProfile.event true event) ∧
          ExecutionPath.Encoded (SP1Clean.FormalModel.Shard.policy p image) image.program source.realize events ∧
          ExecutionPath.ReleaseLinks (SP1Clean.FormalModel.Shard.policy p image) image.program source.realize events ∧
          SP1Clean.FormalModel.Shard.DynamicMatch source target events ∧ Endpoint source target final header events actual := Iff.rfl

-- These are complete boundary maps, not just values at accessed addresses.
example {events : List ExecutionEvent} {actual : ExecutionState}
    (endpoint : Endpoint source target final header events actual) :
    actual.sail.mem = target.sail.memorySnapshot.memory.toSailMemory (2 ^ 48) ∧
      (∀ index, actual.sail.get_reg? index = some (target.sail.memorySnapshot.read (.reg index))) ∧
      actual.clock = StateMsg.timeNat (finalBoundaryStateMessage header) :=
  ⟨endpoint.ram, endpoint.registers, endpoint.clock⟩

end NativeTraceContract

namespace CapstoneContractAudit

open Lean

/-- Exact declarations whose types/definitions determine the audited target and machine view. -/
def roots : Array Name := #[
  ``SP1Clean.Soundness.Shard.statement_iff,
  ``SP1Clean.Soundness.Shard.SoundnessTarget,
  ``SP1Clean.Soundness.Shard.CompilerTarget,
  ``SP1Clean.Soundness.Shard.SailTrace,
  ``SP1Clean.Soundness.Shard.Endpoint,
  ``SP1Clean.Soundness.Shard.sail_trace,
  ``SP1Clean.Export.InstalledAssembly.proverStatement_iff,
  ``SP1Clean.Export.InstalledAssembly.statement_iff_fixedCursor,
  ``SP1Clean.Export.InstalledAssembly.trace_of_statement,
  ``SP1Clean.Export.InstalledAssembly.execution_of_statement,
  ``SP1Clean.Export.InstalledAssembly.header_of_statement,
  ``SP1Clean.Export.InstalledAssembly.native_short_soundnessTarget,
  ``SP1Clean.Export.InstalledAssembly.native_resources_of_statement,
  ``SP1Clean.Export.InstalledAssembly.release_statement_iff_of_statement,
  ``SP1Clean.Export.InstalledAssembly.native_release_statement_iff_peak,
  ``SP1Clean.Export.InstalledAssembly.native_release_of_short_statement,
  ``SP1Clean.Export.InstalledAssembly.native_release_of_short_halt,
  ``SP1Clean.Export.InstalledAssembly.AcceptedChain.short_release,
  ``SP1Clean.Export.InstalledAssembly.soundness,
  ``SP1Clean.Export.InstalledAssembly.AcceptedChain.soundness,
  ``SP1Clean.Export.InstalledAssembly.AcceptedChain.boot_to_halt,
  ``SP1Clean.TraceGen.statementExecution_headerChecks,
  ``SP1Clean.Export.InstalledAssembly.fixedProviderPreset_base_fits,
  ``SP1Clean.Export.InstalledAssembly.fixedProviderPreset_capacity,
  ``SP1Clean.Export.InstalledAssembly.interactionsFit_grow_iff,
  ``SP1Clean.TraceGen.WriteObservations.read?_eq_some_iff,
  ``SP1Clean.TraceGen.WriteObservations.of_admissibleExecution,
  ``SP1Clean.TraceGen.WriteObservations.packets_at,
  ``SP1Clean.Export.InstalledAssembly.fixedProviderPreset_write_probe_bound,
  ``SP1Clean.TraceGen.releaseAdmissibleExecution_instructionBuckets,
  ``SP1Clean.TraceGen.releaseAdmissibleExecution_instructionTables,
  ``SP1Clean.TraceGen.InstalledInstructionTables.generation_padding,
  ``SP1Clean.TraceGen.InstalledInstructionTables.table_receipts,
  ``SP1Clean.TraceGen.InstalledInstructionTables.receipt_weights,
  ``SP1Clean.TraceGen.WriteObservations.installed_cuts,
  ``SP1Clean.Soundness.WriteObservationHistory.versionIntervals_effects,
  ``SP1Clean.TraceGen.WriteObservations.installed_versions,
  ``SP1Clean.TraceGen.WriteObservations.checkPacket_iff_versions,
  ``SP1Clean.TraceGen.MemoryHistoryAccess.matchingValues_of_balance,
  ``SP1Clean.TraceGen.MemoryLocationHistory.heldAt_interval,
  ``SP1Clean.TraceGen.MemoryLocationHistory.heldAt_final,
  ``SP1Clean.Export.InstalledAssembly.fixedProviderPreset_ordinary_capacity,
  ``SP1Clean.Export.InstalledAssembly.fixedProviderPreset_ordinary_base_fits,
  ``SP1Clean.Export.InstalledAssembly.fixedProviderPreset_compiled_ordinary_fits,
  ``SP1Clean.Export.InstalledAssembly.observation_constructed_heights,
  ``SP1Clean.Export.InstalledAssembly.fixedProviderPreset_observation_base_fits,
  ``SP1Clean.TraceGen.admissibleExecution_syscallPushedState,
  ``SP1Clean.TraceGen.admissibleExecution_ordinaryPushedState,
  ``SP1Clean.TraceGen.MixedBumpInput.stateBump?_eq_none_iff,
  ``SP1Clean.TraceGen.routeBumpInputs?_at,
  ``SP1Clean.TraceGen.admissibleExecution_routeMixedRows,
  ``SP1Clean.TraceGen.routeMixedRows?_at,
  ``SP1Clean.TraceGen.admissibleExecution_syscallInstruction,
  ``SP1Clean.TraceGen.admissibleExecution_syscallInputs,
  ``SP1Clean.TraceGen.syscallInstruction_stateMessages,
  ``SP1Clean.TraceGen.admissibleExecution_mixedBumpInventory,
  ``SP1Clean.Export.InstalledAssembly.bump_constructed_tables,
  ``SP1Clean.Export.InstalledAssembly.fixedProviderPreset_bump_base_fits,
  ``SP1CleanTest.MixedStateBumpEdges.low_pc_carry_at_full_upper_limbs,
  ``SP1CleanTest.MixedStateBumpEdges.clock_carry_into_last_window,
  ``SP1CleanTest.MixedStateBumpEdges.pc_carry_into_last_top_limb,
  ``SP1CleanTest.MixedStateBumpEdges.clock_carry_past_last_window,
  ``SP1CleanTest.MixedStateBumpEdges.pc_carry_past_last_top_limb,
  ``SP1Clean.FormalModel.Shard.Executes.header_halt,
  ``SP1Clean.TraceGen.HintReadTransfers.of_admissibleExecution,
  ``SP1Clean.TraceGen.HintReadTransfers.tables_cursor_closed,
  ``SP1Clean.TraceGen.admissibleExecution_compile_from_prefix,
  ``SP1Clean.TraceGen.releaseAdmissibleExecution_compile_from_prefix,
  ``SP1Clean.TraceGen.admissibleExecution_historicalHintCapacity,
  ``SP1Clean.TraceGen.admissibleExecution_observationWitness,
  ``SP1Clean.TraceGen.admissibleExecution_observationData,
  ``SP1Clean.TraceGen.admissibleExecution_observationFits,
  ``SP1Clean.TraceGen.admissibleExecution_hintInventory,
  ``SP1Clean.HostControl.noop_spec_of_run,
  ``SP1Clean.HostNoopChip.run_of_spec,
  ``SP1Clean.HostControl.choice_spec_of_run,
  ``SP1Clean.Soundness.HostRegisteredCalls.noopTable_component,
  ``SP1Clean.Soundness.HostRegisteredCalls.receipt_heights,
  ``SP1Clean.Soundness.HostRegisteredCalls.classified,
  ``SP1Clean.Semantics.HostReceiptProfile.installed_code_iff,
  ``SP1Clean.Export.InstalledAssembly.enter_verify_slot,
  ``SP1Clean.TraceGen.routed_successor_at,
  ``SP1Clean.FormalModel.Shard.Executes.dynamicMatch,
  ``SP1Clean.Export.InstalledAssembly.executionFlag_iff_identity,
  ``SP1Clean.Export.InstalledAssembly.target_ram_changes_of_statement,
  ``SP1Clean.Semantics.ByteMemory.intervals_length_minimal,
  ``SP1Clean.Semantics.ByteMemory.intervals_congr,
  ``SP1Clean.Export.fixedProgram_occurrences,
  ``SP1Clean.Export.fixedPermission_occurrences,
  ``SP1Clean.Export.fixed_hint_occurrences,
  ``SP1Clean.FormalModel.Shard.AdmissibleExecution.fixed_hint_capacity,
  ``SP1Clean.Semantics.HintReadDemand.writeBytes,
  ``SP1Clean.TraceGen.HintReadCapacity.table_counts,
  ``SP1Clean.TraceGen.HintReadCapacity.padded_counts_le,
  ``SP1Clean.FormalModel.Shard.AdmissibleExecution.fixed_image_capacity,
  ``SP1CleanTest.FixedRamCapacity.empty_large_ram_provider_height,
  ``SP1Clean.FormalModel.Shard.AdmissibleExecution.endpoint_ram_capacity,
  ``SP1CleanTest.FixedRamCapacity.empty_release_without_raw_statement,
  ``SP1Clean.FormalModel.Shard.Executes,
  ``SP1Clean.FormalModel.Shard.nativeProfile,
  ``SP1Clean.FormalModel.Shard.AdmissibleExecution,
  ``SP1Clean.FormalModel.Shard.ReleaseAdmissibleExecution,
  ``SP1Clean.FormalModel.Shard.ReleaseStatementExecution,
  ``SP1Clean.FormalModel.Shard.sp1Machine,
  ``Air.Flat.Realizes]

/-- The owning module is used rather than the namespace, which is decoupled from paths. -/
def moduleOf (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some index => env.header.moduleNames[index.toNat]!
  | none => env.mainModule

/-- Traverse repository definitions; pinned upstream declarations remain explicit boundary nodes. -/
def localModule (name : Name) : Bool :=
  ["SP1Clean", "SP1CleanTest", "ToClean", "ToMathlib"].any
    (fun rootName => name.toString.startsWith (rootName ++ "."))

/-- Theorem bodies are kernel-checked implementation, rather than definition dependencies. -/
def body? : ConstantInfo → Option Expr
  | .thmInfo _ => none
  | info => info.value? (allowOpaque := true)

/-- Iterative traversal retains types, constructors, instances and definition bodies. -/
def manifest (env : Environment) : Except String Json := do
  let mut pending := roots.toList
  let mut seen : NameSet := {}
  let mut entries : Array (String × Json) := #[]
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | throw s!"missing declaration: {name}"
    let owner := moduleOf env name
    let repository := localModule owner
    let body := body? info
    entries := entries.push (name.toString, Json.mkObj [
      ("name", toJson name.toString), ("module", toJson owner.toString),
      ("local", toJson repository), ("typeFingerprint", toJson (toString (hash info.type))),
      ("bodyFingerprint", toJson (body.map (fun value => toString (hash value))))])
    if repository then
      pending := info.type.getUsedConstants.toList ++ pending
      if let some value := body then
        pending := value.getUsedConstants.toList ++ pending
      if let .inductInfo declaration := info then
        pending := declaration.ctors ++ pending
  let sortedEntries := entries.qsort (fun left right => left.1 < right.1)
  return Json.mkObj [
    ("version", toJson (1 : Nat)),
    ("roots", toJson (roots.map Name.toString)),
    ("declarations", Json.arr (sortedEntries.map Prod.snd))]

run_cmd do
  let env ← Lean.getEnv
  let some destination ← IO.getEnv "CAPSTONE_SURFACE_OUT"
    | throwError "CAPSTONE_SURFACE_OUT is required; use scripts/check_capstone_contract.py"
  match manifest env with
  | .error message => throwError message
  | .ok result => IO.FS.writeFile destination (result.pretty ++ "\n")

end CapstoneContractAudit
