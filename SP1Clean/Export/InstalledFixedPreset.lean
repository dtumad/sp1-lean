import SP1Clean.Export.InstalledFixedInventory
import SP1Clean.Proofs.Completeness.HintReadCapacity

/-! # A shard preset for the installed fixed providers

Every preallocated table receives its actual height. Its channel occurrences, including
repeated emissions, share capacity with the verifier and the demand-generated tables.
-/

namespace SP1Clean.Export.InstalledAssembly
open Circuit Air.Flat Machine Semantics Soundness Semantics.HintQueue

/-- A release preset for fixed providers and the separately padded HINT_READ transfer block.
The native event and clock ceilings are preserved. -/
def fixedProviderPreset : ResourceLimits :=
  { ResourceLimits.native SP1Prime with boundaryBytes := 2 ^ 29 + 124, writeBytes := 2 ^ 24 }

/-- This release choice tightens the existing native resource domain. -/
theorem fixedProviderPreset_le_native : fixedProviderPreset.LE (.native SP1Prime) := by
  unfold ResourceLimits.LE fixedProviderPreset ResourceLimits.native
  decide

/-- The simultaneous channel reservations for the ten fixed providers in physical order.
The hint clock terminal has one row and emits twice. -/
def fixedReservations (ctx : Context) : List (String × ℕ) :=
  [((Channels.programChannel (p := SP1Prime)).name, FixedProgramProvider.Preprocessed.height (p := SP1Prime) ctx.image),
   ((ctx.source.sail.memorySnapshot.registerTable (p := SP1Prime)).channel.name, 32),
   ((InitialMemoryLookup.membership (p := SP1Prime) ctx.source.sail.memory (2 ^ 48) "sp1.native.initial_memory").channel.name,
     (InitialMemoryLookup.membership (p := SP1Prime) ctx.source.sail.memory (2 ^ 48) "sp1.native.initial_memory").height),
   ((ctx.image.writePermissionTable (p := SP1Prime)).channel.name, (ctx.image.writePermissionTable (p := SP1Prime)).height),
   ((HostHintQueue.nodeChannel (p := SP1Prime)).name, (sourceTable (p := SP1Prime) ctx.source.host.io.hints).height),
   ((HostHintQueue.wordChannel (p := SP1Prime)).name, (HostHintQueue.sourceWordInventory (p := SP1Prime) ctx.source.host.io.hints).height),
   ((FinalRegisterValue.membership (p := SP1Prime) ctx.target.sail.memorySnapshot).channel.name, 32),
   ((InitialMemoryLookup.membership (p := SP1Prime) ctx.target.sail.memory (2 ^ 48) "sp1.native.target_memory").channel.name,
     (InitialMemoryLookup.membership (p := SP1Prime) ctx.target.sail.memory (2 ^ 48) "sp1.native.target_memory").height),
   ((CommitmentDeclaration.channel (p := SP1Prime)).name, 16), ((HostHintQueue.stateChannel (p := SP1Prime)).name, 2)]

private theorem restrict_fixed (tables : List (Component Fp)) (name : String) :
    (tables.map fun t => fixedHeight t * rowOccurrences t name).sum =
    ((tables.filterMap asFixed).map fun t => fixedHeight t * rowOccurrences t name).sum := by
  induction tables with
  | nil => rfl
  | cons t ts ih =>
    cases gen : t.generation <;>
      simp only [List.map_cons, List.sum_cons, List.filterMap_cons, asFixed, gen, fixedHeight] at ih ⊢ <;>
      simp [ih]

private theorem weighted (tables : List (Component Fp)) (name : String) :
    (tables.map fun t => fixedHeight t * rowOccurrences t name).sum =
    (List.zipWith (fun h (ks : List String) => h * ks.countP (· == name))
      (tables.map fixedHeight) (tables.map rowChannelNames)).sum := by
  induction tables with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons, ← ih]
    simp [rowChannelNames, rowOccurrences, List.countP_map, Function.comp_def]

/-- The total count from all preallocated slots of the installed verifier, simultaneously. -/
theorem fixed_occurrences (ctx : Context) (name : String) :
    additionalOccurrences ctx fixedHeight name =
      ((fixedReservations ctx).map fun item => if item.1 = name then item.2 else 0).sum := by
  have single (h : ℕ) (k : String) : h * [k].countP (· == name) = (if k = name then h else 0) := by
    by_cases eq : k = name <;> simp [eq]
  have double (k : String) : 1 * [k,k].countP (· == name) = (if k = name then 2 else 0) := by
    by_cases eq : k = name <;> simp [eq]
  rw [additionalOccurrences, restrict_fixed, preallocated_tables, weighted, fixed_heights, fixed_rowChannels]
  simp only [fixedReservations, List.zipWith_cons_cons, List.zipWith_nil_left, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, single, double]

private theorem reserved_le (entries : List (String × ℕ)) (name : String) (budget : ℕ)
    (unique : (entries.map Prod.fst).Nodup) (bounded : ∀ item ∈ entries, item.2 ≤ budget) :
    (entries.map fun item => if item.1 = name then item.2 else 0).sum ≤ budget := by
  induction entries with
  | nil => simp
  | cons item rest ih =>
    obtain ⟨head, tail⟩ := List.nodup_cons.mp unique
    by_cases same : item.1 = name
    · have zero := List.map_congr_left (l := rest) (fun e member =>
        show (if e.1 = name then e.2 else 0) = 0 by
          have neq : e.1 ≠ name := fun eq => head (same ▸ eq ▸ List.mem_map_of_mem (f := Prod.fst) member)
          simp [neq])
      have bound := bounded item (.head _)
      simpa [same, zero] using bound
    · simpa [same] using ih tail (fun e m => bounded e (.tail _ m))

/-- Under the boundary ceiling, all fixed rows together reserve at most 2^30
occurrences per channel, with repeated clock-terminal emissions counted. -/
theorem fixed_occurrences_le (ctx : Context) {events : List ExecutionEvent}
    (execution : FormalModel.Shard.AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (ceiling : ctx.limits.boundaryBytes ≤ 2 ^ 29 + 124) (name : String) :
    additionalOccurrences ctx fixedHeight name ≤ 2 ^ 30 := by
  rw [fixed_occurrences]
  apply reserved_le
  · simp only [fixedReservations, List.map_cons, List.map_nil, StaticTable.channel,
      MemorySnapshot.registerTable, StaticTable.ofRows, ProgramImage.writePermissionTable,
      FinalRegisterValue.membership, InitialMemoryLookup.membership]
    decide
  · obtain ⟨program, permissions, _⟩ := execution.fixed_image_headroom ceiling
    obtain ⟨_, _, _, nodes, words, hints, _⟩ := execution.fixed_hint_capacity (ceiling.trans (by decide))
    have src := (execution.endpoint_ram_capacity ceiling ctx.source (by simp) "sp1.native.initial_memory").1
    have dst := (execution.endpoint_ram_capacity ceiling ctx.target (by simp) "sp1.native.target_memory").1
    intro item member
    simp only [fixedReservations, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h|h|h|h|h|h|h|h|h|h <;> subst item <;> dsimp only
    all_goals first | exact src | exact dst | exact program.trans (by decide) | exact permissions.trans (by decide) |
      exact nodes.trans (hints.trans (by decide)) | exact words.trans (hints.trans (by decide)) | decide

/-- The three physical HINT_READ heights obtained by independently padding the handler, the
continuing word transfers and the final word of each call. Other events remain in the path. -/
def hintReadHeights (events : List ExecutionEvent) (table : Component Fp) : ℕ :=
  let lengths := events.filterMap HintReadDemand.length?
  let calls := WitnessGeneration.demandHeight lengths.length
  slotRows HostHintReadCoverage.handler calls table +
    slotRows (HintReadCoverage.component false) (WitnessGeneration.demandHeight (HintReadDemand.continuing lengths)) table +
    slotRows (HintReadCoverage.component true) calls table

private theorem width_le (table : Component Fp) (name : String) (bound : ℕ)
    (length : (table.operations.interactions.map (·.channel)).length ≤ bound) :
    rowOccurrences table name ≤ bound :=
  List.countP_le_length.trans (by simpa only [List.length_map] using length)

private theorem read_widths (name : String) :
    rowOccurrences HostHintReadCoverage.handler name ≤ 27 ∧
    ∀ last, rowOccurrences (HintReadCoverage.component last) name ≤ 27 := by
  constructor
  · apply width_le
    rw [TraceGen.HintReadCapacity.handler_channels]
    decide
  · intro last
    apply width_le
    rw [TraceGen.HintReadCapacity.word_channels]
    decide

/-- Every channel of the actual registered three-table transfer block fits a common budget
from the charged write bytes, including the mandatory last word of each aligned transfer. -/
theorem hintRead_occurrences_le (ctx : Context) {events : List ExecutionEvent}
    (execution : FormalModel.Shard.AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (name : String) : additionalOccurrences ctx (hintReadHeights events) name ≤ 14 * ctx.limits.writeBytes := by
  obtain ⟨handler, next, last⟩ := hint_read_slots ctx
  let callsHeight := WitnessGeneration.demandHeight (events.filterMap HintReadDemand.length?).length
  let contHeight := WitnessGeneration.demandHeight (HintReadDemand.continuing (events.filterMap HintReadDemand.length?))
  change additionalOccurrences ctx (fun t => slotRows HostHintReadCoverage.handler callsHeight t +
    slotRows (HintReadCoverage.component false) contHeight t + slotRows (HintReadCoverage.component true) callsHeight t) name ≤ _
  simp only [additionalOccurrences_add,
    additionalOccurrences_slot _ _ (List.mem_of_getElem? handler),
    additionalOccurrences_slot _ _ (List.mem_of_getElem? next),
    additionalOccurrences_slot _ _ (List.mem_of_getElem? last)]
  obtain ⟨handlerWidth, wordWidth⟩ := read_widths name
  have calls := Nat.mul_le_mul_left (WitnessGeneration.demandHeight (events.filterMap HintReadDemand.length?).length) handlerWidth
  have continuing := Nat.mul_le_mul_left (WitnessGeneration.demandHeight (HintReadDemand.continuing
    (events.filterMap HintReadDemand.length?))) (wordWidth false)
  have final := Nat.mul_le_mul_left (WitnessGeneration.demandHeight (events.filterMap HintReadDemand.length?).length) (wordWidth true)
  obtain ⟨_, _, transfer⟩ := TraceGen.HintReadCapacity.demand_bounds execution.1.2
  have paid := execution.2.2.1 .writeBytes
  change executionResources _ _ _ _ .writeBytes ≤ ctx.limits.writeBytes at paid
  dsimp only [callsHeight, contHeight]
  omega

/-- Literal verifier-only occurrences before any table contributes to the per-channel count. -/
def verifierOccurrences (ctx : Context) (name : String) : ℕ :=
  (assembly ctx).verifierOperations.interactions.countP (·.channel.name == name)

private theorem total_count (ctx : Context) (rows : Component Fp → ℕ) (name : String) :
    (assembly ctx).interactionCount name (physicalHeights ctx rows) =
      verifierOccurrences ctx name + additionalOccurrences ctx rows name := by
  simp only [Ensemble.interactionCount, physicalHeights, verifierOccurrences, additionalOccurrences, rowOccurrences]
  apply congrArg (Nat.add _)
  generalize (assembly ctx).tables = tables
  induction tables with
  | nil => rfl
  | cons t ts ih => simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons, ih]

/-- At the release preset, all ten fixed tables and the three HINT_READ components fit
simultaneously whenever the verifier and the other physical rows spend the indicated
remaining budget. Their costs are read from the actual complete 100-slot verifier map. -/
theorem fixedProviderPreset_mixed_fit (ctx : Context) {events : List ExecutionEvent}
    (execution : FormalModel.Shard.AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE fixedProviderPreset) (other : Component Fp → ℕ)
    (remaining : ∀ ch ∈ (assembly ctx).channels, verifierOccurrences ctx ch.name + additionalOccurrences ctx other ch.name
        ≤ SP1Prime - 1 - 2 ^ 30 - 14 * 2 ^ 24) :
    (assembly ctx).interactionsFit .logUp (physicalHeights ctx
      fun t => fixedHeight t + hintReadHeights events t + other t) := by
  unfold ResourceLimits.LE at preset
  have boundary : ctx.limits.boundaryBytes ≤ 2 ^ 29 + 124 := preset.2.2.2.2.2.2.2.2.2.1
  have writes : ctx.limits.writeBytes ≤ 2 ^ 24 := preset.2.2.2.1
  rw [Ensemble.interactionsFit, List.all_eq_true]
  intro ch registered
  simp only [Balance.logUp, decide_eq_true_eq, ComputableRingChar.char_eq, ZMod.ringChar_zmod_n, total_count, additionalOccurrences_add]
  have fixed := fixed_occurrences_le ctx execution boundary ch.name
  have hint := (hintRead_occurrences_le ctx execution ch.name).trans (Nat.mul_le_mul_left 14 writes)
  have rest := remaining ch registered
  have enough : 2 ^ 30 + 14 * 2 ^ 24 ≤ SP1Prime - 1 := by decide
  omega

end SP1Clean.Export.InstalledAssembly
