import SP1Clean.Export.WriteGeneratedRamSources
import SP1Clean.Export.WriteBoundaryBuild

/-! # Physical Memory producers for a released mixed execution

The mixed compiler selects the original tables for each ordinary instruction, ECALL, HINT_READ
word transfer and register refresh. Their independent demand heights are bounded by the genuine
released run, including empty buckets and the two HINT_READ variants.
-/

namespace SP1Clean.Export.WriteMixedSourceTables

open Circuit Air.Flat Channels Soundness Machine Semantics TraceGen FormalModel.Shard
open WriteProbe WriteProbe.AccessInventory WriteSourceRegistry WitnessGeneration

private abbrev F := ZMod SP1Prime

/-- An ordinary physical bucket is the stable projection from the complete mixed tape. -/
def bucket (rows : List MixedCompiledRow) (id : InstructionChipId) : List id.Event :=
  EventBuckets.ofChronological (rows.filterMap MixedCompiledRow.ordinaryObservation?) id

/-- The legal array indices for the actual per-table rounded heights. -/
structure Heights (rows : List MixedCompiledRow) (words : List (Bool × HintReadWordChip.RowInput F)) : Prop where
  ordinary : ∀ id, demandHeight (bucket rows id).length ≤ UInt64.size
  ecall : demandHeight (rows.filterMap (MixedCompiledRow.syscallInput? (p := SP1Prime))).length ≤ UInt64.size
  hint : ∀ last, demandHeight (HintReadTransfers.selected last words).length ≤ UInt64.size
  memory : demandHeight (MixedBumpInput.memoryRows (rows.map MixedCompiledRow.bumpInput)).length ≤ UInt64.size
  state : demandHeight (MixedBumpInput.stateRows (rows.map MixedCompiledRow.bumpInput)).length ≤ UInt64.size

/-- Every release-admissible execution supplies all required physical heights, including the
two independently rounded HINT_READ histories, without a height supplied by the caller. -/
theorem heights {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : ReleaseAdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows) :
    Heights rows (HintReadTransfers.history image source events) := by
  obtain ⟨ordinary, emitted, _, ready⟩ := releaseAdmissibleExecution_instructionBuckets run
  rw [routeObservations?, routed, Option.map_some] at emitted
  obtain rfl := Option.some.inj emitted
  obtain ⟨inputs, bumped, _, mem, cpu, _, _⟩ := admissibleExecution_mixedBumpInventory run.1
  rw [routeBumpInputs?, routed, Option.map_some] at bumped
  obtain rfl := Option.some.inj bumped
  obtain ⟨same, built, fit, _⟩ := MixedSyscallTable.of_execution run.1 (.empty _) (.empty _)
  obtain rfl := Option.some.inj (routed.symm.trans built)
  have count := event_count_le_ticks events
  have ticks := run.1.1.clock
  have last : target.clock < 2 ^ 48 := run.1.2.2.2.2.2.1
  have bounded (n : ℕ) (small : n ≤ 3 * events.length) : demandHeight n ≤ UInt64.size := by
    have bound := (demandHeight_bounds n).2
    change _ ≤ 2 ^ 64
    omega
  refine ⟨fun id => (ready id).1, fit, ?_, bounded _ mem, bounded _ (by omega)⟩
  intro last
  exact (HintReadTransfers.tables_of_admissibleExecution run.1 last (.empty _)).choose

/-- Construct an original Memory source whose physical index lies after the six boundary
components. The two finalizers belong to the generated boundary prefix. -/
noncomputable def table (rows : List MixedCompiledRow) (words : List (Bool × HintReadWordChip.RowInput F))
    (fit : Heights rows words) (data : ProverData F) (hint : ProverHint F) :
    (id : Source) → 6 ≤ position id → Table F
  | .ordinary id, _ => InstalledInstructionTables.table id (bucket rows id) data hint (fit.ordinary id)
  | .host .ecall, _ => MixedSyscallTable.table rows data hint fit.ecall
  | .host (.word last), _ => HintReadTransfers.wordTable last words data (fit.hint last)
  | .refresh, _ => (InstalledAssembly.bumpTables (MixedBumpInput.memoryRows (rows.map MixedCompiledRow.bumpInput))
      (MixedBumpInput.stateRows (rows.map MixedCompiledRow.bumpInput)) data fit.memory fit.state).1
  | .finalizer false, outside => False.elim (by contradiction)
  | .finalizer true, outside => False.elim (by contradiction)

/-- The generated row arrays retain the literal component registered by the complete supervisor. -/
theorem registered (rows : List MixedCompiledRow) (words : List (Bool × HintReadWordChip.RowInput F)) (fit : Heights rows words)
    (data : ProverData F) (hint : ProverHint F) (id : Source) (outside : 6 ≤ position id) :
    (table rows words fit data hint id outside).component = original id := by
  cases id with
  | ordinary i => rfl
  | host family => cases family <;> rfl
  | refresh => rfl
  | finalizer ram => cases ram <;> contradiction

/-- All original generated source rows satisfy their own circuit assertions at their
native, locally constructed data. -/
theorem valid {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : ReleaseAdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow} (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (data : ProverData F) (hint : ProverHint F) (id : Source) (outside : 6 ≤ position id) :
    let t := table rows (HintReadTransfers.history image source events) (heights run routed) data hint id outside
    t.Constraints ∧ t.Guarantees := by
  cases id with
  | ordinary id =>
    obtain ⟨ordinary, emitted, _, ready⟩ := releaseAdmissibleExecution_instructionBuckets run
    rw [routeObservations?, routed, Option.map_some] at emitted
    obtain rfl := Option.some.inj emitted
    exact InstalledInstructionTables.table_valid id _ _ _ ((heights run routed).ordinary id) (ready id).2
  | host family => cases family with
    | ecall => exact MixedSyscallTable.checked run.1 routed data hint (heights run routed).ecall
    | word last => exact (HintReadTransfers.tables_of_admissibleExecution run.1 last data).choose_spec
  | refresh =>
    obtain ⟨inputs, bumped, _, _, _, mv, _⟩ := admissibleExecution_mixedBumpInventory run.1
    rw [routeBumpInputs?, routed, Option.map_some] at bumped
    obtain rfl := Option.some.inj bumped
    exact InstalledAssembly.bumpTables_registerValid _ _ data (heights run routed).memory (heights run routed).state mv
  | finalizer ram => cases ram <;> contradiction

end SP1Clean.Export.WriteMixedSourceTables
