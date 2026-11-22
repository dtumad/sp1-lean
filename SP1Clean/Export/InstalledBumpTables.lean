import SP1Clean.Export.InstalledBumpPreset
import SP1Clean.Proofs.Completeness.Providers

/-! # The two demand-padded refresh tables of a mixed shard

Both registered components use their canonical builder with the same prover data. Active rows
use the register window refreshes and CPU-state normalizations at their actual tape positions.
-/

namespace SP1Clean.Export.InstalledAssembly
open Circuit Air.Flat Semantics Machine TraceGen FormalModel.Shard

private abbrev memory := Soundness.providerTableFor (p := SP1Prime) .memoryBump
private abbrev state := Soundness.providerTableFor (p := SP1Prime) .stateBump

/-- Both row builders use the disabled input prescribed by their installed demand modes. -/
theorem bump_generation_padding :
    (∃ mode, memory.generation = .demand mode ∧ mode.padding = MemoryBumpChip.paddingInputs) ∧
    (∃ mode, state.generation = .demand mode ∧ mode.padding = StateBumpChip.paddingInputs) := by
  constructor <;> refine ⟨_, rfl, ?_⟩ <;> apply ProvableType.toElements_inj_iff.mp <;> decide +kernel

private def padded {α : Type} (rows : List α) (padding : α) : List α :=
  rows ++ List.replicate (WitnessGeneration.demandPadding rows.length) padding

private theorem padded_length {α : Type} (rows : List α) (padding : α) :
    (padded rows padding).length = WitnessGeneration.demandHeight rows.length := by
  simp only [padded, List.length_append, List.length_replicate, WitnessGeneration.add_demandPadding]

private theorem memory_height (events : List MemoryBumpEvent) :
    (padded (memoryBumpTraceInputs (p := SP1Prime) events) MemoryBumpChip.paddingInputs).length =
      WitnessGeneration.demandHeight events.length :=
  (padded_length _ _).trans (congrArg WitnessGeneration.demandHeight (List.length_map ..))

private theorem state_height (events : List StateBumpEvent) :
    (padded (stateBumpTraceInputs (p := SP1Prime) events) StateBumpChip.paddingInputs).length =
      WitnessGeneration.demandHeight events.length :=
  (padded_length _ _).trans (congrArg WitnessGeneration.demandHeight (List.length_map ..))

/-- Construct the two installed bump tables on a shared named input map. The first table is
MemoryBump and the second is StateBump, matching the physical registry. -/
def bumpTables (registers : List MemoryBumpEvent) (pushes : List StateBumpEvent) (data : ProverData Fp)
    (mh : WitnessGeneration.demandHeight registers.length ≤ UInt64.size)
    (sh : WitnessGeneration.demandHeight pushes.length ≤ UInt64.size) : Table Fp × Table Fp :=
  let m := padded (memoryBumpTraceInputs (p := SP1Prime) registers) MemoryBumpChip.paddingInputs
  let s := padded (stateBumpTraceInputs (p := SP1Prime) pushes) StateBumpChip.paddingInputs
  let shared := memory.inputData m (state.inputData s data)
  (Table.build memory m shared (ProverHint.empty _)
    ((memory_height registers).trans_le mh) (by trivial)
    (memory.inputData_consistent _ _),
   Table.build state s shared (ProverHint.empty _)
    ((state_height pushes).trans_le sh) (by trivial)
    (state.inputData_consistent _ data))

private theorem padded_valid {α : Type} (rows : List α) (padding : α) (P : α → Prop)
    (live : ∀ r ∈ rows, P r) (disabled : P padding) : ∀ r ∈ padded rows padding, P r := by
  intro r member
  rcases List.mem_append.mp member with active | tail
  · exact live r active
  · exact (List.eq_of_mem_replicate tail) ▸ disabled

/-- The construction simultaneously satisfies both circuits on one
shared prover input. Their heights are the ones charged by the 44-component preset. -/
theorem bump_constructed_tables (ctx : Context) {events : List ExecutionEvent}
    (execution : AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (data : ProverData Fp) :
    ∃ inputs, routeBumpInputs? (policy SP1Prime ctx.image) ctx.image.program AccessFrontier.initial ctx.source.realize events = some inputs ∧
      ∃ mh sh, let registers := MixedBumpInput.memoryRows inputs
               let pushes := MixedBumpInput.stateRows inputs
               let pair := bumpTables registers pushes data mh sh
               pair.1.component = memory ∧ pair.2.component = state ∧ pair.1.data = pair.2.data ∧
               pair.1.data.publicInput = data.publicInput ∧
               pair.1.length = WitnessGeneration.demandHeight registers.length ∧
               pair.2.length = WitnessGeneration.demandHeight pushes.length ∧
               pair.1.Constraints ∧ pair.1.Guarantees ∧ pair.2.Constraints ∧ pair.2.Guarantees := by
  obtain ⟨inputs, routed, _, mem, cpu, mv, sv⟩ := admissibleExecution_mixedBumpInventory execution
  have count := event_count_le_ticks events
  have ticks := execution.1.clock
  have last : ctx.target.clock < 2 ^ 48 := execution.2.2.2.2.2.1
  have height (n : ℕ) (bounded : n ≤ 3 * events.length) : WitnessGeneration.demandHeight n ≤ UInt64.size := by
    have upper := (WitnessGeneration.demandHeight_bounds n).2
    change _ ≤ 2 ^ 64
    omega
  refine ⟨inputs, routed, height _ mem, height _ (by omega), rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (List.length_map ..).trans (memory_height (MixedBumpInput.memoryRows inputs))
  · exact (List.length_map ..).trans (state_height (MixedBumpInput.stateRows inputs))
  all_goals dsimp only [bumpTables]
  · apply Table.build_constraints
    exact padded_valid _ _ MemoryBumpChip.Spec (memoryBumpTraceInputs_spec mv) MemoryBumpChip.spec_paddingInputs
  · apply Table.build_guarantees
    exact padded_valid _ _ MemoryBumpChip.Spec (memoryBumpTraceInputs_spec mv) MemoryBumpChip.spec_paddingInputs
  · apply Table.build_constraints
    exact padded_valid _ _ StateBumpChip.Spec (stateBumpTraceInputs_spec sv) StateBumpChip.spec_paddingInputs
  · apply Table.build_guarantees
    exact padded_valid _ _ StateBumpChip.Spec (stateBumpTraceInputs_spec sv) StateBumpChip.spec_paddingInputs

end SP1Clean.Export.InstalledAssembly
