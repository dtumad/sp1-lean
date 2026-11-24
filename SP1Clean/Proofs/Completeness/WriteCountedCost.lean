import SP1Clean.Proofs.Completeness.WriteCountedTables
import SP1Clean.Soundness.WriteSourcePulls
import ToClean.Air.Footprint

/-! # Exact demand height of the counted WRITE supplier

There is one allocated row per live original predecessor, even when several predecessor
records encode the same payload. Every physical predecessor site is paid for by its own
original Memory ledger, before decoration.
-/

namespace SP1Clean.WriteProbe

open Circuit Air.Flat Soundness Channels AccessInventory

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- Use the original instruction registry’s physical input columns. -/
local instance (id : InstructionChipId) : ProvableType (supportedChipFor (p := p) id).kind.Inputs :=
  (supportedChipFor (p := p) id).kind.provableInputs

/-- Use the matching original instruction output columns when projecting Memory operations. -/
local instance (id : InstructionChipId) : ProvableType (supportedChipFor (p := p) id).kind.Cols :=
  (supportedChipFor (p := p) id).kind.provableCols

private theorem ordinary_width (id : InstructionChipId) :
    OrdinarySources.accessCount (p := p) id ≤ (ProtectedOrdinaryReceipt.component (p := p) id).channelWidth memoryChannel.toRaw := by
  simp only [Component.channelWidth, ProtectedOrdinaryReceipt.interactions id (memoryChannel (p := p)).toRaw (by
    intro same; exact Bool.noConfusion (congrArg (fun c => c.name == "SP1Memory") same)),
    ProtectedOrdinaryReceipt.provider_interactions id (memoryChannel (p := p)).toRaw (by
    intro same; exact Bool.noConfusion (congrArg (fun c => c.name == "SP1Memory") same)),
    Component.interactionsWith_eq, Component.rowOperations]
  change _ ≤ ((((supportedChipFor (p := p) id).circuit.main (varFromOffset _ 0)).operations
    (size (supportedChipFor (p := p) id).kind.Inputs)).interactionsWith memoryChannel.toRaw).length
  rw [OrdinarySources.original_memory, List.length_map]
  exact List.length_filter_le ..

/-- On every source table all physical predecessor sites are funded by the original Memory
width, including sites at activity zero. -/
theorem AccessInventory.perRow_le_memory (id : Source) :
    perRow (p := p) id ≤ (original (p := p) id).channelWidth memoryChannel.toRaw := by
  let env : Environment (ZMod p) := Environment.fromArray #[] (.empty _)
  have width (c : Component (ZMod p)) : c.channelWidth memoryChannel.toRaw =
      (c.operations.interactionValuesWith memoryChannel.toRaw env).length := (List.length_map ..).symm
  cases id with
  | ordinary id => exact ordinary_width id
  | host family =>
    rw [width]
    have bounded := List.length_filter_le (fun i : Interaction (ZMod p) => i.direction == .pull)
      ((HostSources.original family).operations.interactionValuesWith memoryChannel.toRaw env)
    rw [host_pulls, List.length_map] at bounded
    cases family <;> exact bounded
  | refresh =>
    rw [width]
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations]
    change 1 ≤ ((((MemoryBumpChip.main (varFromOffset MemoryBumpChip.Inputs 0)).operations (size MemoryBumpChip.Inputs)).interactionsWith
      memoryChannel.toRaw).map (AbstractInteraction.eval env)).length
    rw [List.length_map, memoryBumpMain_memoryInteractions]
    exact Nat.le_succ 1
  | finalizer ram =>
    rw [width, show (original (.finalizer ram)).operations.interactionValuesWith memoryChannel.toRaw env = _ from original_final_memory_values ram env]
    exact le_rfl

/-- Total original occurrence count computed from the actual allocated table heights. -/
theorem AccessInventory.records_length (raw : Source → Table (ZMod p)) (registered : ∀ id, (raw id).component = original id) :
    (records raw).length = (sources.map (fun id => (raw id).length * perRow (p := p) id)).sum := by
  have one id : ((raw id).table.flatMap (fun row => rowRecords id ((raw id).environment row))).length =
      (raw id).length * perRow (p := p) id := by
    have same := congrArg List.length (table_records id (raw id) (registered id))
    rw [List.length_map, source_count] at same
    exact same.symm
  simp only [records, List.length_flatMap, one]

/-- The complete raw predecessor inventory costs at most the original Memory interactions
of its registered tables. -/
theorem AccessInventory.records_le_source_memory (raw : Source → Table (ZMod p)) (registered : ∀ id, (raw id).component = original id) :
    (records raw).length ≤ (sources.map (fun id => (raw id).length * (raw id).component.channelWidth memoryChannel.toRaw)).sum := by
  rw [records_length raw registered]
  apply List.sum_le_sum
  intro id _
  rw [registered]
  exact Nat.mul_le_mul_left _ (perRow_le_memory id)

namespace Counted

theorem supply_height (records : List (Readback (ZMod p))) (requests : List (Request records.length (ZMod p)))
    (data : ProverData (ZMod p)) (bound) :
    (table (allocated records requests) data bound).length = WitnessGeneration.demandHeight records.length := by
  calc
    _ = (physical (allocated records requests)).length := List.length_map ..
    _ = _ := by simp only [physical, List.length_append, List.length_replicate, WitnessGeneration.add_demandPadding, allocated, List.length_ofFn]

end Counted
end SP1Clean.WriteProbe
