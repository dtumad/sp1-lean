import SP1Clean.Soundness.HostFinalMemoryTransport
import SP1Clean.Soundness.HostLocalCoreMemory

/-! # One final inventory for target checks and execution grounding

The boundary consumer and existing local-core grounding path read the same physical finalizer
rows and shared data. Their equality is proved through `FinalMemoryEnsemble.records`; neither
path supplies a second semantic inventory or an independently trusted decoder.
-/

namespace SP1Clean.Soundness.HostFinalMemory

open Circuit Air.Flat Channels Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot} {target : MemorySnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}
  {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
  {channels : List (RawChannel (ZMod p))}

/-- The existing grounding projection, retaining the complete source and original row arrays. -/
def coreWitness
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels)) :=
  HostLocalCore.localWitness (HostHintQueueBoundary.expanded (baseWitness witness))

private theorem base_length
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels)) :
    6 ≤ (baseWitness witness).tables.length := by
  rw [← (baseWitness witness).same_length, base_tables_length]
  omega

/-- Source and finalizer arrays are shared with the established grounding projection. -/
theorem coreWitness_boundary_rows
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels)) :
    ((coreWitness witness).tables.take 6).map (·.table) = (witness.tables.take 6).map (·.table) := by
  rw [coreWitness, HostLocalCore.boundary_tables, HostHintQueueBoundary.expanded_tables,
    List.take_append_of_le_length (by rw [List.length_set]; exact base_length witness),
    List.take_set_of_le (by decide : 6 ≤ 57), List.map_take, baseWitness_rows, ← List.map_take]

/-- Grounding and target checking use the same fixed-lookup environment. -/
theorem coreWitness_data
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels)) :
    (coreWitness witness).data = witness.data := by
  rw [coreWitness, HostLocalCore.localWitness, EnsembleWitness.project_data,
    HostHintQueueBoundary.expanded_data, baseWitness_data]

/-- The physical final inventory is identical in the installed checker and existing grounding path. -/
theorem finalRecords_eq_core
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels)) :
    finalRecords witness = FinalMemoryEnsemble.records (LocalCore.finalWitness (coreWitness witness)) := by
  apply FinalMemoryEnsemble.records_congr_rows
  · have coreRows := congrArg (fun rows => (rows.drop 3).take 2) (coreWitness_boundary_rows witness)
    simp only [← List.map_drop, ← List.map_take, List.drop_take, List.take_take] at coreRows
    change _ = ((coreWitness witness).tables.drop 3 |>.take 2).map (·.table)
    rw [List.map_take, FinalMemoryReceipts.original_rows]
    change (List.map (fun table : Table (ZMod p) => table.table) (boundaryTables witness)).take 2 = _
    rw [← List.map_take, boundaryTables_eq,
      List.take_append_of_le_length (by
        have lower : 6 ≤ witness.tables.length := by
          rw [← witness.same_length, tables_eq]
          simp only [List.length_set, List.length_append, prefix_length]
          omega
        simp only [List.length_take, List.length_drop]; omega), List.take_take]
    exact coreRows.symm
  · rw [FinalMemoryReceipts.original_data, FinalMemoryChecks.receiptWitness_data,
      boundaryWitness_data, LocalCore.finalWitness_data, coreWitness_data]

end SP1Clean.Soundness.HostFinalMemory
