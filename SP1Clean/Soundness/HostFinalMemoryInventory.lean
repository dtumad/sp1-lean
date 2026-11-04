import SP1Clean.Soundness.HostFinalMemoryTransport
import SP1Clean.Soundness.HostLocalCoreMemory

/-! # One final inventory for target checks and execution grounding

The boundary consumer and existing local-core grounding path read the same physical finalizer
rows, even though their selected inventories derive different data maps. Their equality is proved
through `FinalMemoryEnsemble.records`; neither path supplies a second semantic inventory or an
independently trusted decoder.
-/

namespace SP1Clean.Soundness.HostFinalMemory

open Circuit Air.Flat Channels Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance finalInventoryLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance finalInventoryClockBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot} {target : MemorySnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}
  {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
  {channels : List (RawChannel (ZMod p))}
  {names : UniqueNames image source target others resources}
  {registration : Registration image source target others resources channels}

/-- The existing grounding projection, retaining the complete source and original row arrays. -/
def coreWitness
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels names registration)) :=
  HostLocalCore.localWitness (HostHintQueueBoundary.projected (baseWitness witness))

/-- Source and finalizer arrays are shared with the established grounding projection. -/
theorem coreWitness_boundary_rows
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels names registration)) :
    ((coreWitness witness).tables.take 6).map (·.table) = (witness.tables.take 6).map (·.table) := by
  have retained : (HostHintQueueBoundary.projected (baseWitness witness)).tables.take 6 =
      (baseWitness witness).tables.take 6 :=
    List.take_set_of_le (by decide : 6 ≤ 57)
  have core := congrArg (List.map Prod.snd)
    (HostLocalCore.boundary_tables (HostHintQueueBoundary.projected (baseWitness witness)))
  simp only [List.map_map, Function.comp_def] at core
  change ((coreWitness witness).tables.take 6).map (·.table) = _ at core
  rw [core, retained, List.map_take, baseWitness_rows, ← List.map_take]

/-- The physical final inventory is identical in the installed checker and existing grounding path. -/
theorem finalRecords_eq_core
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels names registration)) :
    finalRecords witness = FinalMemoryEnsemble.records (LocalCore.finalWitness (coreWitness witness)) := by
  have finalRows : (LocalCore.finalWitness (coreWitness witness)).tables.map (·.table) =
      ((coreWitness witness).tables.drop 3).map (·.table) := by
    simp only [LocalCore.finalWitness, EnsembleWitness.ofTables_tables, withDerivedData,
      List.map_map, Function.comp_def]
    simp
  apply FinalMemoryEnsemble.records_congr_rows
  · simp only [List.map_take]
    rw [finalRows]
    simp only [← List.map_take]
    have coreRows := congrArg (fun rows => (rows.drop 3).take 2) (coreWitness_boundary_rows witness)
    simp only [← List.map_drop, ← List.map_take, List.drop_take, List.take_take] at coreRows
    change _ = ((coreWitness witness).tables.drop 3 |>.take 2).map (·.table)
    rw [List.map_take]
    have receiptRows := FinalMemoryReceipts.original_rows (FinalMemoryChecks.receiptWitness (boundaryWitness witness))
    apply (congrArg (List.take 2) receiptRows).trans
    change (List.map (fun table : Table (ZMod p) => table.table) (boundaryTables witness)).take 2 = _
    rw [← List.map_take, boundaryTables_eq,
      List.take_append_of_le_length (by
        have lower : 6 ≤ witness.tables.length := by
          rw [← witness.same_length, tables_eq]
          simp only [List.length_set, List.length_append, prefix_length]
          omega
        simp only [List.length_take, List.length_drop]; omega), List.take_take]
    exact coreRows.symm

end SP1Clean.Soundness.HostFinalMemory
