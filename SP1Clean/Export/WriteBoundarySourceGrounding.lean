import SP1Clean.Export.WriteSourceGrounding

/-! # Physical register refreshes and final Memory sources for WRITE

The administrative accesses in the local Memory history read exactly the arrays in the
publisher registry. Each genuine register refresh funds its closed read-back interval and
each active register or RAM finalizer funds the suffix beginning at its record timestamp.
-/

namespace SP1Clean.Export.WriteSourceRegistry

open Circuit Air.Flat Semantics Soundness Channels WriteProbe WriteProbe.AccessInventory

private abbrev Fp := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State Fp}

private theorem refresh_rows (witness : EnsembleWitness (HostObserved.ensemble image source target final)) :
    (LocalCore.systemTable (HostFinalMemory.coreWitness (HostObserved.baseWitness witness)) 0).table = (raw witness .refresh).table := by
  let core := HostFinalMemory.coreWitness (HostObserved.baseWitness witness)
  have total := witness.same_length.symm.trans (HostObserved.tables_length (image := image)
    (source := source) (target := target) (final := final))
  have count := core.same_length.symm.trans (LocalCore.tables_length image source)
  have arrays := HostObserved.core_rows_before_halt witness ⟨55, by decide⟩
    (by change 55 < core.tables.length; omega) (by change 55 < witness.tables.length; omega)
  exact arrays

/-- The physical MemoryBump table publishes its genuine old word at its new timestamp. -/
theorem refresh_predecessor (witness : EnsembleWitness (HostObserved.ensemble image source target final))
    {prior next : MemoryMsg Fp}
    (member : (prior, next) ∈ LocalCore.memoryRefreshes (HostFinalMemory.coreWitness (HostObserved.baseWitness witness))) :
    (1, AccessSupply.atClock (next.clk_high, next.clk_low) prior) ∈ records (raw witness) := by
  let core := HostFinalMemory.coreWitness (HostObserved.baseWitness witness)
  obtain ⟨row, active, pair⟩ := List.mem_flatMap.mp member
  obtain ⟨cells, present, rfl, enabled⟩ := NativeCore.activeSystemRows_member _ _ _ active
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp pair).symm
  rw [refresh_rows witness] at present
  let table := raw witness .refresh
  have physical : cells ∈ table.table := present
  apply List.mem_flatMap.mpr
  refine ⟨.refresh, sources_complete _, List.mem_flatMap.mpr ⟨cells, physical, ?_⟩⟩
  apply List.mem_singleton.mpr
  exact Prod.ext enabled.symm rfl

private theorem final_row (ram : Bool) (cells : Array Fp) (data data' : ProverData Fp)
    (active : Environment.fromArray cells data FinalMemoryEnsemble.activity = 1) :
    (1, finalReadback (FinalMemoryEnsemble.rowRecord (Environment.fromArray cells data))) ∈
      rowRecords (.finalizer ram) (Environment.fromArray cells data') := by
  simp only [rowRecords, finalRecordAt_eq, List.mem_singleton]
  refine Prod.ext ?_ rfl
  rw [FinalMemoryEnsemble.input_activity]
  exact active.symm

private theorem final_record (witness : EnsembleWitness (HostObserved.ensemble image source target final))
    (ram : Bool) (cells : Array Fp) (data : ProverData Fp) (present : cells ∈ (raw witness (.finalizer ram)).table)
    (active : Environment.fromArray cells data FinalMemoryEnsemble.activity = 1) :
    (1, finalReadback (FinalMemoryEnsemble.rowRecord (Environment.fromArray cells data))) ∈ records (raw witness) := by
  apply List.mem_flatMap.mpr
  exact ⟨.finalizer ram, sources_complete _, List.mem_flatMap.mpr ⟨cells, present, final_row ram cells _ _ active⟩⟩

private abbrev finalWitness (witness : EnsembleWitness (HostObserved.ensemble image source target final)) :=
  LocalCore.finalWitness (HostFinalMemory.coreWitness (HostObserved.baseWitness witness))

private theorem final_arrays (witness : EnsembleWitness (HostObserved.ensemble image source target final)) (ram : Bool)
    (bound : (if ram then 1 else 0) < (finalWitness witness).tables.length) :
    ((finalWitness witness).tables[if ram then 1 else 0]'bound).table = (raw witness (.finalizer ram)).table := by
  let core := HostFinalMemory.coreWitness (HostObserved.baseWitness witness)
  let boundary := LocalCore.finalWitness core
  have rows : boundary.tables.map (·.table) = (core.tables.drop 3).map (·.table) := by
    simp only [boundary, LocalCore.finalWitness, EnsembleWitness.ofTables_tables, withDerivedData, List.map_map, Function.comp_def]
    simp
  have total := witness.same_length.symm.trans (HostObserved.tables_length (image := image)
    (source := source) (target := target) (final := final))
  have count := core.same_length.symm.trans (LocalCore.tables_length image source)
  cases ram
  · have same := List.getElem_of_eq rows (i := 0) (by rw [rows, List.length_map, List.length_drop]; omega)
    simp only [List.getElem_map, List.getElem_drop] at same
    rw [HostObserved.core_rows_before_halt witness ⟨3, by decide⟩ _ (by change 3 < witness.tables.length; omega)] at same
    exact same
  · have same := List.getElem_of_eq rows (i := 1) (by rw [rows, List.length_map, List.length_drop]; omega)
    simp only [List.getElem_map, List.getElem_drop] at same
    rw [HostObserved.core_rows_before_halt witness ⟨4, by decide⟩ _ (by change 4 < witness.tables.length; omega)] at same
    exact same

/-- A final Memory record is present precisely when the registered register or RAM row has
an active finalizer gate and decodes to that record. -/
private theorem final_member (witness : EnsembleWitness (HostObserved.ensemble image source target final)) {record : MemoryMsg Fp} :
    record ∈ FinalMemoryEnsemble.records (finalWitness witness) ↔ ∃ (ram : Bool), ∃ cells ∈ (raw witness (.finalizer ram)).table,
      let env := Environment.fromArray cells (finalWitness witness).data
      env FinalMemoryEnsemble.activity = 1 ∧ FinalMemoryEnsemble.rowRecord env = record := by
  rw [FinalMemoryEnsemble.records_eq (finalWitness witness)]
  have registers := final_arrays witness false
  have ram := final_arrays witness true
  simp only [Bool.false_eq_true, ↓reduceIte] at registers ram
  have room : 1 < (finalWitness witness).tables.length := by
    rw [← (finalWitness witness).same_length]
    change 1 < (_ ++ _ : List (Component Fp)).length
    rw [List.length_append]
    change 1 < 3 + _
    omega
  rw [registers (by omega), ram room]
  simp only [List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (⟨cells, ⟨member, gate⟩, equal⟩ | ⟨cells, ⟨member, gate⟩, equal⟩)
    · exact ⟨false, cells, member, gate, equal⟩
    · exact ⟨true, cells, member, gate, equal⟩
  · rintro ⟨(_ | _), cells, member, gate, equal⟩
    · exact Or.inl ⟨cells, ⟨member, gate⟩, equal⟩
    · exact Or.inr ⟨cells, ⟨member, gate⟩, equal⟩

/-- The complete execution core's two ordered finalizers contribute their actual consumed
records, including a location remaining at its genesis value. -/
theorem final_predecessor (witness : EnsembleWitness (HostObserved.ensemble image source target final))
    {record : MemoryMsg Fp}
    (member : record ∈ FinalMemoryEnsemble.records (LocalCore.finalWitness (HostFinalMemory.coreWitness (HostObserved.baseWitness witness)))) :
    (1, finalReadback record) ∈ records (raw witness) := by
  obtain ⟨ram, cells, present, gate, rfl⟩ := (final_member witness).mp member
  exact final_record witness ram cells _ present gate

/-- A positive refresh receipt reconstructs one genuine administrative old/new pair in the
core Memory history. Its endpoint is the physical refreshed timestamp. -/
theorem refresh_of_origin (witness : EnsembleWitness (HostObserved.ensemble image source target final)) (checked : witness.Constraints)
    {record : Readback Fp} (origin : Origin (raw witness) .refresh record) :
    ∃ prior next, (prior, next) ∈ LocalCore.memoryRefreshes (HostFinalMemory.coreWitness (HostObserved.baseWitness witness)) ∧
      record = AccessSupply.atClock (next.clk_high, next.clk_low) prior := by
  obtain ⟨cells, present, positive, rfl⟩ := origin
  let table := raw witness .refresh
  let row := valueFromOffset MemoryBumpChip.Inputs 0 (table.environment cells)
  have occurrence : (row.is_real, refreshReadback row) ∈ records (raw witness) :=
    List.mem_flatMap.mpr ⟨.refresh, sources_complete _, List.mem_flatMap.mpr ⟨cells, present, List.mem_singleton_self _⟩⟩
  have gate := positive_record_unit witness checked occurrence positive
  let core := HostFinalMemory.coreWitness (HostObserved.baseWitness witness)
  have real : memoryBumpRow core.data cells ∈ activeSystemRows (LocalCore.systemTable core 0) (memoryBumpRow core.data) (·.is_real) := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_map.mpr ⟨cells, ?_, rfl⟩, ?_⟩
    · rwa [refresh_rows witness]
    · exact decide_eq_true gate
  exact ⟨_, _, List.mem_flatMap.mpr ⟨_, real, List.mem_singleton_self _⟩, rfl⟩

/-- The suffix behind a positive finalizer receipt begins at a genuine finalized Memory
record. Both the gate and the value come from the original ordered row. -/
theorem final_of_origin (witness : EnsembleWitness (HostObserved.ensemble image source target final)) (checked : witness.Constraints)
    (ram : Bool) {record : Readback Fp} (origin : Origin (raw witness) (.finalizer ram) record) :
    ∃ prior ∈ FinalMemoryEnsemble.records (LocalCore.finalWitness (HostFinalMemory.coreWitness (HostObserved.baseWitness witness))),
      record = finalReadback prior := by
  obtain ⟨cells, present, positive, rfl⟩ := origin
  let table := raw witness (.finalizer ram)
  let gate := (valueFromOffset (OrderedMemoryProvider.RowInput MemoryMsg) 0 (table.environment cells)).2
  have occurrence : (gate, finalReadback (finalRecordAt ram (table.environment cells))) ∈ records (raw witness) :=
    List.mem_flatMap.mpr ⟨.finalizer ram, sources_complete _, List.mem_flatMap.mpr ⟨cells, present, List.mem_singleton_self _⟩⟩
  have enabled := positive_record_unit witness checked occurrence positive
  change (valueFromOffset (OrderedMemoryProvider.RowInput MemoryMsg) 0 (table.environment cells)).2 = 1 at enabled
  rw [FinalMemoryEnsemble.input_activity] at enabled
  refine ⟨_, (final_member witness).mpr ⟨ram, cells, present, enabled, rfl⟩, ?_⟩
  rw [finalRecordAt_eq]
  rfl

end SP1Clean.Export.WriteSourceRegistry
