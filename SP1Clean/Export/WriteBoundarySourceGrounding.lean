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

/-- The physical MemoryBump table publishes its genuine old word at its new timestamp. -/
theorem refresh_predecessor (witness : EnsembleWitness (HostObserved.ensemble image source target final))
    {prior next : MemoryMsg Fp}
    (member : (prior, next) ∈ LocalCore.memoryRefreshes (HostFinalMemory.coreWitness (HostObserved.baseWitness witness))) :
    (1, AccessSupply.atClock (next.clk_high, next.clk_low) prior) ∈ records (raw witness) := by
  let core := HostFinalMemory.coreWitness (HostObserved.baseWitness witness)
  obtain ⟨row, active, pair⟩ := List.mem_flatMap.mp member
  obtain ⟨cells, present, rfl, enabled⟩ := NativeCore.activeSystemRows_member _ _ _ active
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp pair).symm
  have total := witness.same_length.symm.trans (HostObserved.tables_length (image := image)
    (source := source) (target := target) (final := final))
  have count := core.same_length.symm.trans (LocalCore.tables_length image source)
  have arrays := HostObserved.core_rows_before_halt witness ⟨55, by decide⟩
    (by change 55 < core.tables.length; omega) (by change 55 < witness.tables.length; omega)
  change cells ∈ (core.tables[55]'_).table at present
  rw [arrays] at present
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

/-- The complete execution core's two ordered finalizers contribute their actual consumed
records, including a location remaining at its genesis value. -/
theorem final_predecessor (witness : EnsembleWitness (HostObserved.ensemble image source target final))
    {record : MemoryMsg Fp}
    (member : record ∈ FinalMemoryEnsemble.records (LocalCore.finalWitness (HostFinalMemory.coreWitness (HostObserved.baseWitness witness)))) :
    (1, finalReadback record) ∈ records (raw witness) := by
  let core := HostFinalMemory.coreWitness (HostObserved.baseWitness witness)
  let boundary := LocalCore.finalWitness core
  have rows : boundary.tables.map (·.table) = (core.tables.drop 3).map (·.table) := by
    simp only [boundary, LocalCore.finalWitness, EnsembleWitness.ofTables_tables, withDerivedData, List.map_map, Function.comp_def]
    simp
  have total := witness.same_length.symm.trans (HostObserved.tables_length (image := image)
    (source := source) (target := target) (final := final))
  have count := core.same_length.symm.trans (LocalCore.tables_length image source)
  change record ∈ FinalMemoryEnsemble.records boundary at member
  rw [FinalMemoryEnsemble.records_eq boundary] at member
  rcases List.mem_append.mp member with register | ram
  · obtain ⟨cells, selected, rfl⟩ := List.mem_map.mp register
    obtain ⟨present, enabled⟩ := List.mem_filter.mp selected
    have same := List.getElem_of_eq rows (i := 0) (by rw [rows, List.length_map, List.length_drop]; omega)
    simp only [List.getElem_map, List.getElem_drop] at same
    rw [same, HostObserved.core_rows_before_halt witness ⟨3, by decide⟩ _ (by change 3 < witness.tables.length; omega)] at present
    exact final_record witness false cells _ present (of_decide_eq_true enabled)
  · obtain ⟨cells, selected, rfl⟩ := List.mem_map.mp ram
    obtain ⟨present, enabled⟩ := List.mem_filter.mp selected
    have same := List.getElem_of_eq rows (i := 1) (by rw [rows, List.length_map, List.length_drop]; omega)
    simp only [List.getElem_map, List.getElem_drop] at same
    rw [same, HostObserved.core_rows_before_halt witness ⟨4, by decide⟩ _ (by change 4 < witness.tables.length; omega)] at present
    exact final_record witness true cells _ present (of_decide_eq_true enabled)

end SP1Clean.Export.WriteSourceRegistry
