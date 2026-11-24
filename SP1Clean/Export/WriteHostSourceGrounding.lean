import SP1Clean.Export.WriteSourceGrounding
import SP1Clean.Soundness.HostHintReadExecutionRows

/-! # Host predecessor records at their actual incoming State cuts

The ECALL instruction and the HINT_READ word tables publish at the same incoming clock as
the corresponding decoded CPU event. Physical row identity and activity determine every
record, independently of the host dispatch profile.
-/

namespace SP1Clean.Export.WriteSourceRegistry

open Circuit Air.Flat Semantics Soundness Channels WriteProbe WriteProbe.AccessInventory
open HostHintReadCPU NativeCore

private abbrev Fp := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State Fp}

/-- The host execution decoder underneath final Memory and ordinary receipts. -/
abbrev hostWitness (witness : EnsembleWitness (HostObserved.ensemble image source target final)) :=
  HostHintQueueBoundary.projected (HostFinalMemory.baseWitness (HostObserved.baseWitness witness))

/-- The ECALL instruction and every word row survive all three witness projections. -/
private theorem host_arrays (witness : EnsembleWitness (HostObserved.ensemble image source target final)) :
    ((hostWitness witness).tables.drop 58).map (·.table) = (witness.tables.drop 58).map (·.table) := by
  rw [hostWitness, HostHintQueueBoundary.projected_drop _ _ (by decide), List.map_drop,
    HostFinalMemory.baseWitness_rows, HostObserved.baseWitness_rows witness, List.map_drop]

private theorem ecall_records (env : Environment Fp) :
    let r := HostCallLedger.input env
    let state := SyscallInstrsChip.statePulledMessage r
    rowRecords (.host .ecall) env = (syscallRowFacts r).memPulls.map (fun x =>
      (r.is_real, AccessSupply.atClock (state.clk_high, state.clk_low) x.1)) := by
  let input := varFromOffset (F := Fp) SyscallInstrsChip.Inputs 0
  let receipt := fun block register => (env input.is_real,
    eval env (AccessSupply.atClock ((HostCallChip.message input).clk_high, (HostCallChip.message input).clk_low)
      (SyscallInstrsChip.memPullMsg input block register)))
  change [receipt input.op_a_memory input.op_a, receipt input.op_b_memory input.op_b,
    receipt input.op_c_memory input.op_c] = _
  rw [show HostCallLedger.input env = eval env input from (eval_varFromOffset_valueFromOffset _ _ env).symm]
  simp only [receipt, AccessSupply.eval_atClock]
  simp only [HostCallChip.message, syscallRowFacts, List.map_cons,
    List.map_nil, SyscallInstrsChip.memPulledMessage, SyscallInstrsChip.statePulledMessage, circuit_norm]

private theorem ecall_record_of_pull (cells : Array Fp) (data data' : ProverData Fp)
    {prior : MemoryMsg Fp} {time : ℕ} (enabled : (HostCallLedger.input (Environment.fromArray cells data)).is_real = 1)
    (pulled : (prior, time) ∈ (syscallRowFacts (HostCallLedger.input (Environment.fromArray cells data))).memPulls) :
    let state := SyscallInstrsChip.statePulledMessage (HostCallLedger.input (Environment.fromArray cells data))
    (1, AccessSupply.atClock (state.clk_high, state.clk_low) prior) ∈ rowRecords (.host .ecall) (Environment.fromArray cells data') := by
  rw [ecall_records]
  have same : HostCallLedger.input (Environment.fromArray cells data') = HostCallLedger.input (Environment.fromArray cells data) := rfl
  rw [same, enabled]
  exact List.mem_map.mpr ⟨_, pulled, rfl⟩

/-- The released ECALL contributes its three actual predecessor records at the incoming
clock, including the x10/x11 reads whose individual access slots are later in the step. -/
theorem syscall_predecessor (witness : EnsembleWitness (HostObserved.ensemble image source target final))
    {row : SyscallInstrsChip.Inputs Fp}
    (member : ExecutionRow.syscall row ∈ LocalCore.executionRows (HostFinalMemory.coreWitness (HostObserved.baseWitness witness)))
    {prior : MemoryMsg Fp} {time : ℕ} (pulled : (prior, time) ∈ (syscallRowFacts row).memPulls) :
    let state := SyscallInstrsChip.statePulledMessage row
    (1, AccessSupply.atClock (state.clk_high, state.clk_low) prior) ∈ records (raw witness) := by
  let host := hostWitness witness
  change ExecutionRow.syscall row ∈ LocalCore.executionRows (HostLocalCore.localWitness host) at member
  have active : row ∈ activeSystemRows (LocalCore.systemTable (HostLocalCore.localWitness host) 3)
      (syscallInstrsRow (HostLocalCore.localWitness host).data) (·.is_real) := by
    simpa [LocalCore.executionRows] using member
  rw [← HostLocalCore.hostCallTable_projection host] at active
  obtain ⟨env, inRows, rfl⟩ := List.mem_map.mp active
  have enabled := HostCallLedger.activeRows_is_real _ _ _ inRows
  obtain ⟨cells, present, rfl⟩ := List.mem_map.mp (List.mem_filter.mp inRows).1
  have h := host_arrays witness
  have position := List.getElem_of_eq h (i := 0) (by
    rw [h, List.length_map, List.length_drop, ← witness.same_length, HostObserved.tables_length]
    decide)
  simp only [List.getElem_map, List.getElem_drop, Nat.add_zero] at position
  change cells ∈ (host.tables[58]'_).table at present
  rw [position] at present
  let table := raw witness (.host .ecall)
  have physical : cells ∈ table.table := present
  apply List.mem_flatMap.mpr
  refine ⟨.host .ecall, sources_complete _, List.mem_flatMap.mpr ⟨cells, physical, ?_⟩⟩
  exact ecall_record_of_pull cells host.data table.data enabled pulled

private theorem suffix_array_at {left right : List (Table Fp)} (i : ℕ) (after : 58 ≤ i)
    (inside : i < left.length) (outside : i < right.length)
    (rows : (left.drop 58).map (·.table) = (right.drop 58).map (·.table)) :
    (left[i]'inside).table = (right[i]'outside).table := by
  have same := List.getElem_of_eq rows (i := i - 58) (by simp only [List.length_map, List.length_drop]; omega)
  simpa only [List.getElem_map, List.getElem_drop, Nat.add_sub_of_le after] using same

private theorem word_origin (witness : EnsembleWitness (HostObserved.ensemble image source target final))
    {last : Bool} {table : Table Fp}
    (paired : (last, table) ∈ HintReadCoverage.variants.zip (HostHintReadLocal.wordTables (hostWitness witness))) :
    table.table = (raw witness (.host (.word last))).table := by
  obtain ⟨i, hi, same⟩ := List.mem_iff_getElem.mp paired
  rw [List.length_zip] at hi
  have small : i < 2 := (lt_min_iff.mp hi).1
  have total := witness.same_length.symm.trans (HostObserved.tables_length (image := image)
    (source := source) (target := target) (final := final))
  have bounds : i + 84 < (hostWitness witness).tables.length := by
    have len := congrArg List.length (host_arrays witness)
    simp only [List.length_map, List.length_drop, total] at len
    omega
  simp only [List.getElem_zip, HostHintReadLocal.wordTables, List.getElem_take, HostLocalHandoff.resourceTables,
    HostLocalCore.auxiliaryTables, List.getElem_drop, Prod.mk.injEq] at same
  obtain ⟨rfl, rfl⟩ := same
  interval_cases i
  · exact suffix_array_at 84 (by decide) bounds (by omega) (host_arrays witness)
  · exact suffix_array_at 85 (by decide) bounds (by omega) (host_arrays witness)

private theorem word_records (last : Bool) (env : Environment Fp) :
    let ram := (HintReadCoverage.rowInput (last, env)).ram
    rowRecords (.host (.word last)) env =
      [(HintReadCoverage.rowActivity (last, env), AccessSupply.atClock (ram.clk_high, ram.clockLow) ram.prior)] := by
  let input := varFromOffset (F := Fp) HintReadWordChip.RowInput 0
  change [(env input.2, eval env (AccessSupply.atClock (input.1.ram.clk_high, input.1.ram.clockLow) input.1.ram.prior))] = _
  rw [← HintReadCoverage.eval_rowInput]
  simp only [AccessSupply.eval_atClock]
  simp only [HostRamAccessChip.Inputs.clockLow, HostRamAccessChip.Inputs.prior,
    HintReadCoverage.rowActivity, circuit_norm, input]

/-- Every active HINT_READ word contributes its original RAM predecessor at the exact call
clock. The physical array tracks the continuation and final-word variants separately. -/
theorem word_predecessor (witness : EnsembleWitness (HostObserved.ensemble image source target final))
    {row : HintReadCoverage.Row (p := SP1Prime)}
    (active : row ∈ TransitionView.readIndexedActiveRows HintReadCoverage.variants HintReadCoverage.view
      (HostHintReadLocal.wordTables (hostWitness witness))) :
    (1, AccessSupply.atClock (wordClock row) (touch row).1.1) ∈ records (raw witness) := by
  obtain ⟨member, on⟩ := HintReadCoverage.mem_active_rows.mp active
  obtain ⟨⟨last, table⟩, paired, mapped⟩ := List.mem_flatMap.mp member
  obtain ⟨cells, physical, rfl⟩ := List.mem_map.mp mapped
  have origin := word_origin witness paired
  rw [origin] at physical
  let actual := raw witness (.host (.word last))
  apply List.mem_flatMap.mpr
  refine ⟨.host (.word last), sources_complete _, List.mem_flatMap.mpr ⟨cells, physical, ?_⟩⟩
  rw [word_records]
  exact List.mem_singleton.mpr (Prod.ext on.symm rfl)

end SP1Clean.Export.WriteSourceRegistry
