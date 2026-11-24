import SP1Clean.Export.WriteSourceGrounding
import SP1Clean.Soundness.HostHintReadExecutionRows
import SP1Clean.Soundness.HostHintReadTerminalProjection

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

private theorem ecall_rows (witness : EnsembleWitness (HostObserved.ensemble image source target final)) :
    (HostLocalCore.hostCallTable (hostWitness witness)).table = (raw witness (.host .ecall)).table := by
  have h := host_arrays witness
  have same := List.getElem_of_eq h (i := 0) (by
    rw [h, List.length_map, List.length_drop, ← witness.same_length, HostObserved.tables_length]; decide)
  simp only [List.getElem_map, List.getElem_drop, Nat.add_zero] at same
  exact same

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
  rw [ecall_rows witness] at present
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

private theorem host_record_of_origin (witness : EnsembleWitness (HostObserved.ensemble image source target final))
    (checked : witness.Constraints) (family : HostSources.Family) {record : Readback Fp}
    (origin : Origin (raw witness) (.host family) record) :
    ∃ cells ∈ (raw witness (.host family)).table, (1, record) ∈ rowRecords (.host family)
      ((raw witness (.host family)).environment cells) := by
  obtain ⟨cells, present, weight, prior, positive, pulled, rfl⟩ := origin
  have occurrence := records_of_pull (raw witness) (raw_registered witness) (.host family) cells present weight prior pulled
  have unit := positive_record_unit witness checked occurrence positive
  subst weight
  rw [raw_registered witness (.host family)] at pulled
  exact ⟨cells, present, host_records_of_pull family _ 1 prior pulled⟩

private theorem host_record_data (family : HostSources.Family) (cells : Array Fp) (left right : ProverData Fp) :
    rowRecords (.host family) (Environment.fromArray cells left) = rowRecords (.host family) (Environment.fromArray cells right) := by
  cases family with
  | ecall => rw [ecall_records, ecall_records]; rfl
  | word last => rw [word_records, word_records]; rfl

/-- Each authenticated ECALL receipt is one of the three actual predecessor reads in a
real decoded syscall row, stamped with that row's incoming State. -/
theorem syscall_event_of_origin (witness : EnsembleWitness (HostObserved.ensemble image source target final))
    (checked : witness.Constraints) {record : Readback Fp} (origin : Origin (raw witness) (.host .ecall) record) :
    ∃ row, ExecutionRow.syscall row ∈ LocalCore.executionRows (HostFinalMemory.coreWitness (HostObserved.baseWitness witness)) ∧
      ∃ prior time, (prior, time) ∈ (syscallRowFacts row).memPulls ∧
        let state := SyscallInstrsChip.statePulledMessage row
        record = AccessSupply.atClock (state.clk_high, state.clk_low) prior := by
  obtain ⟨cells, present, found⟩ := host_record_of_origin witness checked .ecall origin
  let host := hostWitness witness
  let env := Environment.fromArray cells host.data
  simp only [Table.environment] at found
  rw [host_record_data .ecall cells _ host.data, ecall_records] at found
  obtain ⟨⟨prior, time⟩, read, eq⟩ := List.mem_map.mp found
  have enabled : (HostCallLedger.input env).is_real = 1 := congrArg Prod.fst eq
  have member : env ∈ HostCallLedger.activeRows (HostLocalCore.hostCallTable host) host.data := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_map.mpr ⟨cells, ?_, rfl⟩, ?_⟩
    · rwa [ecall_rows witness]
    · simpa only [decide_eq_true_eq] using enabled
  have decoded := List.mem_map_of_mem (f := HostCallLedger.input) member
  rw [HostLocalCore.hostCallTable_projection host] at decoded
  refine ⟨HostCallLedger.input env, List.mem_append_right _ (List.mem_map_of_mem (f := ExecutionRow.syscall) decoded),
    prior, time, read, ?_⟩
  exact (congrArg Prod.snd eq).symm

/-- Each authenticated HINT_READ receipt originates at the exact word and clock of one
of the two active word tables. -/
theorem word_of_origin (witness : EnsembleWitness (HostObserved.ensemble image source target final))
    (checked : witness.Constraints) (last : Bool) {record : Readback Fp}
    (origin : Origin (raw witness) (.host (.word last)) record) :
    ∃ row ∈ TransitionView.readIndexedActiveRows HintReadCoverage.variants HintReadCoverage.view
      (HostHintReadLocal.wordTables (hostWitness witness)), record = AccessSupply.atClock (wordClock row) (touch row).1.1 := by
  obtain ⟨cells, present, found⟩ := host_record_of_origin witness checked (.word last) origin
  let tables := HostHintReadLocal.wordTables (hostWitness witness)
  have counts : 2 = tables.length := (HostHintReadLocal.wordTables_aligned (hostWitness witness)).length_eq
  let index : Fin 2 := if last then 1 else 0
  let table := tables[index.val]'(counts ▸ index.isLt)
  have pair : (last, table) ∈ HintReadCoverage.variants.zip tables := by
    have inside : index.val < (HintReadCoverage.variants.zip tables).length := by
      rw [List.length_zip, ← counts]; exact index.isLt
    have entry := List.getElem_mem (l := HintReadCoverage.variants.zip tables) inside
    simp only [List.getElem_zip] at entry
    cases last <;> exact entry
  have physical : cells ∈ table.table := (word_origin witness pair).symm ▸ present
  let row : HintReadCoverage.Row (p := SP1Prime) := (last, table.environment cells)
  simp only [Table.environment] at found
  rw [host_record_data (.word last) cells _ table.data, word_records, List.mem_singleton] at found
  refine ⟨row, HintReadCoverage.mem_active_rows.mpr ⟨?_, ?_⟩, ?_⟩
  · exact List.mem_flatMap.mpr ⟨(last, table), pair, List.mem_map.mpr ⟨cells, physical, rfl⟩⟩
  · exact (congrArg Prod.fst found).symm
  · change (1, record) = (HintReadCoverage.rowActivity row, AccessSupply.atClock (wordClock row) (touch row).1.1) at found
    exact congrArg Prod.snd found

/-- Every predecessor of an actual CPU event is published at that event's incoming cut.
This combines ordinary accesses, ECALL operands, and HINT_READ words selected by the full
clock. The constrained legacy HALT table has no real rows. -/
theorem event_predecessor (witness : EnsembleWitness (HostObserved.ensemble image source target final))
    (checked : witness.Constraints) {event : ExecutionRow SP1Prime}
    (present : event ∈ LocalCore.executionRows (HostFinalMemory.coreWitness (HostObserved.baseWitness witness)))
    (data : ProverData Fp) {prior : MemoryMsg Fp} {time : ℕ} :
    let words := TransitionView.readIndexedActiveRows HintReadCoverage.variants HintReadCoverage.view
      (HostHintReadLocal.wordTables (hostWitness witness))
    (prior, time) ∈ (eventFacts data words event).memPulls →
      (1, AccessSupply.atClock (cpuClock data event) prior) ∈ records (raw witness) := by
  intro words pulled
  rcases List.mem_append.mp pulled with initial | additional
  · cases event with
    | instruction row => exact (execution_ordinary_predecessor witness present data initial).2
    | syscall row => exact syscall_predecessor witness present initial
    | halt row =>
      let memory := HostObserved.baseWitness witness
      let boundary := HostFinalMemory.baseWitness memory
      have noHalt := HostHintReadTerminal.legacy_rows_nil boundary
        (HostFinalMemory.baseWitness_constraints memory (HostObserved.baseWitness_constraints witness checked))
      have enabled : row ∈ activeSystemRows (LocalCore.systemTable (HostLocalCore.localWitness (HostHintQueueBoundary.projected boundary)) 2)
          (haltRow (HostLocalCore.localWitness (HostHintQueueBoundary.projected boundary)).data) (·.is_real) := by
        change ExecutionRow.halt row ∈ LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected boundary)) at present
        simpa [LocalCore.executionRows] using present
      rw [noHalt] at enabled
      exact False.elim (List.not_mem_nil enabled)
  · obtain ⟨row, selected, same⟩ := List.mem_map.mp additional
    obtain ⟨inWords, clock⟩ := List.mem_filter.mp selected
    have record := word_predecessor witness inWords
    have key : wordClock row = cpuClock data event := of_decide_eq_true clock
    rw [key] at record
    have message : (touch row).1.1 = prior := congrArg Prod.fst same
    rwa [message] at record

/-- The State ledger orders the entire CPU tape. At every index, the physical publishers
contain every predecessor of the indexed event, stamped with its incoming clock. -/
theorem ordered_predecessors (witness : EnsembleWitness (HostObserved.ensemble image source target final))
    (checked : witness.Constraints)
    (ordering : LocalCore.OrderingChannels (HostFinalMemory.coreWitness (HostObserved.baseWitness witness))) :
    let core := HostFinalMemory.coreWitness (HostObserved.baseWitness witness)
    let words := TransitionView.readIndexedActiveRows HintReadCoverage.variants HintReadCoverage.view
      (HostHintReadLocal.wordTables (hostWitness witness))
    ∃ ordered : List (ExecutionRow SP1Prime), ordered.Perm (LocalCore.executionRows core) ∧
      Walk.IsWalk (ExecutionRow.canonEdge core.data) (initialBoundaryStateMessage core.publicInput)
        (finalBoundaryStateMessage core.publicInput) ordered ∧
      ∀ (index : Fin ordered.length) (prior : MemoryMsg Fp) (time : ℕ),
        (prior, time) ∈ (eventFacts core.data words ordered[index]).memPulls →
          (1, AccessSupply.atClock (cpuClock core.data ordered[index]) prior) ∈ records (raw witness) := by
  intro core words
  have memory := HostObserved.baseWitness_constraints witness checked
  have sourceBoundary := HostFinalMemory.baseWitness_constraints _ memory
  have physical := HostLocalCore.localWitness_constraints _ (HostHintQueueBoundary.projected_constraints _ sourceBoundary)
  obtain ⟨ordered, perm, walk⟩ := LocalCore.executionRows_ordered_of_orderingChannels core physical ordering
  refine ⟨ordered, perm, walk, fun index _ _ pulled => ?_⟩
  exact event_predecessor witness checked (perm.mem_iff.mp (List.getElem_mem index.isLt)) core.data pulled


/-- The signed host protocols and original Memory ledger retain
all physical occurrences when removing the observation, final-memory and queue endpoints. -/
theorem host_protocol_ledger (witness : EnsembleWitness (HostObserved.ensemble image source target final)) (channel : RawChannel Fp)
    (protocol : channel ∈ [HostCallChip.channel.toRaw, HintReadWordChip.stateChannel.toRaw, HostHintQueue.wordChannel.toRaw, memoryChannel.toRaw]) :
    (hostWitness witness).interactionsWith channel = witness.interactionsWith channel := by
  let memory := HostObserved.baseWitness witness
  let boundary := HostFinalMemory.baseWitness memory
  have names := List.mem_map_of_mem (f := RawChannel.name) protocol
  have different (other : RawChannel Fp) (fresh : other.name ∉ ([HostCallChip.channel.toRaw, HintReadWordChip.stateChannel.toRaw,
      HostHintQueue.wordChannel.toRaw, memoryChannel.toRaw] : List (RawChannel Fp)).map RawChannel.name) : channel ≠ other :=
    fun same => fresh (same ▸ names)
  have reg : channel ∈ HostLocalCore.registry image source (HintReadWordChip.stateChannel.toRaw ::
      HostFinalMemory.sourceChannels (p := SP1Prime) target.sail.memorySnapshot) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at protocol
    rcases protocol with rfl | rfl | rfl | rfl <;>
      simp [HostLocalCore.registry, HostFinalMemory.sourceChannels, LocalCore.baseEnsemble, sp1Ensemble_channels]
  have qa := HostHintQueueBoundary.projected_silent_interactions boundary channel (List.mem_append_left _ reg)
    (HostHintQueueBoundary.boundary_silent _ (different _ (by decide)) (different _ (by decide))
      (different _ (by decide)) (different _ (by decide)))
  have fm := HostFinalMemory.baseWitness_silent_interactions memory channel (List.mem_append_left _ (List.mem_append_left _ reg))
    (different _ (by decide)) (different _ (by decide)) (different _ (by decide))
  have obs := HostObserved.baseWitness_interactions witness channel
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ reg)))
    (different _ (by decide)) (different _ (by decide))
  exact qa.trans (fm.trans obs)

private theorem hostWitness_data (witness : EnsembleWitness (HostObserved.ensemble image source target final)) :
    (hostWitness witness).data = witness.data := by
  rw [hostWitness, HostHintQueueBoundary.projected_data, HostFinalMemory.baseWitness_data, HostObserved.baseWitness_data witness]

private theorem word_table_pair (witness : EnsembleWitness (HostObserved.ensemble image source target final))
    {last : Bool} {table : Table Fp}
    (paired : (last, table) ∈ HintReadCoverage.variants.zip (HostHintReadLocal.wordTables (hostWitness witness))) :
    table = raw witness (.host (.word last)) := by
  let host := hostWitness witness
  have member := (List.of_mem_zip paired).2
  have left := host.same_data table (HostHintReadLocal.wordTables_mem host table member)
  have right := witness.same_data (raw witness (.host (.word last))) ((originalSlot (.host (.word last))).table_mem witness)
  have component := (List.forall₂_zip (HostHintReadLocal.wordTables_aligned host) paired).symm
  have actual := raw_registered witness (.host (.word last))
  change (raw witness (.host (.word last))).component = (HintReadCoverage.view last).component at actual
  exact Table.ext_iff.mpr ⟨component.trans actual.symm, word_origin witness paired,
    left.trans ((hostWitness_data witness).trans right.symm)⟩

private theorem paired_of_mem {left : List Bool} {right : List (Table Fp)}
    (lengths : left.length = right.length) {t : Table Fp} (member : t ∈ right) : ∃ tag, (tag, t) ∈ left.zip right := by
  obtain ⟨i, h, rfl⟩ := List.mem_iff_getElem.mp member
  have inside : i < (left.zip right).length := by rw [List.length_zip, lengths]; exact lt_min h h
  exact ⟨_, List.getElem_zip .. ▸ (List.getElem_mem (l := left.zip right) inside)⟩

/-- Word tables in the inner history decoder are the exact original physical tables in the
supervisor, including the component, row order, multiplicities and verifier-derived data. -/
theorem word_table_eq (witness : EnsembleWitness (HostObserved.ensemble image source target final)) {table : Table Fp}
    (member : table ∈ HostHintReadLocal.wordTables (hostWitness witness)) :
    ∃ last, table = raw witness (.host (.word last)) := by
  obtain ⟨tag, pair⟩ := paired_of_mem (HostHintReadLocal.wordTables_aligned (hostWitness witness)).length_eq member
  exact ⟨tag, word_table_pair witness pair⟩

end SP1Clean.Export.WriteSourceRegistry
