import SP1Clean.Soundness.HostHintReadTrajectory
import SP1Clean.Soundness.HostFootprint

/-! # HINT_READ execution and exact RAM effects

The complete physical word inventory identifies every updated Sail RAM cell, including the
mandatory padding word. Canonical RAM keys derive destination alignment; cells outside that
inventory are unchanged. The installed AIR derives a real host execution at the exact next
paired-replay position, authenticating the complete event including its PC and recombined clock.
The timed step/frame bundle and complete outgoing snapshot agreement remain open.
-/

namespace SP1Clean.Soundness.HostHintReadCPU

open Circuit Air.Flat Channels Model.Core Semantics NativeCore HostHintReadLocal TimedGrounding

private theorem hint_word_written {execution : HostExecution} {address : ℕ} {bytes : Bytes}
    (written : execution.effect.write = some ⟨address, hintWriteBytes bytes⟩)
    (source : SailState) (pc : BitVec 64) (cell : RamCell) (entry : ℕ × BitVec 64)
    (member : entry ∈ HintQueue.wordWrites address bytes) (atAddress : cell.baseAddr.toNat = entry.1) :
    locContent (execution.apply source pc) (.ram cell) = some entry.2 := by
  obtain ⟨index, bound, rfl⟩ := List.mem_map.mp member
  have inside := List.mem_range.mp bound
  have full : 8 * index + 8 ≤ (hintWriteBytes bytes).length := by
    rw [HintQueue.wordCount_length]
    omega
  have read := hostExecution_written_word written source pc index full cell (by
    simpa only [Nat.mul_comm] using atAddress)
  rw [read]
  apply congrArg some
  change Word.bytesValue _ = Word.bytesValue (HintQueue.wordBytes bytes index)
  apply congrArg Word.bytesValue
  apply Vector.ext
  intro slot small
  have value := HintQueue.wordValue_byte bytes inside ⟨slot, small⟩
  rw [HintQueue.wordValue, Word.bytesValue_extract] at value
  simpa only [HostMemoryWrite.wordBytes, Vector.getElem_ofFn, Fin.getElem_fin, Nat.mul_comm]
    using value.symm

private theorem hint_cell_covered (address : ℕ) (bytes : Bytes) (aligned : address % 8 = 0)
    (cell : RamCell)
    (covered : cell.toNat ∈ (MemorySpan.mk address (hintWriteBytes bytes).length).cells) :
    ∃ word, (cell.baseAddr.toNat, word) ∈ HintQueue.wordWrites address bytes := by
  rw [MemorySpan.mem_cells, HintQueue.wordCount_length] at covered
  dsimp only at covered
  have quotient := Nat.mod_add_div address 8
  rw [aligned] at quotient
  have bound : cell.toNat - address / 8 < HintQueue.wordCount bytes := by omega
  refine ⟨HintQueue.wordValue bytes (cell.toNat - address / 8), List.mem_map.mpr
    ⟨cell.toNat - address / 8, List.mem_range.mpr bound, ?_⟩⟩
  congr 1
  rw [RamCell.baseAddr_toNat]
  omega

private theorem hint_write_frame {execution : HostExecution} {address : ℕ} {bytes : Bytes}
    (written : execution.effect.write = some ⟨address, hintWriteBytes bytes⟩)
    (aligned : address % 8 = 0) (source : SailState) (pc : BitVec 64) (cell : RamCell)
    (outside : ∀ entry ∈ HintQueue.wordWrites address bytes, entry.1 ≠ cell.baseAddr.toNat) :
    locContent (execution.apply source pc) (.ram cell) = locContent source (.ram cell) := by
  have excluded : cell.toNat ∉ (MemorySpan.mk address (hintWriteBytes bytes).length).cells := by
    intro covered
    obtain ⟨word, member⟩ := hint_cell_covered address bytes aligned cell covered
    exact outside _ member rfl
  apply locContent_ram_congr_cell
  intro slot
  change (execution.effect.applyMemory source.mem).get? (cell.baseAddr.toNat + slot.val) = _
  simp only [HostEffect.applyMemory, written]
  apply HostMemoryWrite.read_outside
  have outsideByte := MemorySpan.byte_outside ⟨address, (hintWriteBytes bytes).length⟩
    cell.toNat slot.val slot.isLt excluded
  simpa only [RamCell.baseAddr_toNat] using outsideByte

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

omit [Fact (2 ^ 25 < p)] in
private theorem word_cell (row : HintReadCoverage.Row (p := p))
    (facts : HostRamTouches.AccessFacts (HintReadCoverage.rowInput row).ram) :
    ∃ cell : RamCell, MemoryMsg.locOf (touch row).2 = .ram cell ∧
      cell.baseAddr.toNat = (HintReadWrites.produced row).1 := by
  have lower := facts.ram.1
  rw [facts.canonical.2.2] at lower
  change 2 ^ 16 ≤ (MemoryMsg.locOf (touch row).2).busAddress at lower
  cases located : MemoryMsg.locOf (touch row).2 with
  | reg index =>
    rw [located] at lower
    change 2 ^ 16 ≤ index.toNat at lower
    have bounded := index.isLt
    omega
  | ram cell =>
    refine ⟨cell, rfl, ?_⟩
    have address := address_loc row facts
    simpa only [located, MemLoc.busAddress, RamCell.baseAddr_toNat] using address.symm

omit [Fact (2 ^ 25 < p)] in
private theorem write_alignment (rows : List (HintReadCoverage.Row (p := p)))
    (facts : ∀ row ∈ rows, HostRamTouches.AccessFacts (HintReadCoverage.rowInput row).ram)
    (address : ℕ) (bytes : Bytes)
    (inventory : (rows.map HintReadWrites.produced).Perm (HintQueue.wordWrites address bytes)) :
    address % 8 = 0 := by
  have first : (address, HintQueue.wordValue bytes 0) ∈ HintQueue.wordWrites address bytes := by
    apply List.mem_map.mpr
    exact ⟨0, List.mem_range.mpr (HintQueue.wordCount_pos bytes), by simp⟩
  obtain ⟨row, member, same⟩ := List.mem_map.mp (inventory.mem_iff.mpr first)
  obtain ⟨cell, _, atAddress⟩ := word_cell row (facts row member)
  have base : cell.baseAddr.toNat = address := atAddress.trans (congrArg Prod.fst same)
  rw [← base, RamCell.baseAddr_toNat]
  omega

omit [Fact (2 ^ 25 < p)] in
/-- The complete physical inventory realizes every pushed RAM word and preserves every other
RAM cell. No assumption about overwritten values or previous Memory records is needed. -/
theorem hint_memory_effect (input : HostHintReadChip.Inputs (ZMod p)) (host : HostState)
    (bytes : Bytes) (rest : List Bytes) (rows : List (HintReadCoverage.Row (p := p)))
    (facts : ∀ row ∈ rows, HostRamTouches.AccessFacts (HintReadCoverage.rowInput row).ram)
    (inventory : (rows.map HintReadWrites.produced).Perm
      (HintQueue.wordWrites (Address.toNat input.span.start) bytes))
    (source : SailState) (pc : BitVec 64) :
    (∀ row ∈ rows, locContent ((HostHintReadChip.execution input host bytes rest).apply source pc)
        (MemoryMsg.locOf (touch row).2) = some (Word.toBitVec64 (touch row).2.value)) ∧
      (∀ cell : RamCell, (∀ row ∈ rows, MemoryMsg.locOf (touch row).2 ≠ .ram cell) →
        locContent ((HostHintReadChip.execution input host bytes rest).apply source pc) (.ram cell) =
          locContent source (.ram cell)) := by
  constructor
  · intro row member
    obtain ⟨cell, located, address⟩ := word_cell row (facts row member)
    rw [located]
    exact hint_word_written (execution := HostHintReadChip.execution input host bytes rest) rfl
      source pc cell (HintReadWrites.produced row)
      (inventory.mem_iff.mp (List.mem_map_of_mem member)) address
  · intro cell outside
    apply hint_write_frame (execution := HostHintReadChip.execution input host bytes rest) rfl
      (write_alignment rows facts _ bytes inventory) source pc cell
    intro entry member same
    obtain ⟨row, rowMem, rowEq⟩ := List.mem_map.mp (inventory.mem_iff.mpr member)
    obtain ⟨actual, located, address⟩ := word_cell row (facts row rowMem)
    have equalAddress : actual.baseAddr.toNat = cell.baseAddr.toNat :=
      address.trans ((congrArg Prod.fst rowEq).trans same)
    have equal : actual = cell := by
      apply BitVec.eq_of_toNat_eq
      rw [RamCell.baseAddr_toNat, RamCell.baseAddr_toNat] at equalAddress
      omega
    exact outside row rowMem (located.trans (congrArg MemLoc.ram equal))

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)} {channels : List (RawChannel (ZMod p))}

omit [Fact (2 ^ 25 < p)] in
private theorem hint_event (wrapper : HostCallChip.Inputs (ZMod p)) (flag : ZMod p)
    (input : HostHintReadChip.Inputs (ZMod p)) (host : HostState) (bytes : Bytes) (rest : List Bytes)
    (same : wrapper.message flag = input.call)
    (code : Word.toBitVec64 (wrapper.message flag).code = SyscallKind.hintRead.code)
    (law : (syscallEventOfRow wrapper.instruction).RowLaw)
    (clock : ℕ) (atClock : clock = (syscallEventOfRow wrapper.instruction).clock) :
    (HostHintReadChip.execution input host bytes rest).toEvent clock
      (StateMsg.pcBits (SyscallInstrsChip.statePulledMessage wrapper.instruction)) =
        syscallEventOfRow wrapper.instruction := by
  have raw : (syscallEventOfRow wrapper.instruction).rawCode = SyscallKind.hintRead.code := code
  have next := law.2.2.1
  simp only [Machine.CoreSyscallEvent.PcLaw, Machine.CoreSyscallEvent.syscallId, raw,
    SyscallKind.code, Machine.haltSyscallId] at next
  change (syscallEventOfRow wrapper.instruction).nextPc = (syscallEventOfRow wrapper.instruction).pc + 4 at next
  have arg1 : Word.toBitVec64 input.call.arg1 = (syscallEventOfRow wrapper.instruction).arg1 := by
    rw [← same]; rfl
  have arg2 : Word.toBitVec64 input.call.arg2 = (syscallEventOfRow wrapper.instruction).arg2 := by
    rw [← same]; rfl
  have result : Word.toBitVec64 input.call.result = (syscallEventOfRow wrapper.instruction).result := by
    rw [← same]; rfl
  have pc : StateMsg.pcBits (SyscallInstrsChip.statePulledMessage wrapper.instruction) =
      (syscallEventOfRow wrapper.instruction).pc := rfl
  have stamp : clock = (syscallEventOfRow wrapper.instruction).clock := atClock
  simp only [HostExecution.toEvent, HostHintReadChip.execution, HostExecution.nextPc,
    reduceCtorEq, ↓reduceIte, arg1, arg2, result, pc, stamp, ← raw, ← next]

private theorem source_memory_effect
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (event : ExecutionRow p)
    (member : event ∈ LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)))
    (env : Environment (ZMod p))
    (handler : env ∈ (handlerTable (HostHintQueueBoundary.expanded witness)).table.map
      (handlerTable (HostHintQueueBoundary.expanded witness)).environment)
    (clock : StateMsg.timeNat (event.edge witness.data).1 = HostQueueCPUOrder.eventTime (none, env))
    (host : HostState) (bytes : Bytes) (remaining : List Bytes)
    (inventory : ((TransitionView.readIndexedRows HintReadCoverage.variants
      (HostHintReadPartition.tablesFor (HostHintReadPartition.callClock env)
        (wordTables (HostHintQueueBoundary.expanded witness)))).map HintReadWrites.produced).Perm
      (HintQueue.wordWrites (Address.toNat (HostHintReadCoverage.input env).span.start) bytes))
    (state : SailState) (pc : BitVec 64) :
    (∀ row ∈ wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.expanded witness))) event,
      locContent ((HostHintReadChip.execution (HostHintReadCoverage.input env) host bytes remaining).apply state pc)
        (MemoryMsg.locOf (touch row).2) = some (Word.toBitVec64 (touch row).2.value)) ∧
    (∀ cell : RamCell, (∀ row ∈ wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.expanded witness))) event, MemoryMsg.locOf (touch row).2 ≠ .ram cell) →
      locContent ((HostHintReadChip.execution (HostHintReadCoverage.input env) host bytes remaining).apply state pc)
        (.ram cell) = locContent state (.ram cell)) := by
  have checks := HostHintQueueBoundary.expanded_constraints witness constraints
  have balance := HostHintQueueBoundary.expanded_balanced witness balanced
  have interface := HostHintQueueBoundary.expanded_interface (source := source) (final := final)
    (source_interface (p := p) source.host.io.hints)
  have selected := handler_wordsAt (HostHintQueueBoundary.expanded witness) interface checks balance
    event member env handler clock
  have data : (HostHintQueueBoundary.expanded witness).data = witness.data := rfl
  rw [data] at selected
  have writes : ((wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
      (wordTables (HostHintQueueBoundary.expanded witness))) event).map HintReadWrites.produced).Perm
      (HintQueue.wordWrites (Address.toNat (HostHintReadCoverage.input env).span.start) bytes) := by
    rw [selected]
    exact inventory
  exact hint_memory_effect (HostHintReadCoverage.input env) host bytes remaining _
    (fun row present => source_word_touches witness constraints balanced row (List.mem_filter.mp present).1)
    writes state pc

/-- The physical HINT_READ executes at its exact position on paired replay. Its semantic
successor realizes all grouped RAM pushes and preserves every other RAM cell. The only semantic
antecedents are the incoming State and operand currency supplied by timed grounding. -/
theorem GroundingCarrier.hintRead_step (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (event : ExecutionRow p)
    (member : event ∈ LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)))
    (env : Environment (ZMod p))
    (handler : env ∈ (handlerTable (HostHintQueueBoundary.expanded witness)).table.map
      (handlerTable (HostHintQueueBoundary.expanded witness)).environment)
    (clock : StateMsg.timeNat (event.edge witness.data).1 = HostQueueCPUOrder.eventTime (none, env))
    (pull : LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid) carrier.timeline
      (event.facts witness.data).statePull)
    (currency : ∀ mp ∈ (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.expanded witness))) event).memPulls,
      MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 ∧
      LocalValueAtG (carrier.trajectory valid) source.sail.realize carrier.timeline (MemoryMsg.locOf mp.1) mp.2 mp.1.value) :
    ∃ n current next, carrier.ordered[n]? = some event ∧
      carrier.pairedTrajectory valid n = some current ∧ carrier.pairedTrajectory valid (n + 1) = some next ∧
      ExecutionStep ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid) current event.event next ∧
      (∀ row ∈ wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
          (wordTables (HostHintQueueBoundary.expanded witness))) event,
        locContent next.sail (MemoryMsg.locOf (touch row).2) = some (Word.toBitVec64 (touch row).2.value)) ∧
      (∀ cell : RamCell, (∀ row ∈ wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
          (wordTables (HostHintQueueBoundary.expanded witness))) event, MemoryMsg.locOf (touch row).2 ≠ .ram cell) →
        locContent next.sail (.ram cell) = locContent current.sail (.ram cell)) := by
  obtain ⟨n, current, _, bytes, remaining, atIndex, paired, _, _, _, ran, inventory⟩ :=
    carrier.hintRead_run valid constraints balanced event member env handler clock pull
      (fun mp present => (currency mp present).2.2)
  have time := ExecutionCarrier.time_of_ordered_at carrier atIndex
  change StateMsg.timeNat (event.facts witness.data).statePull = carrier.timeline.start n at time
  have before : carrier.trajectory valid n = some current.sail := by
    simp only [GroundingCarrier.trajectory, paired, Option.map_some]
  obtain ⟨m, state, present, atTime, atPc, _⟩ := pull
  have sameIndex : m = n := start_injective carrier.timeline (atTime.symm.trans time)
  subst m
  have sail : current.sail = state := Option.some.inj (before.symm.trans present)
  rw [← sail] at atPc
  have covered : n ≤ carrier.events.length := by
    have bound := (List.getElem?_eq_some_iff.mp atIndex).1
    simpa only [ExecutionCarrier.events, List.length_map] using Nat.le_of_lt bound
  have currentTime : current.clock = carrier.timeline.start n := by
    rw [carrier.timeline_events constraints balanced, eventTimeline_start_le _ _ _ covered]
    exact replayEvents?_clock paired
  have checks := HostHintQueueBoundary.expanded_constraints witness constraints
  have balance := HostHintQueueBoundary.expanded_balanced witness balanced
  have interface := HostHintQueueBoundary.expanded_interface (source := source) (final := final)
    (source_interface (p := p) source.host.io.hints)
  have handlerMember : (none, env) ∈ TransitionView.readIndexedRows HostQueueOrder.indices
      (queueTables (HostHintQueueBoundary.expanded witness)) := by
    obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp handler
    simp only [TransitionView.readIndexedRows, HostQueueOrder.indices, queueTables,
      List.zip_cons_cons, List.flatMap_cons]
    exact List.mem_append_left _ (List.mem_map_of_mem physicalMem)
  obtain ⟨physical, active, sameCall, sameEvent⟩ := HostQueueCPUOrder.call_cpu_at
    (HostHintQueueBoundary.expanded witness) interface checks balance (none, env) handlerMember event member clock
  have original : ∀ mp ∈ (syscallRowFacts (HostCallLedger.input physical).instruction).memPulls,
      MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 ∧
      LocalValueAtG (carrier.trajectory valid) source.sail.realize carrier.timeline (MemoryMsg.locOf mp.1) mp.2 mp.1.value := by
    intro mp present
    apply currency mp
    apply List.mem_append_left
    simpa only [sameEvent, ExecutionRow.facts] using present
  have instructionTime : StateMsg.timeNat (SyscallInstrsChip.statePulledMessage
      (HostCallLedger.input physical).instruction) = carrier.timeline.start n := by
    simpa only [sameEvent, ExecutionRow.facts, syscallRowFacts_statePull] using time
  have registers := HostLocalCore.hostCall_registers valid (HostHintQueueBoundary.expanded witness)
    (source_program_silent source final) checks balance physical active _ source.sail.realize current.sail _ n
    before instructionTime (fun mp present => (original mp present).2.2)
  have law := HostLocalCore.hostCall_eventLaw (HostHintQueueBoundary.expanded witness)
    (auxiliaryInterface interface) (source_program_silent source final) checks balance physical active
    (fun mp present => ⟨(original mp present).1, (original mp present).2.1⟩)
  have observed := (current.host.run_eq_some_iff _ _ _).mp ran
  have code := Option.some.inj (registers.1.symm.trans observed.2.1)
  have label := hint_event (HostCallLedger.input physical) _ (HostHintReadCoverage.input env)
    current.host bytes remaining sameCall code law.1 current.clock
    (currentTime.trans (instructionTime.symm.trans law.2.symm))
  have committed := HostLocalCore.hostCall_program_committed valid (HostHintQueueBoundary.expanded witness)
    (source_program_silent source final) checks balance physical active
  have fetched := (committed.ecall_of_opcode rfl).1
  change (image.toGuestProgram valid).fetchWord
    (StateMsg.pcBits (SyscallInstrsChip.statePulledMessage (HostCallLedger.input physical).instruction)) =
      some Target.ECALL_ENC at fetched
  change current.sail.regs.get? LeanRV64D.Defs.Register.PC =
    some (StateMsg.pcBits (event.facts witness.data).statePull) at atPc
  have sourcePc : StateMsg.pcBits (event.facts witness.data).statePull =
      StateMsg.pcBits (SyscallInstrsChip.statePulledMessage (HostCallLedger.input physical).instruction) := by
    rw [sameEvent]; rfl
  let execution := HostHintReadChip.execution (HostHintReadCoverage.input env) current.host bytes remaining
  let next : ExecutionState := ⟨execution.apply current.sail (StateMsg.pcBits (event.facts witness.data).statePull),
    execution.effect.state, current.clock + Machine.syscallSchedule.duration⟩
  have step : ExecutionStep ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid) current event.event next := by
    have stepped : current.host.step ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
        current.clock current.sail = some (execution.effect.state, next.sail,
          syscallEventOfRow (HostCallLedger.input physical).instruction) := by
      simp only [HostState.step, atPc, Bind.bind, Option.bind_some, sourcePc, fetched, ↓reduceIte, ran]
      simp only [next, execution, sourcePc, label]
    rw [sameEvent]
    exact ExecutionStep.syscall stepped
  have after : carrier.pairedTrajectory valid (n + 1) = some next := by
    change ExecutionCarrier.pairedTrajectory carrier _ _ _ (n + 1) = _
    rw [ExecutionCarrier.pairedTrajectory_succ carrier _ _ _ member time]
    change (carrier.pairedTrajectory valid n).bind _ = _
    rw [paired, Option.bind_some, step.replay]
  have effect := source_memory_effect witness constraints balanced event member env handler clock
    current.host bytes remaining inventory current.sail (StateMsg.pcBits (event.facts witness.data).statePull)
  exact ⟨n, current, next, atIndex, paired, after, step, effect⟩

end SP1Clean.Soundness.HostHintReadCPU
