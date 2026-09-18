import SP1Clean.Model.Core.HostExecutionLaws
import SP1Clean.Model.Machine.Syscall

/-! # Applying the native host interpreter to official Sail states

The read context uses the source state's actual registers and memory. Applying an execution
updates x5, PC, and exactly the returned memory-write interval. The adapter produces the event's
observations and return value from execution; it does not accept a claimed syscall result.
-/

namespace SP1Clean.Model.Core

open LeanRV64D LeanRV64D.Defs SP1Clean.Soundness.Target

def HostReadContext.ofSail (source : SailState) : HostReadContext where
  register := source.get_reg?
  byte := source.mem.get?

/-- The finite sequence of byte writes, with distinct consecutive addresses. -/
def HostMemoryWrite.entries (write : HostMemoryWrite) : List (ℕ × BitVec 8) :=
  (List.finRange write.bytes.length).map fun index =>
    (write.address + index.val, write.bytes[index.val])

/-- Reading back a written byte observes that byte, even when the cell already existed. -/
theorem HostMemoryWrite.read_written (write : HostMemoryWrite)
    (memory : Std.ExtHashMap ℕ (BitVec 8)) (index : ℕ) (bound : index < write.bytes.length) :
    (memory.insertMany write.entries).get? (write.address + index) = some write.bytes[index] := by
  apply Std.ExtHashMap.getElem?_insertMany_list_of_mem (k := write.address + index) (by simp)
  · rw [entries, List.pairwise_map]
    apply (List.nodup_finRange _).imp
    intro left right distinct
    simp only [beq_eq_false_iff_ne, ne_eq, Nat.add_left_cancel_iff]
    exact fun equal => distinct (Fin.ext equal)
  · exact List.mem_map.mpr ⟨⟨index, bound⟩, List.mem_finRange _, rfl⟩

/-- Applying a host write leaves every address outside its full interval unchanged. -/
theorem HostMemoryWrite.read_outside (write : HostMemoryWrite)
    (memory : Std.ExtHashMap ℕ (BitVec 8)) (query : ℕ)
    (outside : query < write.address ∨ write.address + write.bytes.length ≤ query) :
    (memory.insertMany write.entries).get? query = memory.get? query := by
  apply Std.ExtHashMap.getElem?_insertMany_list_of_contains_eq_false
  apply Bool.eq_false_iff.mpr
  intro present
  obtain ⟨entry, entryMem, rfl⟩ := List.mem_map.mp (List.contains_iff_mem.mp present)
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp entryMem
  simp only at outside
  have := index.isLt
  omega

/-- Apply the complete emitted write, including hint padding. -/
def HostEffect.applyMemory (effect : HostEffect) (memory : Std.ExtHashMap ℕ (BitVec 8)) :
    Std.ExtHashMap ℕ (BitVec 8) :=
  match effect.write with
  | none => memory
  | some write => memory.insertMany write.entries

/-- The actual Sail memory update preserves every protected byte. -/
theorem HostMemoryWrite.preserves_readOnly (write : HostMemoryWrite)
    (memory : Std.ExtHashMap ℕ (BitVec 8)) (policy : HostMemoryPolicy)
    (permitted : policy.permits write.address write.bytes.length = true)
    (query : ℕ) (readOnly : policy.readOnly query = true) :
    (memory.insertMany write.entries).get? query = memory.get? query := by
  apply Std.ExtHashMap.getElem?_insertMany_list_of_contains_eq_false
  apply Bool.eq_false_iff.mpr
  intro present
  have member := List.contains_iff_mem.mp present
  obtain ⟨entry, entryMem, rfl⟩ := List.mem_map.mp member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp entryMem
  have excluded := ((policy.permits_iff _ _).mp permitted).2.2 index.val index.isLt
  simp only at readOnly
  rw [readOnly] at excluded
  contradiction

def HostExecution.nextPc (execution : HostExecution) (pc : BitVec 64) : BitVec 64 :=
  if execution.kind = .halt then Machine.haltPc else pc + 4

/-- Host effects leave all architectural registers other than PC/x5 unchanged. -/
def HostExecution.apply (execution : HostExecution) (source : SailState) (pc : BitVec 64) : SailState :=
  { source with
    regs := (source.regs.insert Register.x5 execution.result).insert Register.PC (execution.nextPc pc)
    mem := execution.effect.applyMemory source.mem }

/-- Every integer register except the return register keeps its source observation. -/
theorem HostExecution.register_frame (execution : HostExecution) (source : SailState)
    (pc : BitVec 64) (index : BitVec 5) (other : index ≠ 5) :
    (execution.apply source pc).get_reg? index = source.get_reg? index := by
  have different : Register.x5 ≠ reg_idx_to_Register index := by simpa [eq_comm] using other
  simp [apply, SailState.get_reg?, Std.ExtDHashMap.get?_insert, different, PC_ne_reg_idx_toRegister]

def HostExecution.toEvent (execution : HostExecution) (clock : ℕ) (pc : BitVec 64) :
    Machine.CoreSyscallEvent where
  clock
  pc
  nextPc := execution.nextPc pc
  rawCode := execution.kind.code
  arg1 := execution.arg1
  arg2 := execution.arg2
  result := execution.result

/-- One committed ECALL, with explicit host state and a result computed from the source state. -/
def HostState.step (host : HostState) (policy : HostPolicy) (program : GuestProgram)
    (clock : ℕ) (source : SailState) : Option (HostState × SailState × Machine.CoreSyscallEvent) := do
  let pc ← source.regs.get? Register.PC
  if program.fetchWord pc = some ECALL_ENC then do
    let execution ← host.run policy (.ofSail source)
    some (execution.effect.state, execution.apply source pc, execution.toEvent clock pc)
  else none

/-- The returned event satisfies all instruction-row laws, including the computed HINT_LEN arm. -/
theorem HostExecution.rowLaw {host : HostState} {execution : HostExecution}
    (result : execution.result = host.result execution.kind) (clock : ℕ) (pc : BitVec 64) :
    (execution.toEvent clock pc).RowLaw := by
  rcases execution with ⟨kind, arg1, arg2, value, effect⟩
  dsimp only at result
  subst value
  cases kind <;> simp [toEvent, nextPc, HostState.result, SyscallKind.code,
    Machine.CoreSyscallEvent.RowLaw, Machine.CoreSyscallEvent.WellRouted,
    Machine.CoreSyscallEvent.syscallId, Machine.CoreSyscallEvent.tableByte,
    Machine.CoreSyscallEvent.ResultLaw, Machine.CoreSyscallEvent.PcLaw,
    Machine.CoreSyscallEvent.HandlerAddressesFit, Machine.CoreSyscallEvent.hasTable,
    Machine.haltSyscallId, Machine.enterUnconstrainedSyscallId, Machine.hintLenSyscallId]

/-- Dispatch observations and architectural application agree with both State endpoints. -/
theorem HostExecution.matchesStates {host : HostState} {policy : HostPolicy} {source : SailState}
    {execution : HostExecution} {pc : BitVec 64}
    (run : host.run policy (.ofSail source) = some execution)
    (atPc : source.regs.get? Register.PC = some pc) (clock : ℕ) :
    (execution.toEvent clock pc).MatchesStates source (execution.apply source pc) := by
  have observed := (host.run_eq_some_iff policy (.ofSail source) execution).mp run
  refine ⟨atPc, observed.2.1, observed.2.2.1, observed.2.2.2.1, ?_, ?_⟩
  · simp only [toEvent, apply, Std.ExtDHashMap.get?_insert_self]
  · simp [toEvent, apply, SailState.get_reg?]

/-- ROM preservation follows from execution's checked write plan, including all hint padding. -/
theorem HostExecution.preserves_readOnly {host : HostState} {policy : HostPolicy} {source : SailState}
    {execution : HostExecution} (run : host.run policy (.ofSail source) = some execution)
    (pc : BitVec 64) (query : ℕ) (readOnly : policy.memory.readOnly query = true) :
    (execution.apply source pc).mem.get? query = source.mem.get? query := by
  have executed := ((host.run_eq_some_iff policy (.ofSail source) execution).mp run).2.2.2.2.2
  change (execution.effect.applyMemory source.mem).get? query = source.mem.get? query
  cases actual : execution.effect.write with
  | none => simp only [HostEffect.applyMemory, actual]
  | some write =>
      simp only [HostEffect.applyMemory, actual]
      exact write.preserves_readOnly source.mem policy.memory
        (host.executeKind_write_permitted executed write actual) query readOnly

/-- All successful host calls preserve the complete memory map outside the permitted window. -/
theorem HostExecution.preserves_memory_outside {host : HostState} {policy : HostPolicy} {source : SailState}
    {execution : HostExecution} (run : host.run policy (.ofSail source) = some execution)
    (pc : BitVec 64) (query : ℕ) (outside : query < policy.memory.lower ∨ policy.memory.upper ≤ query) :
    (execution.apply source pc).mem.get? query = source.mem.get? query := by
  have executed := ((host.run_eq_some_iff policy (.ofSail source) execution).mp run).2.2.2.2.2
  change (execution.effect.applyMemory source.mem).get? query = source.mem.get? query
  cases actual : execution.effect.write with
  | none => simp only [HostEffect.applyMemory, actual]
  | some write =>
    simp only [HostEffect.applyMemory, actual]
    have bounds := (policy.memory.permits_iff _ _).mp
      (host.executeKind_write_permitted executed write actual)
    exact write.read_outside source.mem query (by omega)

/-- The graph of the concrete stateful interpreter, for one incoming host state. Whole runs
thread the returned host state; they do not reuse this incoming state at every instruction. -/
def HostState.handler (host : HostState) (policy : HostPolicy) : Machine.SyscallHandler :=
  fun program event source target =>
    ∃ nextHost, host.step policy program event.clock source = some (nextHost, target, event)

/-- A computed host step is a committed ECALL transition in the existing RISC-V event model.
No separate return-value, operand, or instruction-row-law premise is supplied. -/
theorem HostState.step_sound {host nextHost : HostState} {policy : HostPolicy}
    {program : GuestProgram} {clock : ℕ} {source target : SailState}
    {event : Machine.CoreSyscallEvent}
    (success : host.step policy program clock source = some (nextHost, target, event)) :
    Machine.AboutToExecuteEcall program source ∧
      Machine.SyscallTransition (host.handler policy) program event source target := by
  have parsed := success
  simp only [step, bind, Option.bind_eq_some_iff] at parsed
  obtain ⟨pc, atPc, parsed⟩ := parsed
  split_ifs at parsed with fetched
  · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at parsed
    obtain ⟨execution, run, rfl, rfl, rfl⟩ := parsed
    have binding := (host.run_eq_some_iff policy (.ofSail source) execution).mp run
    exact ⟨⟨pc, atPc, fetched⟩, execution.rowLaw binding.2.2.2.2.1 clock pc,
      execution.matchesStates run atPc clock, ⟨execution.effect.state, success⟩⟩

end SP1Clean.Model.Core
