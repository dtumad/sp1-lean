import SP1Clean.Export.WriteGeneratedHostSources
import SP1Clean.Proofs.Completeness.WriteFinalSourceBounds

/-! # The clock limbs of every physical ECALL read-back

A unit ECALL receipt identifies one of the three register reads of an actual mixed instruction.
Its previous timestamp comes from the original mixed Memory tape, and its closing clock from
that syscall's real CPU position. Disabled rows have no unit receipt.
-/

namespace SP1Clean.Export.WriteSourceRegistry

open Circuit Air.Flat Channels Soundness Machine Semantics TraceGen FormalModel.Shard
open WriteProbe WriteProbe.AccessInventory

private abbrev F := ZMod SP1Prime

private theorem syscall_clock {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    {f : AccessFrontier} {base : ℕ} {call : CoreSyscallEvent} (used : MixedCompiledRow.syscall f base call ∈ rows) :
    base = call.clock ∧ activeClockPhase call.clock ∧ call.clock < 2 ^ 48 := by
  obtain ⟨i, found⟩ := List.mem_iff_getElem?.mp used
  obtain ⟨actual, made, size⟩ := admissibleExecution_routeMixedRows run
  have length : rows.length = events.length := Option.some.inj (routed.symm.trans made) ▸ size
  have inTape : i < events.length := (List.getElem?_eq_some_iff.mp found).1.trans_eq length
  have present := List.getElem?_eq_getElem inTape
  generalize events[i] = event at present
  obtain ⟨current, incoming, next, prefixAt, _, emitted⟩ := routeMixedRows?_at routed present
  cases event with
  | ordinary =>
    obtain ⟨_, _, _, _, atRow⟩ := emitted
    cases Option.some.inj (found.symm.trans atRow)
  | syscall candidate =>
    cases Option.some.inj (found.symm.trans emitted)
    obtain ⟨s, _, _, _, compared, step, _, _, phase, small, _⟩ := admissibleExecution_syscall_from_prefix run present
    cases Option.some.inj (prefixAt.symm.trans compared)
    have clock := step.startsAt
    change call.clock = current.clock at clock
    exact ⟨clock.symm, clock ▸ phase, clock ▸ (by omega)⟩

private theorem operand_bound {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    {row : MixedCompiledRow} (found : row ∈ rows) {a : MemoryHistoryAccess} (operand : a ∈ MixedMemoryHistory.instruction row) :
    a.previous < 2 ^ 48 := by
  have partition : (MixedMemoryHistory.cpu row).Perm
      (row.bumpInput.refreshes.map MemoryHistoryAccess.ofMemoryBump ++ MixedMemoryHistory.instruction row) := by
    simpa only [List.flatMap_singleton, List.map_singleton, MixedBumpInput.memoryRows] using MixedMemoryHistory.cpu_partition [row]
  have member := partition.mem_iff.mpr (List.mem_append_right _ operand)
  obtain ⟨i, inside, same⟩ := List.mem_iff_getElem.mp found
  have inTape : a ∈ MixedMemoryHistory.stream image source events rows :=
    List.mem_flatMap.mpr ⟨⟨i,inside⟩, List.mem_finRange _, List.mem_append_left _ (same ▸ member)⟩
  exact ((MixedMemoryHistory.record_chronology run routed).2 a inTape).trans (MixedMemoryHistory.posted_clock_bound run routed inTape)

/-- Every unit receipt on the genuine generated ECALL table has four bounded 24-bit limbs,
including when global canonicalization supplies different evaluation data. -/
theorem generated_ecall_bounded {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (data evaluation : ProverData F) (hint : ProverHint F) (fit)
    {cells : Array F} (present : cells ∈ (MixedSyscallTable.table rows data hint fit).table) {r : Readback F}
    (unit : (1,r) ∈ rowRecords (.host .ecall) (Environment.fromArray cells evaluation)) : Counted.Bounded r := by
  let : DecidableEq F := FiniteField.instDecidableEq
  let original := MixedSyscallTable.table rows data hint fit
  let env := Environment.fromArray cells evaluation
  rw [ecall_records] at unit
  obtain ⟨⟨prior, time⟩, pulled, eq⟩ := List.mem_map.mp unit
  have enabled : (HostCallLedger.input env).is_real = 1 := congrArg Prod.fst eq
  have real : env ∈ HostCallLedger.activeRows original evaluation :=
    List.mem_filter.mpr ⟨List.mem_map_of_mem present, decide_eq_true enabled⟩
  have issued := List.mem_map_of_mem (f := HostCallLedger.input) real
  rw [MixedSyscallTable.active] at issued
  obtain ⟨entry, placed, decoded⟩ := List.mem_filterMap.mp issued
  cases entry with
  | ordinary => contradiction
  | syscall f base call =>
    obtain ⟨rfl, phase, fits⟩ := syscall_clock run routed placed
    have input : syscallInstruction f call = HostCallLedger.input env := Option.some.inj decoded
    have mem : prior ∈ ((syscallRowFacts (syscallInstruction f call)).memPulls.map Prod.fst) := by
      rw [input]
      exact List.mem_map_of_mem (f := Prod.fst) pulled
    rw [MixedMemoryHistory.syscall_pulls f call phase] at mem
    obtain ⟨a, operand, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp mem)
    have same := congrArg Prod.snd eq
    change AccessSupply.atClock _ _ = r at same
    rw [← same]
    have incoming := (syscallInstruction_stateMessages (p := SP1Prime) f call).1
    change SyscallInstrsChip.statePulledMessage (syscallInstruction f call) = _ at incoming
    rw [← input, incoming]
    exact Counted.bounded_compiled_entry a.pulledEntry call.clock (operand_bound run routed placed operand) fits

end SP1Clean.Export.WriteSourceRegistry
