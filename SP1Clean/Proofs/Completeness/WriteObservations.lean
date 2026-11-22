import SP1Clean.Proofs.Completeness.MixedAccessFrontier
import SP1Clean.FormalModel.ShardPreservation
import SP1Clean.FormalModel.Contracts.HostCall
import SP1Clean.FormalModel.Contracts.HostRamRead
import SP1Clean.Semantics.Execution.ExecutionAccess
import SP1Clean.Soundness.Grounding.MemoryCell

/-! # Reconstructing released WRITE observations from the genuine execution prefix

SP1 v6.10.0's `minimal/write.rs` reads x12 directly and calls `mr_slice_no_trace`. The
aligned words have no WRITE-generated Memory timestamps. This compiler uses the actual Sail
prefix state, including for the extra observation of an unaligned empty buffer. Host hooks
use the existing request-indexed reply transcript described in `docs/write-observations.md`.
-/

namespace SP1Clean.TraceGen.WriteObservations

open Semantics Machine FormalModel.Shard Soundness.Target

/-- Number of aligned words passed to the released untraced memory-slice accessor. -/
def wordCount (address length : ℕ) : ℕ := (address % 8 + length + 7) / 8

/-- Canonical word position in the untraced slice. -/
def cell (address index : ℕ) : RamCell := BitVec.ofNat 61 (address / 8 + index)

/-- The released `u64::to_le_bytes` stream for a single observed word. -/
private def bytesOf (word : BitVec 64) : Bytes := (Soundness.wordBytes word).toList

/-- Observe every aligned word in order in the complete source state. All reads are proved
present at an actual WRITE, including bytes beyond the selected payload in its boundary words. -/
def words (source : SailState) (address length : ℕ) : List (BitVec 64) :=
  (List.range (wordCount address length)).map fun i => (ramWord64? source (cell address i).baseAddr).getD 0

/-- Reproduce the released flat little-endian slice, dropping head bytes and taking the exact x12 length. -/
def payload (buffer : List (BitVec 64)) (address length : ℕ) : Bytes :=
  ((buffer.flatMap bytesOf).drop (address % 8)).take length

theorem words_length (source : SailState) (address length : ℕ) :
    (words source address length).length = wordCount address length := by simp [words]

/-- An unaligned zero-length request still observes one full word and returns no bytes. -/
theorem empty_buffer (source : SailState) (address : ℕ) :
    (words source address 0).length = (if address % 8 = 0 then 0 else 1) ∧
      payload (words source address 0) address 0 = [] := by
  rw [words_length]
  refine ⟨?_, rfl⟩
  unfold wordCount
  split <;> omega

private theorem cell_window {address length index : ℕ} (upper : address + length ≤ 2 ^ 48)
    (inside : index < wordCount address length) :
    (cell address index).baseAddr.toNat = (address / 8 + index) * 8 ∧
      (address / 8 + index) * 8 + 8 ≤ 2 ^ 48 := by
  unfold wordCount at inside
  have key : address / 8 + index < 2 ^ 61 := by omega
  have window : (address / 8 + index) * 8 + 8 ≤ 2 ^ 48 := by omega
  refine ⟨?_, window⟩
  simp only [cell, RamCell.baseAddr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt key, Nat.mod_eq_of_lt (by omega :
    (address / 8 + index) * 8 < 2 ^ 64)]

private theorem stream_length (buffer : List (BitVec 64)) :
    (buffer.flatMap bytesOf).length = 8 * buffer.length := by
  induction buffer with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.flatMap_cons, List.length_append, bytesOf, Vector.length_toList, ih, List.length_cons]
    omega

private theorem stream_byte (buffer : List (BitVec 64)) {i : ℕ} (inside : i < buffer.length) (slot : Fin 8) :
    (buffer.flatMap bytesOf)[i * 8 + slot.val]? = some (Soundness.wordBytes buffer[i])[slot.val] := by
  induction buffer generalizing i with
  | nil => simp at inside
  | cons word tail ih =>
    cases i with
    | zero =>
      simp only [List.flatMap_cons, Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
      rw [List.getElem?_append_left (show slot.val < (bytesOf word).length from by simp [bytesOf])]
      exact List.getElem?_eq_getElem _
    | succ i =>
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      rw [List.getElem?_append_right (show (bytesOf word).length ≤ (i+1)*8+slot.val by simp [bytesOf]; omega)]
      have shorter : i < tail.length := by simpa using inside
      simpa only [bytesOf, Vector.length_toList, show (i+1)*8+slot.val-8 = i*8+slot.val by omega] using
        ih shorter

/-- Pack the actual full-word observations without introducing a timestamp transition, and recover
the very byte list returned by the existing host interpreter. -/
theorem observe {source : SailState} {address length : ℕ} {expected : Bytes}
    (upper : address + length ≤ 2 ^ 48)
    (available : ∀ a < 2 ^ 48, (source.mem.get? a).isSome)
    (size : expected.length = length) (observed : (HostReadContext.ofSail source).ObservesBytes address expected) :
    (∀ i, (inside : i < wordCount address length) →
      ramWord64? source (cell address i).baseAddr = (words source address length)[i]?) ∧
      payload (words source address length) address length = expected := by
  let buffer := words source address length
  have count : buffer.length = wordCount address length := words_length ..
  have read (i : ℕ) (inside : i < wordCount address length) :
      ramWord64? source (cell address i).baseAddr = buffer[i]? := by
    have ⟨key, bound⟩ := cell_window upper inside
    have present := ramWord64?_isSome_of_present source (cell address i).baseAddr (by
      intro j small
      apply available
      rw [key]
      omega)
    change _ = ((List.range _).map _)[i]?
    rw [List.getElem?_map, List.getElem?_range inside]
    cases h : ramWord64? source (cell address i).baseAddr <;> simp_all
  refine ⟨read, ?_⟩
  have enough : address % 8 + length ≤ 8 * buffer.length := by rw [count]; unfold wordCount; omega
  have full : (payload buffer address length).length = length := by
    simp only [payload, List.length_take, List.length_drop, stream_length]
    omega
  apply List.ext_getElem (full.trans size.symm)
  intro n atPayload atExpected
  have inside : n < length := by omega
  let i := (address % 8 + n) / 8
  let slot : Fin 8 := ⟨(address % 8 + n) % 8, Nat.mod_lt _ (by decide)⟩
  have inWords : i < wordCount address length := by unfold i wordCount; omega
  have atWord : i < buffer.length := count ▸ inWords
  have ground := read i inWords
  rw [List.getElem?_eq_getElem atWord] at ground
  have seen := Soundness.byte_of_ramWord64?_eq_some ground slot
  have ⟨key, _⟩ := cell_window upper inWords
  have off : i * 8 + slot.val = address % 8 + n := by dsimp [i, slot]; omega
  have whereByte : (address / 8 + i) * 8 + slot.val = address + n := by omega
  rw [key, whereByte] at seen
  have matching := Option.some.inj (seen.symm.trans (observed n atExpected))
  apply Option.some.inj
  rw [← List.getElem?_eq_getElem atPayload]
  change ((buffer.flatMap bytesOf).drop (address % 8) |>.take length)[n]? = _
  rw [List.getElem?_take_of_lt inside, List.getElem?_drop, ← off, stream_byte buffer atWord slot]
  exact congrArg some matching

/-- Released WRITE leaves the guest RAM and x12 Memory chronology unchanged.
The three ECALL operand records remain in the genuine prefix schedule. -/
theorem frontier_frame {call : CoreSyscallEvent} (code : call.rawCode = SyscallKind.write.code)
    (prior : AccessFrontier) (clock : ℕ) :
    syscallFrontier prior clock call (.reg 12) = prior (.reg 12) ∧
      ∀ address, syscallFrontier prior clock call (.ram address) = prior (.ram address) := by
  constructor
  · apply advancePlan_of_not_touched
    intro touch occurs
    simp only [syscallRegisterPlan, List.mem_cons, List.not_mem_nil, or_false] at occurs
    rcases occurs with rfl | rfl | rfl <;> simp
  · intro address
    simp [syscallFrontier, code, show SyscallKind.write.code ≠ SyscallKind.hintRead.code by decide]

/-- Recover x12 and the untraced word slice from a genuine replay state. This procedure
fails if any observed word is missing, including an unselected part of a boundary word. -/
def read? (source : SailState) (call : CoreSyscallEvent) : Option (BitVec 64 × List (BitVec 64)) := do
  if call.rawCode ≠ SyscallKind.write.code then none else
  let length ← source.get_reg? 12
  if 2 ^ 16 ≤ call.arg2.toNat ∧ call.arg2.toNat + length.toNat ≤ 2 ^ 48 then
    let buffer ← (List.range (wordCount call.arg2.toNat length.toNat)).mapM fun i =>
      ramWord64? source (cell call.arg2.toNat i).baseAddr
    return (length, buffer)
  else none

private theorem map_words_iff {source : SailState} {address length : ℕ} {buffer : List (BitVec 64)} :
    (List.range (wordCount address length)).mapM (fun i => ramWord64? source (cell address i).baseAddr) = some buffer ↔
      buffer.length = wordCount address length ∧
        ∀ i, i < buffer.length → ramWord64? source (cell address i).baseAddr = buffer[i]? := by
  rw [List.mapM_option_eq_some_iff, List.forall₂_iff_get]
  constructor
  · rintro ⟨same, each⟩
    have size : buffer.length = wordCount address length := by simpa using same.symm
    refine ⟨size, ?_⟩
    intro i inside
    rw [List.getElem?_eq_getElem inside]
    simpa only [List.get_eq_getElem, List.getElem_range] using each i (by simpa only [same] using inside) inside
  · rintro ⟨size, each⟩
    refine ⟨by simp [size], ?_⟩
    intro i _ inside
    simpa only [List.get_eq_getElem, List.getElem_range, List.getElem?_eq_getElem inside] using each i inside

/-- The observer succeeds exactly on the released WRITE code, actual x12 value, bounded span
and complete ordered words of the given Sail state. Any replacement length or word fails. -/
theorem read?_eq_some_iff {source : SailState} {call : CoreSyscallEvent} {length : BitVec 64}
    {buffer : List (BitVec 64)} :
    read? source call = some (length, buffer) ↔ call.rawCode = SyscallKind.write.code ∧
      source.get_reg? 12 = some length ∧ 2 ^ 16 ≤ call.arg2.toNat ∧ call.arg2.toNat + length.toNat ≤ 2 ^ 48 ∧
      buffer.length = wordCount call.arg2.toNat length.toNat ∧
        ∀ i, i < buffer.length → ramWord64? source (cell call.arg2.toNat i).baseAddr = buffer[i]? := by
  constructor
  · intro ran
    unfold read? at ran
    split at ran
    · contradiction
    rename_i sameCode
    simp only [bind, Option.bind_eq_some_iff] at ran
    obtain ⟨actual, x12, rest⟩ := ran
    split at rest
    · rename_i bounds
      simp only [Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at rest
      obtain ⟨observed, packet, rfl, rfl⟩ := rest
      exact ⟨of_not_not sameCode, x12, bounds.1, bounds.2, map_words_iff.mp packet⟩
    · contradiction
  · rintro ⟨code, x12, lower, upper, words⟩
    have full := map_words_iff.mpr words
    simp only [read?, code, ne_eq, not_true_eq_false, ↓reduceIte, x12, bind, Option.bind_some,
      lower, upper, and_self, full, pure]

/-- Consequences of direct hint and hook dispatch. The hook clause consumes precisely one
authenticated request/reply pair from the declared host input and preserves reply order. -/
def HintEffects (before after : HostState) (descriptor : BitVec 64) (bytes : Bytes) : Prop :=
  (descriptor.setWidth 32 = 14 → after = {before with io := before.io.writeHint bytes}) ∧
    (descriptor.setWidth 32 ∈ hookDescriptors →
      ∃ returned rest, before.replies = ⟨⟨descriptor.setWidth 32, bytes⟩, returned⟩ :: rest ∧
        after = { before with
          io := {before.io with hints := returned ++ before.io.hints}
          replies := rest
          requests := before.requests ++ [⟨descriptor.setWidth 32, bytes⟩] })

private theorem hint_effects {before after : HostState} {descriptor : BitVec 64} {bytes : Bytes}
    (success : before.writeOutput descriptor bytes = some after) : HintEffects before after descriptor bytes := by
  constructor
  · intro direct
    have neither : descriptor ≠ 1 ∧ descriptor ≠ 2 := by
      constructor <;> rintro rfl <;> contradiction
    rw [HostState.writeOutput, ite_eq_right neither.1, ite_eq_right neither.2, direct] at success
    exact (Option.some.inj success).symm
  · intro hooked
    have notFd (fd : BitVec 32) (unused : fd ∉ hookDescriptors) : descriptor.setWidth 32 ≠ fd :=
      fun h => unused (h ▸ hooked)
    have n1 : descriptor ≠ 1 := fun h => notFd 1 (by decide) (h ▸ rfl)
    have n2 : descriptor ≠ 2 := fun h => notFd 2 (by decide) (h ▸ rfl)
    simp only [HostState.writeOutput, ite_eq_right n1, ite_eq_right n2, ite_eq_right (notFd 13 (by decide)),
      ite_eq_right (notFd 14 (by decide)), ite_eq_left hooked, bind, Option.bind_eq_some_iff] at success
    obtain ⟨⟨io, remaining⟩, applied, eq⟩ := success
    obtain ⟨returned, replies, ioEq⟩ := (HostIO.applyHook_eq_some_iff ..).mp applied
    exact ⟨returned, remaining, replies, (Option.some.inj eq).symm.trans (by rw [ioEq])⟩

/-- Every actual WRITE cut constructs the exact released observation packet and descriptor effect.
The x12 length and every consumed word are read from the same replayed Sail state as the ECALL.
No host write or predecessor timestamp is synthesized for the untraced observations. -/
theorem of_admissibleExecution {limits : ResourceLimits} {p : ℕ} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events)
    {cut : ℕ} {call : CoreSyscallEvent} (atEvent : events[cut]? = some (.syscall call))
    (code : call.rawCode = SyscallKind.write.code) :
    let hostPolicy := policy p image
    ∃ current next frontier length buffer,
      mixedAccessPrefix hostPolicy image.program source.realize events cut = some (current, frontier) ∧
      mixedAccessPrefix hostPolicy image.program source.realize events (cut + 1) =
        some (next, syscallFrontier frontier current.clock call) ∧
      current.sail.get_reg? 12 = some length ∧ read? current.sail call = some (length, buffer) ∧
      buffer.length = wordCount call.arg2.toNat length.toNat ∧
      (∀ i, i < buffer.length → ramWord64? current.sail (cell call.arg2.toNat i).baseAddr = buffer[i]?) ∧
      next.sail.mem = current.sail.mem ∧
      syscallFrontier frontier current.clock call (.reg 12) = frontier (.reg 12) ∧
      (∀ a, syscallFrontier frontier current.clock call (.ram a) = frontier (.ram a)) ∧
      let data := payload buffer call.arg2.toNat length.toNat
      current.host.writeOutput call.arg1 data = some next.host ∧ HintEffects current.host next.host call.arg1 data := by
  obtain ⟨current, frontier, next, replay, built, step, nextBuilt, _⟩ := admissibleExecution_syscall_from_prefix execution atEvent
  have ⟨sameRegister, sameMemory⟩ := frontier_frame code frontier current.clock
  cases step with
  | syscall success =>
    obtain ⟨pc, exec, _, _, ran, hostEq, sailEq, eventEq⟩ := HostState.step_observations success
    subst call
    have kind : exec.kind = .write := SyscallKind.code_injective code
    have effect := ((HostState.run_eq_some_iff ..).mp ran).2.2.2.2.2
    rw [kind] at effect
    obtain ⟨length, bytes, host, x12, read, dispatched, hostChange⟩ := (HostState.execute_write_iff ..).mp effect
    obtain ⟨lower, upper, size, seen⟩ := (HostReadContext.readGuest?_eq_some_iff ..).mp read
    have ⟨reads, data⟩ := observe upper (execution.1.memory_present_prefix replay) size seen
    let buffer := words current.sail exec.arg2.toNat length.toNat
    have bufferSize : buffer.length = wordCount exec.arg2.toNat length.toNat := words_length ..
    have nextHost := hostEq.trans (congrArg HostEffect.state hostChange)
    have dataRead (i : ℕ) (inside : i < buffer.length) := reads i (bufferSize ▸ inside)
    have packet := read?_eq_some_iff.mpr ⟨code, x12, lower, upper, bufferSize, dataRead⟩
    refine ⟨current, _, frontier, length, buffer, built, nextBuilt, x12, packet, bufferSize,
      dataRead, ?_, sameRegister, sameMemory, ?_⟩
    · simp only [sailEq, HostExecution.apply, HostEffect.applyMemory, hostChange]
    · change current.host.writeOutput exec.arg1 (payload buffer exec.arg2.toNat length.toNat) = _ ∧ _
      have both : current.host.writeOutput exec.arg1 (payload buffer exec.arg2.toNat length.toNat) = some _ :=
        data ▸ dispatched
      have agrees := both.trans (congrArg some nextHost.symm)
      exact ⟨agrees, hint_effects agrees⟩

/-- The native wrapper's enabled x12 receiver strictly advances time. It cannot preserve
the predecessor timestamp of a released WRITE observation. -/
theorem traced_x12_incompatible {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)] {input : HostCallChip.Inputs (ZMod p)}
    (valid : HostCallChip.Spec input) (active : input.instruction.is_real = 1)
    (code : input.instruction.op_a_memory.prev_value = HostCallChip.writeWord) :
    let extra := input.read (HostCallChip.writeFlag input.instruction.op_a_memory.prev_value)
    MemoryMsg.timeNat extra.prior < MemoryMsg.timeNat extra.pushed := by
  exact (valid.2 (by simp [HostCallChip.Inputs.read, HostCallChip.writeFlag, active, code])).2.2

/-- The traced native host RAM read also requires strictly increasing Memory time. -/
theorem traced_ram_incompatible {p : ℕ} [Fact p.Prime] {input : HostRamReadChip.Inputs (ZMod p)}
    (valid : HostRamReadChip.Spec input) :
    MemoryMsg.timeNat input.ram.prior < MemoryMsg.timeNat input.ram.pushed :=
  valid.1.2.2.2.2.2.2.2.2.1

end SP1Clean.TraceGen.WriteObservations
