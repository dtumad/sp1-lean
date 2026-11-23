import SP1Clean.Proofs.Completeness.WriteObservations
import SP1Clean.Soundness.WriteVersionIntervals

/-! # Checking the untraced WRITE operands against a physical prefix

Each presented length and RAM word has four field limbs. The checker compares those limbs with
the held values from the incoming snapshot and the ordered physical pushes before the call.
Its result consumes neither a guest Memory record nor any observation allowance.
-/

namespace SP1Clean.TraceGen.WriteObservations

open Semantics Machine Soundness.Target Soundness.WriteObservationHistory

variable {p : ℕ} [Fact p.Prime]

/-- Check the actual raw four-limb operands for the released read-only WRITE. Only the supplied word count controls
the number of RAM probes, even when a claimed x12 length disagrees with that count. -/
def checkPacket (snapshot : MemorySnapshot) (rows : List (RowFacts p)) (cut : ℕ) (call : CoreSyscallEvent)
    (length : Word (ZMod p)) (buffer : List (Word (ZMod p))) : Bool :=
  let address := call.arg2.toNat
  let size := length.toBitVec64.toNat
  decide (call.rawCode = SyscallKind.write.code ∧
    length = wordAt snapshot rows cut (.reg 12) ∧ 2 ^ 16 ≤ address ∧ address + size ≤ 2 ^ 48 ∧
    buffer.length = wordCount address size ∧
    buffer = (List.range buffer.length).map (fun i => wordAt snapshot rows cut (.ram (cell address i))))

/-- The released packet checker accepts exactly when x12 and every *indexed* buffer
word have an authentic physical interval at this cut. No register or RAM touch is added. -/
theorem checkPacket_iff_versions {snapshot : MemorySnapshot} {rows : List (RowFacts p)} {cut : ℕ}
    (within : cut ≤ rows.length) (call : CoreSyscallEvent) (length : Word (ZMod p))
    (buffer : List (Word (ZMod p))) :
    checkPacket snapshot rows cut call length buffer = true ↔
      call.rawCode = SyscallKind.write.code ∧ VersionedWord snapshot rows cut (.reg 12) length ∧
      2 ^ 16 ≤ call.arg2.toNat ∧ call.arg2.toNat + length.toBitVec64.toNat ≤ 2 ^ 48 ∧
      buffer.length = wordCount call.arg2.toNat length.toBitVec64.toNat ∧
      ∀ i (inside : i < buffer.length),
        VersionedWord snapshot rows cut (.ram (cell call.arg2.toNat i)) buffer[i] := by
  simp only [checkPacket, decide_eq_true_eq, versionedWord_iff within]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro same i inside
    simpa only [List.getElem?_map, List.getElem?_range inside, Option.map_some,
      List.getElem?_eq_getElem inside, Option.some.injEq] using congrArg (·[i]?) same
  · intro each
    exact List.ext_getElem (by simp) fun i inside _ => by simpa using each i inside

private theorem cell_busAddress {address length index : ℕ} (upper : address + length ≤ 2 ^ 48)
    (inside : index < wordCount address length) : (MemLoc.ram (cell address index)).busAddress < 2 ^ 48 := by
  unfold wordCount at inside
  have key : address / 8 + index < 2 ^ 61 := by omega
  simp only [MemLoc.busAddress, cell, BitVec.toNat_ofNat, Nat.mod_eq_of_lt key]
  omega

/-- Soundness and completeness for arbitrary presented limbs. Success identifies x12 and every
aligned word in order with the same predecessor state, and rejects noncanonical 64-bit encodings. -/
theorem checkPacket_iff {snapshot : MemorySnapshot} {rows : List (RowFacts p)} {cut : ℕ}
    {current : SailState} (held : ∀ loc : MemLoc, loc.busAddress < 2 ^ 48 →
      let word := wordAt snapshot rows cut loc
      word.isU64 ∧ locContent current loc = some word.toBitVec64)
    (call : CoreSyscallEvent) (length : Word (ZMod p)) (buffer : List (Word (ZMod p))) :
    checkPacket snapshot rows cut call length buffer = true ↔
      length.isU64 ∧ (∀ word ∈ buffer, word.isU64) ∧
      read? current call = some (length.toBitVec64, buffer.map Word.toBitVec64) := by
  have reg := held (.reg 12) (by decide)
  simp only [checkPacket, decide_eq_true_eq, read?_eq_some_iff, List.length_map]
  constructor
  · rintro ⟨code, sameLength, lower, upper, count, sameWords⟩
    have atWord (i : ℕ) (inside : i < buffer.length) :
        buffer[i] = wordAt snapshot rows cut (.ram (cell call.arg2.toNat i)) := by
      simpa only [List.getElem?_map, List.getElem?_range inside, Option.map_some,
        List.getElem?_eq_getElem inside, Option.some.injEq] using congrArg (·[i]?) sameWords
    refine ⟨sameLength ▸ reg.1, ?_, code, sameLength ▸ reg.2, lower, upper, count, ?_⟩
    · intro word member
      obtain ⟨i, inside, rfl⟩ := List.mem_iff_getElem.mp member
      rw [atWord i inside]
      exact (held _ (cell_busAddress upper (count ▸ inside))).1
    · intro i inside
      rw [List.getElem?_map, List.getElem?_eq_getElem inside, Option.map_some, atWord i inside]
      exact (held _ (cell_busAddress upper (count ▸ inside))).2
  · rintro ⟨lengthBound, wordBounds, code, seenLength, lower, upper, count, each⟩
    refine ⟨code, Word.eq_of_toBitVec64_eq lengthBound reg.1 (Option.some.inj (seenLength.symm.trans reg.2)),
      lower, upper, count, List.ext_getElem (by simp) ?_⟩
    intro i inside _
    simp only [List.getElem_map, List.getElem_range]
    have observed := each i inside
    rw [List.getElem?_map, List.getElem?_eq_getElem inside, Option.map_some] at observed
    have actual := held _ (cell_busAddress upper (count ▸ inside))
    exact Word.eq_of_toBitVec64_eq (wordBounds _ (List.getElem_mem inside)) actual.1
      (Option.some.inj (observed.symm.trans actual.2))

/-- Generate the exact four-limb operands directly from the physical cut. A genuine WRITE operates
on the complete aligned words even when its byte payload is empty. -/
def makePacket? (snapshot : MemorySnapshot) (rows : List (RowFacts p)) (cut : ℕ) (call : CoreSyscallEvent) :
    Option (Word (ZMod p) × List (Word (ZMod p))) :=
  let length := wordAt snapshot rows cut (.reg 12)
  let address := call.arg2.toNat
  let size := length.toBitVec64.toNat
  if call.rawCode = SyscallKind.write.code ∧ 2 ^ 16 ≤ address ∧ address + size ≤ 2 ^ 48 then
    some (length, (List.range (wordCount address size)).map (fun i => wordAt snapshot rows cut (.ram (cell address i))))
  else none

/-- The checker and honest generator agree on arbitrary physical input. Reusing a packet does
not consume any guest interaction or change the physical prefix. -/
theorem checkPacket_iff_makePacket {snapshot : MemorySnapshot} {rows : List (RowFacts p)} {cut : ℕ}
    (call : CoreSyscallEvent) (length : Word (ZMod p)) (buffer : List (Word (ZMod p))) :
    checkPacket snapshot rows cut call length buffer = true ↔
      makePacket? snapshot rows cut call = some (length, buffer) := by
  simp only [checkPacket, decide_eq_true_eq]
  constructor
  · rintro ⟨code, rfl, lower, upper, size, words⟩
    simp only [makePacket?, code, lower, upper, and_self, ↓reduceIte, Option.some.injEq,
      Prod.mk.injEq, true_and]
    simpa only [← size] using words.symm
  · dsimp only [makePacket?]
    split
    · rintro ⟨⟩
      rename_i bounds
      exact ⟨bounds.1, rfl, bounds.2.1, bounds.2.2, by simp, by simp⟩
    · intro impossible
      contradiction

/-- Check the three ECALL argument registers from the same prefix as the untraced x12 and
RAM observations. Clock, instruction fetch, and the outgoing result belong to the CPU row. -/
def checkWriteInputs (snapshot : MemorySnapshot) (rows : List (RowFacts p)) (cut : ℕ) (call : CoreSyscallEvent)
    (length : Word (ZMod p)) (buffer : List (Word (ZMod p))) : Bool :=
  decide (call.rawCode = (wordAt snapshot rows cut (.reg 5)).toBitVec64 ∧
    call.arg1 = (wordAt snapshot rows cut (.reg 10)).toBitVec64 ∧
    call.arg2 = (wordAt snapshot rows cut (.reg 11)).toBitVec64) &&
      checkPacket snapshot rows cut call length buffer

/-- The claimed code, descriptor, address, length, and complete buffer all refer to one state.
Repeated checks use the same physical evidence and may overlap in any number of words. -/
theorem checkWriteInputs_iff {snapshot : MemorySnapshot} {rows : List (RowFacts p)} {cut : ℕ}
    {current : SailState} (held : ∀ loc : MemLoc, loc.busAddress < 2 ^ 48 →
      let word := wordAt snapshot rows cut loc
      word.isU64 ∧ locContent current loc = some word.toBitVec64)
    (call : CoreSyscallEvent) (length : Word (ZMod p)) (buffer : List (Word (ZMod p))) :
    checkWriteInputs snapshot rows cut call length buffer = true ↔
      (current.get_reg? 5 = some call.rawCode ∧ current.get_reg? 10 = some call.arg1 ∧
        current.get_reg? 11 = some call.arg2) ∧ length.isU64 ∧ (∀ word ∈ buffer, word.isU64) ∧
        read? current call = some (length.toBitVec64, buffer.map Word.toBitVec64) := by
  have reg (i : BitVec 5) : current.get_reg? i = some (wordAt snapshot rows cut (.reg i)).toBitVec64 :=
    (held (.reg i) (by change i.toNat < 2 ^ 48; have := i.isLt; omega)).2
  rw [checkWriteInputs, Bool.and_eq_true, decide_eq_true_eq, checkPacket_iff held, reg 5, reg 10, reg 11]
  simp only [Option.some.injEq, eq_comm]

end SP1Clean.TraceGen.WriteObservations
