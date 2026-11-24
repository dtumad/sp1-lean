import SP1Clean.Soundness.WriteBufferCoverage
import SP1Clean.Proofs.Completeness.WriteObservations

/-! # Constructing the complete physical WRITE word walk

A successful native WRITE produces one span and an ordered list of word rows from
its actual incoming Sail observations. No extra RAM access or guest event is introduced.
-/

namespace SP1Clean.WriteBuffer

open Soundness Soundness.Target Semantics Machine TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Build one row per word, preserving source order and all repeated values. -/
def wordSteps (clock : fields 3 (ZMod p)) (first : ℕ) (buffer : List (Word (ZMod p))) : List (Step (ZMod p)) :=
  buffer.zipIdx.map fun (word, i) => Step.populate clock (first + i) word

omit [Fact (2 ^ 17 < p)] in
private theorem wordSteps_cons (clock : fields 3 (ZMod p)) (first : ℕ) (x : Word (ZMod p)) (xs) :
    wordSteps clock first (x :: xs) = Step.populate clock first x :: wordSteps clock (first + 1) xs := by
  simp [wordSteps, List.zipIdx_cons, List.zipIdx_succ, Function.comp_def, Nat.add_assoc, Nat.add_comm 1]

omit [Fact (2 ^ 17 < p)] in
/-- The actual receipt at position `i` binds all address, time, and word limbs. -/
theorem wordSteps_getElem? (clock : fields 3 (ZMod p)) (first : ℕ) (words : List (Word (ZMod p))) (index : ℕ) :
    (wordSteps clock first words)[index]? = words[index]?.map (Step.populate clock (first + index)) := by
  induction words generalizing first index with
  | nil => simp [wordSteps]
  | cons word rest ih =>
    rw [wordSteps_cons]
    cases index with
    | zero => simp
    | succ i => simpa [Nat.add_assoc, Nat.add_comm 1] using ih (first + 1) i

omit [Fact (2 ^ 17 < p)] in
private theorem steps_walk (clock : fields 3 (ZMod p)) (first : ℕ) (words : List (Word (ZMod p))) :
    Walk.IsWalk (fun r : Step (ZMod p) => (r.source, r.target)) ⟨clock, Address.ofNat first⟩
      ⟨clock, Address.ofNat (first + words.length)⟩ (wordSteps clock first words) := by
  induction words generalizing first with
  | nil => simp [wordSteps, Walk.IsWalk]
  | cons word rest ih =>
    rw [wordSteps_cons]
    refine ⟨rfl, ?_⟩
    convert ih (first + 1) using 1 <;> simp [Step.populate, Step.target, Nat.add_assoc, Nat.add_comm 1]

private theorem all_honest (clock : fields 3 (ZMod p)) (first : ℕ) (words : List (Word (ZMod p)))
    (bound : first + words.length ≤ 2 ^ 45) : ∀ row ∈ wordSteps clock first words, row.Honest := by
  induction words generalizing first with
  | nil => simp [wordSteps]
  | cons x xs ih =>
    rw [wordSteps_cons]
    simp only [List.length_cons] at bound
    intro row member
    rcases List.mem_cons.mp member with rfl | later
    · exact Step.populate_honest _ _ _ (by omega)
    · exact ih _ (by omega) _ later

/-- Supply the physical span row and every word row for a successfully observed complete
WRITE packet, including the empty aligned case at one-past guest memory. -/
theorem rows_of_packet (h : WritePacket.Header (ZMod p))
    (address : h.address.isU64) (length : h.length.isU64)
    (lower : 2 ^ 16 ≤ h.address.toNat) (bound : h.address.toNat + h.length.toNat ≤ 2 ^ 48)
    (buffer : List (Word (ZMod p))) (count : buffer.length = WriteObservations.wordCount h.address.toNat h.length.toNat) :
    let span := Span.populate h
    let words := wordSteps h.clock (h.address.toNat / 8) buffer
    span.Honest ∧ (∀ row ∈ words, row.Honest) ∧
      Walk.IsWalk (fun r : Step (ZMod p) => (r.source, r.target)) span.source span.target words ∧
      ∀ i, (words[i]?).map Step.read = (buffer[i]?).map (fun value =>
        ⟨Address.ofNat (8 * (h.address.toNat / 8 + i)), h.clock, value⟩) := by
  have honest := Span.populate_honest h address length lower bound
  obtain ⟨_, _, _, _, _, _, first, last, lo, hi⟩ := honest.1
  change Address.toNat (Span.populate h).first = h.address.toNat / 8 at lo
  change Address.toNat (Span.populate h).stop = (h.address.toNat + h.length.toNat + 7) / 8 at hi
  rw [WriteObservations.wordCount] at count
  have stop : (h.address.toNat + h.length.toNat + 7) / 8 = h.address.toNat / 8 + buffer.length := by omega
  refine ⟨honest, all_honest _ _ _ (by omega), ?_, ?_⟩
  · have a : (Span.populate h).source = ⟨h.clock, Address.ofNat (h.address.toNat / 8)⟩ := by
      change Cursor.mk h.clock (Span.populate h).first = _
      rw [← Address.ofNat_toNat first, lo]
    have b : (Span.populate h).target = ⟨h.clock, Address.ofNat (h.address.toNat / 8 + buffer.length)⟩ := by
      change Cursor.mk h.clock (Span.populate h).stop = _
      rw [← Address.ofNat_toNat last, hi, stop]
    rw [a, b]
    exact steps_walk _ _ _
  · intro i
    rw [wordSteps_getElem?, Option.map_map]
    rfl

/-- Actual released ECALL operands embedded in the header and the native source words. -/
def headerOfCall (clock : ℕ) (call : CoreSyscallEvent) (length : BitVec 64) : WritePacket.Header (ZMod p) :=
  ⟨Address.ofNat clock, bitVecToWord call.arg1, bitVecToWord call.arg2, bitVecToWord length⟩

/-- From a successful `read?`, construct honest span/word rows and an exhaustive physical
walk without any premise about compiler readiness or the values of the reads. -/
theorem rows_of_read {before : SailState} {call : CoreSyscallEvent} {length : BitVec 64} {buffer : List (BitVec 64)}
    (observed : WriteObservations.read? before call = some (length, buffer)) (clock : ℕ) :
    let h := headerOfCall (p := p) clock call length
    let span := Span.populate h
    let words := wordSteps h.clock (call.arg2.toNat / 8) (buffer.map bitVecToWord)
    span.Honest ∧ (∀ row ∈ words, row.Honest) ∧
      Walk.IsWalk (fun r : Step (ZMod p) => (r.source, r.target)) span.source span.target words ∧
      ∀ i, (words[i]?).map Step.read = (buffer[i]?).map (fun value =>
        ⟨Address.ofNat (8 * (call.arg2.toNat / 8 + i)), h.clock, bitVecToWord value⟩) := by
  obtain ⟨_, _, lo, hi, n, _⟩ := WriteObservations.read?_eq_some_iff.mp observed
  have vals (word : BitVec 64) : (bitVecToWord (p := p) word).toNat = word.toNat := by
    rw [← Word.toBitVec64_toNat (isU64_bitVecToWord _), toBitVec64_bitVecToWord]
  have rows := rows_of_packet (headerOfCall (p := p) clock call length)
    (isU64_bitVecToWord _) (isU64_bitVecToWord _) (by simpa [headerOfCall, vals] using lo)
    (by simpa [headerOfCall, vals] using hi) (buffer.map bitVecToWord)
    (by simpa [headerOfCall, vals] using n)
  simpa only [headerOfCall, vals, List.getElem?_map, Option.map_map, Function.comp_def] using rows

/-- Every real WRITE in an admissible mixed execution builds the exact consecutive word
rows at its own incoming clock, using the operand observations of that same execution. -/
theorem rows_of_admissibleExecution {limits : ResourceLimits} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : FormalModel.Shard.AdmissibleExecution limits p image source target events)
    {cut : ℕ} {call : CoreSyscallEvent} (atEvent : events[cut]? = some (.syscall call))
    (write : call.rawCode = SyscallKind.write.code) :
    ∃ current frontier len buffer,
      mixedAccessPrefix (FormalModel.Shard.policy p image) image.program source.realize events cut = some (current, frontier) ∧
      WriteObservations.read? current.sail call = some (len, buffer) ∧
      let header := headerOfCall (p := p) current.clock call len
      let span := Span.populate header
      let words := wordSteps header.clock (call.arg2.toNat / 8) (buffer.map bitVecToWord)
      span.Honest ∧ (∀ row ∈ words, row.Honest) ∧
        Walk.IsWalk (fun r : Step (ZMod p) => (r.source, r.target)) span.source span.target words ∧
        ∀ i, (words[i]?).map Step.read = (buffer[i]?).map (fun value =>
          ⟨Address.ofNat (8 * (call.arg2.toNat / 8 + i)), header.clock, bitVecToWord value⟩) := by
  obtain ⟨current, _, frontier, len, buffer, reached, _, _, observed, _⟩ :=
    WriteObservations.of_admissibleExecution run atEvent write
  exact ⟨current, frontier, len, buffer, reached, observed, rows_of_read observed current.clock⟩

end SP1Clean.WriteBuffer
