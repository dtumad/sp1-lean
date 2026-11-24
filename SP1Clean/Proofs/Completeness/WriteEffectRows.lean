import SP1Clean.Proofs.Operations.WriteEffects
import SP1Clean.Proofs.Completeness.WriteObservations
import SP1Clean.Semantics.Host.WriteEffects

/-! # Constructing the exact WRITE effect from one execution cut

The actual x12 and guest words determine the rows and all selected little-endian bytes. Both
partial boundary words are retained in the physical list. The host effect consumes the same
ordered payload and, for a hook, the same supplied reply as the released dispatcher.
-/

namespace SP1Clean.WriteEffects
open Semantics Soundness Soundness.Target Machine FormalModel.Shard TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Extract the sequential WRITE byte slice from the physically decoded octets. -/
def payload (rows : List (Octets (ZMod p))) (address length : Nat) : Bytes :=
  ((rows.flatMap fun r => (r.bytes.map fun b => BitVec.ofNat 8 b.val).toList).drop (address % 8)).take length

omit [Fact (2 ^ 17 < p)] in
private theorem word_bytes (r : WordRow (ZMod p)) (valid : r.Valid) :
    ((r.octets (256 : ZMod p)⁻¹).bytes.map fun b => BitVec.ofNat 8 b.val) = wordBytes r.read.value.toBitVec64 := by
  apply Vector.ext
  intro i hi
  have nth := (valid ⟨i, hi⟩).2
  simp only [Vector.getElem_map]
  rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 by omega) with h|h|h|h|h|h|h|h <;> subst i <;> exact nth

omit [Fact (2 ^ 17 < p)] in
/-- Word order is preserved and every active word contributes all its checked lanes before trimming. -/
theorem payload_eq (rows : List (WordRow (ZMod p))) (address length : Nat) (checked : ∀ r ∈ rows, r.Valid) :
    payload (rows.map (WordRow.octets (256 : ZMod p)⁻¹)) address length =
      WriteObservations.payload (rows.map fun r => r.read.value.toBitVec64) address length := by
  have packed :
      (rows.map (WordRow.octets (256 : ZMod p)⁻¹)).flatMap (fun r => (r.bytes.map fun b => BitVec.ofNat 8 b.val).toList) =
      (rows.map fun r => r.read.value.toBitVec64).flatMap (fun w => (wordBytes w).toList) := by
    induction rows with
    | nil => rfl
    | cons first tail ih =>
      simp only [List.map_cons, List.flatMap_cons, word_bytes first (checked first List.mem_cons_self)]
      exact congrArg _ (ih (fun r h => checked r (List.mem_cons_of_mem _ h)))
  unfold payload
  rw [packed]
  rfl

/-- Generate the two private row families from the actual x12 and observed full words. -/
def effectRows (clock : Nat) (fd address length : BitVec 64) (words : List (BitVec 64)) :
    Request (ZMod p) × List (WordRow (ZMod p)) :=
  let header : WritePacket.Header (ZMod p) := ⟨Address.ofNat clock, bitVecToWord fd, bitVecToWord address, bitVecToWord length⟩
  (Request.populate header, words.zipIdx.map fun (w, i) =>
    WordRow.populate ⟨Address.ofNat (8 * (address.toNat / 8 + i)), header.clock, bitVecToWord w⟩)

private theorem pop_valid (read : WriteProbe.Read (ZMod p)) (bound : read.value.isU64) :
    (WordRow.populate read).Valid := by
  apply WordRow.valid_of_decomp
  exact (U16toU8OperationSafe.spec_populate (bound 0) (bound 1) (bound 2) (bound 3) 1) rfl

private theorem effectRows_honest (clock : Nat) (fd addr len : BitVec 64) (words : List (BitVec 64)) :
    let prepared := effectRows (p := p) clock fd addr len words
    prepared.1.Valid ∧ (∀ r ∈ prepared.2, r.Valid) ∧ (prepared.2.map fun r => r.read.value.toBitVec64) = words := by
  refine ⟨Request.populate_valid _ (isU64_bitVecToWord _), ?_, ?_⟩
  · intro r member
    obtain ⟨⟨_, _⟩, _, rfl⟩ := List.mem_map.mp member
    apply pop_valid
    exact isU64_bitVecToWord _
  · simp [effectRows, WordRow.populate, List.map_map, Function.comp_def, toBitVec64_bitVecToWord]

/-- A successful admitted cut generates both physical inputs and a verifier-bound host transition.
There is no independent descriptor, payload, witness for the ordered guest reads, or hook reply. -/
theorem of_admissibleExecution {limits : ResourceLimits} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events)
    {cut : Nat} {call : CoreSyscallEvent} (atEvent : events[cut]? = some (.syscall call))
    (code : call.rawCode = SyscallKind.write.code) :
    let policy := FormalModel.Shard.policy p image
    ∃ current next frontier length words,
      mixedAccessPrefix policy image.program source.realize events cut = some (current, frontier) ∧
      mixedAccessPrefix policy image.program source.realize events (cut+1) = some (next, syscallFrontier frontier current.clock call) ∧
      WriteObservations.read? current.sail call = some (length, words) ∧
      let rows := effectRows (p := p) current.clock call.arg1 call.arg2 length words
      let bytes := payload (rows.2.map (WordRow.octets (256 : ZMod p)⁻¹)) call.arg2.toNat length.toNat
      rows.1.Valid ∧ (∀ r ∈ rows.2, r.Valid) ∧
      (WriteRoute.ofDescriptor call.arg1).Effect current.host bytes next.host ∧
      WriteStreams.fromEndpoints current.host next.host = WriteStreams.ofEvent (WriteRoute.ofDescriptor call.arg1) current.host bytes := by
  obtain ⟨current, next, frontier, length, words, atCut, after, _, read, _, _, _, _, _, dispatched, _⟩ :=
    WriteObservations.of_admissibleExecution execution atEvent code
  obtain ⟨request, valid, values⟩ := effectRows_honest (p := p) current.clock call.arg1 call.arg2 length words
  refine ⟨current, next, frontier, length, words, atCut, after, read, request, valid, ?_⟩
  simp only [payload_eq _ _ _ valid, values]
  have effect := (WriteRoute.effect_iff ..).mpr dispatched
  exact ⟨effect, (WriteStreams.ofEvent_binds effect).unique⟩

end SP1Clean.WriteEffects
