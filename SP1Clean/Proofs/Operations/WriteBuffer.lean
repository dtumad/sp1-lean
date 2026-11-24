import SP1Clean.Native.Operations.WriteBuffer
import SP1Clean.Semantics.ISA.Decode

/-! # Checked cursor and span meanings

Every accepted word advances its absolute cell index and observes the corresponding aligned
byte address. A header pins both ends by exact unwrapped addition of its original address and length.
-/

namespace SP1Clean.WriteBuffer
open Circuit Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Exact observable word edge. Its payload is supplied by the physical read receipt. -/
def Step.Valid (s : Step (ZMod p)) : Prop :=
  Address.Bounded s.read.key ∧ Address.Bounded s.index ∧ Address.Bounded s.next ∧
  Address.toNat s.read.key = 8 * Address.toNat s.index ∧ Address.toNat s.next = Address.toNat s.index + 1

/-- The quotient witness is deterministic. -/
def Step.Honest (s : Step (ZMod p)) : Prop := s.Valid ∧ s.division = AddressDiv8.populate (Address.asWord s.read.key)

/-- Populate an aligned step from the actual cell and returned word. -/
def Step.populate (clock : fields 3 (ZMod p)) (index : ℕ) (word : Word (ZMod p)) : Step (ZMod p) :=
  let read := WriteProbe.Read.mk (Address.ofNat (8 * index)) clock word
  ⟨read, (AddressDiv8.populate (Address.asWord read.key)).quotients, Address.ofNat index, Address.ofNat (index + 1)⟩

theorem Step.populate_honest (clock : fields 3 (ZMod p)) (i : ℕ) (word : Word (ZMod p)) (fits : i < 2 ^ 45) :
    (Step.populate clock i word).Honest := by
  have k : 8 * i < 2 ^ 48 := by omega
  have n : i + 1 < 2 ^ 48 := by omega
  exact ⟨⟨Address.bounded_ofNat _, Address.bounded_ofNat _, Address.bounded_ofNat _,
    by simp [populate, Address.toNat_ofNat _ k, Address.toNat_ofNat _ (show i < 2 ^ 48 by omega)],
    by simp [populate, Address.toNat_ofNat _ n, Address.toNat_ofNat _ (show i < 2 ^ 48 by omega)]⟩, rfl⟩

omit [Fact (2 ^ 17 < p)] in
private theorem one_word : Word.isU64 (#v[1, 0, 0, 0] : Word (ZMod p)) ∧
    Word.toNat (#v[1, 0, 0, 0] : Word (ZMod p)) = 1 := by
  constructor
  · apply Word.isU64_of_cases <;> simp only [circuit_norm, ZMod.val_one, ZMod.val_zero] <;> omega
  · simp [Word.toNat_def, ZMod.val_one]

omit [Fact (2 ^ 17 < p)] in
private theorem step_sound (s : Step (ZMod p)) {d : AddressDiv8.Output (ZMod p)}
    (div : AddressDiv8.Spec s.division d) (index : d.quotient = s.index) (align : d.remainder = 0)
    (sum : AddrAddOperation.Assumptions ⟨Address.asWord s.index, #v[1, 0, 0, 0], ⟨s.next⟩, 1⟩ →
      AddrAddOperation.Spec ⟨Address.asWord s.index, #v[1, 0, 0, 0], ⟨s.next⟩, 1⟩) : s.Valid := by
  obtain ⟨low, _, qBound, q, rem, _⟩ := div
  rw [index] at qBound q
  simp only [Step.division, Address.toNat_asWord, align, ZMod.val_zero] at q rem
  have := Address.toNat_lt qBound
  obtain ⟨next, eq, _⟩ := AddrAddOperation.exact_sum _ _ _ (sum ⟨Address.isU64_asWord qBound, one_word.1, Or.inr rfl⟩)
    (by rw [Address.toNat_asWord, one_word.2]; omega)
  exact ⟨Address.bounded_of_isU64_asWord low, qBound, next, by omega, by simpa [Address.toNat_asWord, one_word.2] using eq⟩

private theorem step_checks (s : Step (ZMod p)) (valid : s.Valid) {d : AddressDiv8.Output (ZMod p)}
    (div : AddressDiv8.Spec s.division d) :
    d.quotient = s.index ∧ d.remainder = 0 ∧
      (AddrAddOperation.Assumptions ⟨Address.asWord s.index, #v[1, 0, 0, 0], ⟨s.next⟩, 1⟩ ∧
       AddrAddOperation.Spec ⟨Address.asWord s.index, #v[1, 0, 0, 0], ⟨s.next⟩, 1⟩) := by
  obtain ⟨_, idx, nxt, address, successor⟩ := valid
  obtain ⟨_, _, qBound, q, rem, _⟩ := div
  simp only [Step.division, Address.toNat_asWord, address] at q rem
  refine ⟨?_, ?_, ⟨Address.isU64_asWord idx, one_word.1, Or.inr rfl⟩, ?_⟩
  · rw [← Address.ofNat_toNat qBound, ← Address.ofNat_toNat idx]
    congr 1
    omega
  · exact ZMod.val_injective _ (by rw [ZMod.val_zero]; omega)
  · apply AddrAddOperation.spec_of_sum _ _ _ nxt
    rwa [Address.toNat_asWord, one_word.2]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_division (env : Environment (ZMod p)) (s : Var Step (ZMod p)) :
    ProvableStruct.eval env s.division = (ProvableStruct.eval env s).division := by
  rcases s with ⟨⟨_,_,_⟩,_,_,_⟩
  simp only [Step.division, Address.asWord, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_asWord (env : Environment (ZMod p)) (x : fields 3 (Expression (ZMod p))) :
    Eval.eval env (Address.asWord x) = Address.asWord (Eval.eval env x) := by simp only [Address.asWord, circuit_norm]

/-- The actual word-transfer circuit on the read and cursor buses. -/
def stepCircuit : GeneralFormalCircuit (ZMod p) Step unit where
  name := "sp1.native.write_buffer_word"
  main := stepMain
  elaborated := stepElaborated
  computableWitnesses := by computable_witnesses [Step.division, Step.source, Step.target, Address.asWord]
  channelsWithRequirements := [channel.toRaw, wordChannel.toRaw]
  Spec s _ _ := s.Valid
  ProverAssumptions s _ _ := s.Honest
  soundness := by
    circuit_proof_start [stepMain, AddressDiv8.circuit, Gadgets.Equality.circuit, AddrAddOperation.circuit,
      channel, wordChannel, WriteProbe.readChannel, eval_division, eval_asWord]
    obtain ⟨d, index, aligned, successor⟩ := h_holds
    exact step_sound _ d index aligned successor
  completeness := by
    circuit_proof_start [stepMain, AddressDiv8.circuit, Gadgets.Equality.circuit, AddrAddOperation.circuit,
      channel, wordChannel, WriteProbe.readChannel, eval_division, eval_asWord]
    obtain ⟨valid, prepared⟩ := h_assumptions
    have a : AddressDiv8.ProverAssumptions _ := ⟨Address.isU64_asWord valid.1,
      by simpa only [Step.division, Address.toNat_asWord] using Address.toNat_lt valid.1, prepared⟩
    exact ⟨a, step_checks _ valid (h_env a)⟩

/-- Both typed header endpoint words are exact and cover the released guest RAM window. -/
def Span.Valid (s : Span (ZMod p)) : Prop :=
  s.header.address.isU64 ∧ s.header.length.isU64 ∧ s.finish.isU64 ∧
  2 ^ 16 ≤ s.header.address.toNat ∧ s.finish.toNat = s.header.address.toNat + s.header.length.toNat ∧
  s.finish.toNat ≤ 2 ^ 48 ∧ Address.Bounded s.first ∧ Address.Bounded s.stop ∧
  Address.toNat s.first = s.header.address.toNat / 8 ∧
  Address.toNat s.stop = (s.header.address.toNat + s.header.length.toNat + 7) / 8

/-- Both divisions' witnesses are computed from the original byte endpoints. -/
def Span.Honest (s : Span (ZMod p)) : Prop :=
  s.Valid ∧ Endpoint.ProverAssumptions false s.startEndpoint ∧ Endpoint.ProverAssumptions true s.endEndpoint

/-- Use the full untruncated byte sum when building the exclusive endpoint. -/
def Span.populate (h : WritePacket.Header (ZMod p)) : Span (ZMod p) :=
  let finish := bitVecToWord (BitVec.ofNat 64 (h.address.toNat + h.length.toNat))
  let first := Endpoint.populate false h.address
  let stop := Endpoint.populate true finish
  ⟨h, finish, first.quotients, stop.quotients, first.index, stop.index⟩

theorem Span.populate_honest (h : WritePacket.Header (ZMod p)) (addr : h.address.isU64) (len : h.length.isU64)
    (lower : 2 ^ 16 ≤ h.address.toNat) (bound : h.address.toNat + h.length.toNat ≤ 2 ^ 48) :
    (Span.populate h).Honest := by
  let finish := bitVecToWord (p := p) (BitVec.ofNat 64 (h.address.toNat + h.length.toNat))
  have fWord : finish.isU64 := isU64_bitVecToWord _
  have fValue : finish.toNat = h.address.toNat + h.length.toNat := by
    rw [← Word.toBitVec64_toNat fWord, toBitVec64_bitVecToWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have first := Endpoint.populate_valid false h.address addr (by omega)
  have stop := Endpoint.populate_valid true finish fWord (fValue ▸ bound)
  refine ⟨⟨addr, len, fWord, lower, fValue, fValue ▸ bound, first.1.2.2.1, stop.1.2.2.1,
    ?_, ?_⟩, first, stop⟩
  · change Address.toNat (Endpoint.populate false h.address).index = h.address.toNat / 8
    simpa [cellIndex, Endpoint.populate] using first.1.2.2.2
  · change Address.toNat (Endpoint.populate true finish).index = (h.address.toNat + h.length.toNat + 7) / 8
    rw [← fValue]
    exact stop.1.2.2.2

private theorem span_sound (s : Span (ZMod p)) (first : Endpoint.Spec false s.startEndpoint)
    (last : Endpoint.Spec true s.endEndpoint) (len : s.header.length.isU64) (hi : IsBool s.header.length[3])
    (sum : AddOperation.Assumptions ⟨s.header.address, s.header.length, ⟨s.finish⟩, 1⟩ →
      AddOperation.Spec ⟨s.header.address, s.header.length, ⟨s.finish⟩, 1⟩)
    (lower : AddressOrder.Assumptions ⟨minimum, s.first⟩ → AddressOrder.Spec ⟨minimum, s.first⟩) : s.Valid := by
  have fit : s.header.length.toNat < 2 ^ 49 := by
    have range := Word.lt_cases_of_isU64 len
    rcases hi with h | h <;> simp only [Word.toNat_def, h, ZMod.val_zero, ZMod.val_one] <;> omega
  have eq := congrArg BitVec.toNat ((sum ⟨fun _ => ⟨first.1, len⟩, Or.inr rfl⟩) rfl).2
  change s.finish.toBitVec64.toNat = (s.header.address.toBitVec64 + s.header.length.toBitVec64).toNat at eq
  have aBound : s.header.address.toNat ≤ 2 ^ 48 := first.2.1
  have endWord : s.finish.isU64 := last.1
  have addrWord : s.header.address.isU64 := first.1
  rw [Word.toBitVec64_toNat endWord, BitVec.toNat_add, Word.toBitVec64_toNat addrWord,
    Word.toBitVec64_toNat len, Nat.mod_eq_of_lt (by omega)] at eq
  have firstIndex : Address.toNat s.first = s.header.address.toNat / 8 := by simpa [cellIndex, Span.startEndpoint] using first.2.2.2
  have lowerBound := lower ⟨Address.bounded_ofNat _, first.2.2.1⟩
  change Address.toNat minimum ≤ Address.toNat s.first at lowerBound
  rw [minimum, Address.toNat_ofNat _ (by norm_num), firstIndex] at lowerBound
  refine ⟨first.1, len, last.1, by omega, eq, last.2.1, first.2.2.1, last.2.2.1, firstIndex, ?_⟩
  rw [← eq]
  exact last.2.2.2

private theorem span_checks (s : Span (ZMod p)) (valid : s.Valid) :
    s.header.length.isU64 ∧ IsBool s.header.length[3] ∧
    (AddOperation.Assumptions ⟨s.header.address, s.header.length, ⟨s.finish⟩, 1⟩ ∧
      AddOperation.Spec ⟨s.header.address, s.header.length, ⟨s.finish⟩, 1⟩) ∧
    (AddressOrder.Assumptions ⟨minimum, s.first⟩ ∧ AddressOrder.Spec ⟨minimum, s.first⟩) := by
  obtain ⟨addr, len, fin, lo, sum, fits, first, _, idx, _⟩ := valid
  refine ⟨len, Or.inl ?_, ⟨⟨fun _ => ⟨addr, len⟩, Or.inr rfl⟩, fun _ => ⟨fin, ?_⟩⟩, ⟨Address.bounded_ofNat _, first⟩, ?_⟩
  · apply ZMod.val_injective
    rw [ZMod.val_zero]
    have lt : s.header.length.toNat < 2 ^ 48 := by omega
    simp only [Word.toNat_def] at lt
    omega
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, Word.toBitVec64_toNat addr, Word.toBitVec64_toNat len, Word.toBitVec64_toNat fin,
      Nat.mod_eq_of_lt (by omega), sum]
  · change Address.toNat minimum ≤ Address.toNat s.first
    rw [minimum, Address.toNat_ofNat _ (by norm_num), idx]
    omega

omit [Fact (2 ^ 17 < p)] in
private theorem eval_first (env : Environment (ZMod p)) (s : Var Span (ZMod p)) :
    ProvableStruct.eval env s.startEndpoint = (ProvableStruct.eval env s).startEndpoint := by
  rcases s with ⟨⟨_, _, _, _⟩, _, _, _, _, _⟩
  simp only [Span.startEndpoint, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_last (env : Environment (ZMod p)) (s : Var Span (ZMod p)) :
    ProvableStruct.eval env s.endEndpoint = (ProvableStruct.eval env s).endEndpoint := by
  rcases s with ⟨⟨_, _, _, _⟩, _, _, _, _, _⟩
  simp only [Span.endEndpoint, circuit_norm]

/-- The actual header-span row binds a complete header to two cell cursors. -/
def spanCircuit : GeneralFormalCircuit (ZMod p) Span unit where
  name := "sp1.native.write_buffer_span"
  main := spanMain
  elaborated := spanElaborated
  computableWitnesses := by computable_witnesses [Span.startEndpoint, Span.endEndpoint, Span.source, Span.target]
  channelsWithRequirements := [channel.toRaw, effectHeaderChannel.toRaw]
  Spec s _ _ := s.Valid
  ProverAssumptions s _ _ := s.Honest
  soundness := by
    circuit_proof_start [spanMain, Endpoint.circuit, WordRangeCheck.circuit, WordRangeCheck.Assumptions,
      WordRangeCheck.Spec, AddOperation.circuit, AddressOrder.circuit, WritePacket.channel, effectHeaderChannel, channel, eval_first, eval_last, Vector.map_id']
    obtain ⟨start, last, len, top, sum, lower⟩ := h_holds
    exact span_sound _ start last len top sum lower
  completeness := by
    circuit_proof_start [spanMain, Endpoint.circuit, WordRangeCheck.circuit, WordRangeCheck.Assumptions,
      WordRangeCheck.Spec, AddOperation.circuit, AddressOrder.circuit, WritePacket.channel, effectHeaderChannel, channel, eval_first, eval_last, Vector.map_id']
    obtain ⟨valid, start, last⟩ := h_assumptions
    exact ⟨start, last, span_checks _ valid⟩

end SP1Clean.WriteBuffer
