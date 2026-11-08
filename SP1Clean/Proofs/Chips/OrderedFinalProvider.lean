import SP1Clean.Proofs.Chips.OrderedMemoryProvider
import SP1Clean.Proofs.Chips.FinalRegisterProvider
import SP1Clean.Proofs.Chips.FinalRamProvider

/-! # Constructive ordered finalization

Both final-record circuits use the same ordering wrapper as initialization. Their constructors
accept exactly canonical register or bounded aligned RAM locations,
and a preceding key smaller than the record's key. No internal address-gadget condition escapes.
-/

namespace SP1Clean.OrderedFinalProvider

open Circuit SP1Clean.Channels SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def channelName : String := "SP1NativeMemoryFinalOrder"

def registerCircuit :
    GeneralFormalCircuit (ZMod p) (OrderedMemoryProvider.RowInput MemoryMsg) MemoryMsg :=
  OrderedMemoryProvider.circuit channelName MemoryBoundary.FinalSpec FinalRegisterProvider.circuit
    (fun _ _ _ valid => valid.1) (fun _ valid => valid)

def ramCircuit :
    GeneralFormalCircuit (ZMod p) (OrderedMemoryProvider.RowInput MemoryMsg) MemoryMsg :=
  OrderedMemoryProvider.circuit channelName MemoryBoundary.RamFinalSpec FinalRamProvider.circuit
    (fun _ _ _ valid => valid.1) (fun _ valid => valid.1)

omit [Fact (2 ^ 17 < p)] in
instance (record : MemoryMsg (ZMod p)) :
    Decidable (MemoryMsg.isU64 record ∧ MemoryMsg.ClkBound record) := by
  unfold MemoryMsg.isU64 MemoryMsg.ClkBound Word.isU64
  infer_instance

def populateRegister? (previous : ℕ) (record : MemoryMsg (ZMod p)) :
    Option (OrderedMemoryProvider.RowInput MemoryMsg (ZMod p)) :=
  if (FinalRegisterProvider.Domain record ∧ MemoryMsg.isU64 record ∧ MemoryMsg.ClkBound record) ∧ previous < Word.toNat (MemoryBoundary.address record) + 1 then
    some (OrderedMemoryProvider.populate record previous (Word.toNat (MemoryBoundary.address record)))
  else none

def populateRam? (previous : ℕ) (record : MemoryMsg (ZMod p)) :
    Option (OrderedMemoryProvider.RowInput MemoryMsg (ZMod p)) :=
  if (FinalRamProvider.Domain record ∧ MemoryMsg.isU64 record ∧ MemoryMsg.ClkBound record) ∧ previous < Word.toNat (MemoryBoundary.address record) + 1 then
    some (OrderedMemoryProvider.populate record previous (Word.toNat (MemoryBoundary.address record)))
  else none

omit [Fact (2 ^ 17 < p)] in
theorem populateRegister?_isSome_iff (previous : ℕ) (record : MemoryMsg (ZMod p)) :
    (populateRegister? previous record).isSome = true ↔
      (FinalRegisterProvider.Domain record ∧ MemoryMsg.isU64 record ∧ MemoryMsg.ClkBound record) ∧ previous < Word.toNat (MemoryBoundary.address record) + 1 := by
  unfold populateRegister?
  split <;> simp_all

omit [Fact (2 ^ 17 < p)] in
theorem populateRam?_isSome_iff (previous : ℕ) (record : MemoryMsg (ZMod p)) :
    (populateRam? previous record).isSome = true ↔
      (FinalRamProvider.Domain record ∧ MemoryMsg.isU64 record ∧ MemoryMsg.ClkBound record) ∧ previous < Word.toNat (MemoryBoundary.address record) + 1 := by
  unfold populateRam?
  split <;> simp_all

theorem populateRegister?_sound (previous : ℕ) (record : MemoryMsg (ZMod p))
    (input : OrderedMemoryProvider.RowInput MemoryMsg (ZMod p))
    (found : populateRegister? previous record = some input)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    registerCircuit.ProverAssumptions input data hint := by
  unfold populateRegister? at found
  split at found
  next valid =>
    obtain rfl := Option.some.inj found
    obtain ⟨⟨domain, wellFormed⟩, ordered⟩ := valid
    have canonical := FinalRegisterProvider.canonical record domain.1 domain.2.1 domain.2.2
    exact OrderedMemoryProvider.populate_assumptions channelName MemoryBoundary.FinalSpec
      FinalRegisterProvider.circuit (fun input => Word.toNat (MemoryBoundary.address input))
      (fun _ _ _ spec => spec) (fun _ spec => spec) record previous data hint ⟨domain, wellFormed⟩ trivial
      (by rw [canonical.2.2]; exact MemLoc.busAddress_lt_two_pow_48 canonical.1) ordered
  next invalid => contradiction

theorem populateRam?_sound (previous : ℕ) (record : MemoryMsg (ZMod p))
    (input : OrderedMemoryProvider.RowInput MemoryMsg (ZMod p))
    (found : populateRam? previous record = some input)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ramCircuit.ProverAssumptions input data hint := by
  unfold populateRam? at found
  split at found
  next valid =>
    obtain rfl := Option.some.inj found
    obtain ⟨⟨domain, wellFormed⟩, ordered⟩ := valid
    exact OrderedMemoryProvider.populate_assumptions channelName MemoryBoundary.RamFinalSpec
      FinalRamProvider.circuit (fun input => Word.toNat (MemoryBoundary.address input))
      (fun _ _ _ spec => spec) (fun _ spec => spec.1) record previous data hint
      ⟨(FinalRamProvider.addressAssumptions_iff record).mpr domain, wellFormed⟩ trivial domain.2.2.1 ordered
  next invalid => contradiction

end SP1Clean.OrderedFinalProvider
