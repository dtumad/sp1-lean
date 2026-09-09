import SP1Clean.FormalModel.Contracts.OrderedInitialProvider
import SP1Clean.Native.Operations.OrderedBoundary
import SP1Clean.Proofs.Operations.AddOperation.Formal
import SP1Clean.Model.Semantics.Decode
import SP1Clean.Proofs.Chips.InitialRamProvider
import SP1Clean.Proofs.Chips.InitialRegisterProvider

/-! # Binding initial records to their ordered keys

This wrapper composes any proved initial-memory provider with an ordered boundary link. Its
current key is constrained to the provider's canonical address plus one. Zero is therefore
available as a fixed start sentinel, including when the first record initializes register x0.
The increment cannot wrap: canonical memory addresses fit in 48 bits.
-/

namespace SP1Clean.OrderedInitialProvider

open Circuit SP1Clean.Model.Core SP1Clean.Semantics SP1Clean.Channels SP1Clean.Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
variable {Payload : TypeMap} [ProvableType Payload]

private def oneWord : Word (ZMod p) := bitVecToWord 1

omit [Fact (2 ^ 17 < p)] in
private theorem key_of_addition (image : ProgramImage) (record : MemoryMsg (ZMod p))
    (current : Word (ZMod p)) (valid : MemoryBoundary.InitialSpec image record)
    (currentBound : Word.isU64 current)
    (addition : Word.toBitVec64 current = Word.toBitVec64 (MemoryBoundary.address record) + 1) :
    Word.toNat current = (MemoryMsg.locOf record).busAddress + 1 := by
  have address := valid.2.2.2.2.2
  have bound := MemLoc.busAddress_lt_two_pow_48 valid.2.2.2.1
  have equal := congrArg BitVec.toNat addition
  rw [Word.toBitVec64_toNat currentBound, BitVec.toNat_add,
    Word.toBitVec64_toNat address.1, address.2,
    show (1 : BitVec 64).toNat = 1 by decide] at equal
  exact equal.trans (Nat.mod_eq_of_lt (by omega))

def main (name : String) (provider : GeneralFormalCircuit (ZMod p) Payload MemoryMsg)
    (input : Var (Inputs Payload) (ZMod p)) : Circuit (ZMod p) (Var MemoryMsg (ZMod p)) := do
  let record ← provider input.payload
  let _ ← OrderedBoundary.circuit name input.link
  assertion AddOperation.circuit
    ⟨MemoryBoundary.address record, const oneWord, ⟨input.link.current⟩, 1⟩
  return record

def circuit (name : String) (image : ProgramImage)
    (provider : GeneralFormalCircuit (ZMod p) Payload MemoryMsg)
    (binds : ∀ input output data, provider.Spec input output data → MemoryBoundary.InitialSpec image output) :
    GeneralFormalCircuit (ZMod p) (Inputs Payload) MemoryMsg where
  main := main name provider
  Assumptions input data := provider.Assumptions input.payload data
  Spec input output _ := Spec image input.link output
  ProverAssumptions input data hint :=
    provider.ProverAssumptions input.payload data hint ∧ provider.Assumptions input.payload data ∧
      OrderedBoundary.ProverAssumptions input.link ∧
        ∀ output, provider.Spec input.payload output data →
          Word.toBitVec64 input.link.current = Word.toBitVec64 (MemoryBoundary.address output) + 1
  channelsWithRequirements := provider.channelsWithRequirements ++ [(OrderedBoundary.channel name).toRaw]
  soundness := by
    circuit_proof_start [OrderedBoundary.circuit, MemoryBoundary.address]
    have one : Vector.map (Expression.eval env) (Vector.map Expression.const (oneWord (p := p))) =
        oneWord := by simp only [Vector.map_map, Function.comp_def, Expression.eval]; exact Vector.map_id _
    rw [one] at h_holds
    have valid := binds _ _ _ (h_holds.1 h_assumptions)
    have addition := h_holds.2.2 ⟨fun _ => ⟨valid.2.2.2.2.2.1, isU64_bitVecToWord _⟩, Or.inr rfl⟩
    have key := key_of_addition image _ _ valid h_holds.2.1.2.1 (by
      simpa only [oneWord, toBitVec64_bitVecToWord, MemoryBoundary.address] using (addition rfl).2)
    exact ⟨⟨valid, h_holds.2.1, key⟩, Or.inr h_assumptions⟩
  completeness := by
    circuit_proof_start [OrderedBoundary.circuit, MemoryBoundary.address]
    have one : Vector.map (Expression.eval env.toEnvironment)
        (Vector.map Expression.const (oneWord (p := p))) = oneWord := by
      simp only [Vector.map_map, Function.comp_def, Expression.eval]
      exact Vector.map_id _
    rw [one]
    have spec := (h_env.1 h_assumptions.1).1 h_assumptions.2.1
    have valid := binds _ _ _ spec
    refine ⟨h_assumptions.1, h_assumptions.2.2.1,
      ⟨⟨fun _ => ⟨valid.2.2.2.2.2.1, isU64_bitVecToWord _⟩, Or.inr rfl⟩, ?_⟩⟩
    intro _
    refine ⟨h_assumptions.2.2.1.1.2.1, ?_⟩
    simpa only [oneWord, toBitVec64_bitVecToWord] using h_assumptions.2.2.2 _ spec

/-- Both classes of initial records share one address-ordering channel. -/
def channelName : String := "SP1NativeMemoryInitOrder"

def ramCircuit (image : ProgramImage) :
    GeneralFormalCircuit (ZMod p) (Inputs InitialRamProvider.Inputs) MemoryMsg :=
  circuit channelName image (InitialRamProvider.circuit image) (fun _ _ _ valid => valid.1)

def registerCircuit (image : ProgramImage) :
    GeneralFormalCircuit (ZMod p) (Inputs field) MemoryMsg :=
  circuit channelName image (InitialRegisterProvider.circuit image) (fun _ _ _ valid => valid.1)

/-- Construct the control columns from the payload and its semantic address. -/
def populate (payload : Payload (ZMod p)) (previous address : ℕ) : Inputs Payload (ZMod p) :=
  ⟨payload, OrderedBoundary.populate (bitVecToWord (BitVec.ofNat 64 previous))
    (bitVecToWord (BitVec.ofNat 64 (address + 1)))⟩

/-- A provider that preserves its query admits the ordered wrapper's honest constructor.
In particular, the universally quantified internal output condition is discharged here rather
than left as a compiler-readiness condition on an execution. -/
theorem populate_assumptions (name : String) (image : ProgramImage)
    (provider : GeneralFormalCircuit (ZMod p) Payload MemoryMsg)
    (query : Payload (ZMod p) → ℕ)
    (bindsAt : ∀ input output data,
      provider.Spec input output data → MemoryBoundary.InitialAtSpec image (query input) output)
    (payload : Payload (ZMod p)) (previous : ℕ) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (prover : provider.ProverAssumptions payload data hint) (assumes : provider.Assumptions payload data)
    (bound : query payload < 2 ^ 48) (increases : previous < query payload + 1) :
    (circuit name image provider (fun input output data spec => (bindsAt input output data spec).1)).ProverAssumptions
      (populate payload previous (query payload)) data hint := by
  have previousBound : previous < 2 ^ 64 := by omega
  have currentBound : query payload + 1 < 2 ^ 64 := by omega
  refine ⟨prover, assumes, ?_, ?_⟩
  · apply OrderedBoundary.populate_assumptions _ _ (isU64_bitVecToWord _) (isU64_bitVecToWord _)
    rw [endpoint_toNat _ previousBound, endpoint_toNat _ currentBound]
    exact increases
  · intro output spec
    have valid := bindsAt payload output data spec
    change Word.toBitVec64 (bitVecToWord (BitVec.ofNat 64 (query payload + 1))) = _
    rw [toBitVec64_bitVecToWord]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt currentBound, BitVec.toNat_add,
      Word.toBitVec64_toNat valid.1.2.2.2.2.2.1, valid.2,
      show (1 : BitVec 64).toNat = 1 by decide, Nat.mod_eq_of_lt currentBound]

/-- The complete ordered RAM row constructor has no proof inputs or external column hints. -/
def populateRam? (image : ProgramImage) (previous address : ℕ) :
    Option (Inputs InitialRamProvider.Inputs (ZMod p)) :=
  if previous < address + 1 then
    (InitialRamProvider.populate? image address).map (fun payload => populate payload previous address)
  else none

theorem populateRam?_sound (image : ProgramImage) (previous address : ℕ)
    (input : Inputs InitialRamProvider.Inputs (ZMod p))
    (found : populateRam? image previous address = some input)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (ramCircuit image).ProverAssumptions input data hint := by
  unfold populateRam? at found
  split at found
  next increases =>
    obtain ⟨payload, generated, rfl⟩ := Option.map_eq_some_iff.mp found
    have valid := InitialRamProvider.populate?_sound image address payload generated
    have domain := (InitialRamProvider.populate?_isSome_iff (p := p) image address).mp
      (by rw [generated]; rfl)
    have built := populate_assumptions channelName image (InitialRamProvider.circuit image)
      (fun input => Word.toNat input.bytes[0].address) (fun _ _ _ spec => spec)
      payload previous data hint ⟨valid.1, valid.2.1⟩ trivial
      (by rw [valid.2.2]; exact domain.2.1) (by rw [valid.2.2]; exact increases)
    simpa only [ramCircuit, valid.2.2] using built
  next invalid => contradiction

omit [Fact (2 ^ 17 < p)] in
theorem populateRam?_isSome_iff (image : ProgramImage) (previous address : ℕ) :
    (populateRam? (p := p) image previous address).isSome = true ↔
      previous < address + 1 ∧ 2 ^ 16 ≤ address ∧ address < 2 ^ 48 ∧ address % 8 = 0 := by
  simp only [populateRam?]
  split
  next increases => simp only [Option.isSome_map, InitialRamProvider.populate?_isSome_iff, increases, true_and]
  next invalid => simp only [Option.isSome_none, Bool.false_eq_true, invalid, false_and]

/-- A register needs only its index and the preceding key; x0 uses current key one. -/
theorem populateRegister_assumptions (image : ProgramImage) (index : BitVec 5) (previous : ℕ)
    (increases : previous < index.toNat + 1) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (registerCircuit image).ProverAssumptions
      (populate (InitialRegisterProvider.populate index) previous index.toNat) data hint := by
  have indexP : index.toNat < p := by
    have := index.isLt; have := Fact.out (p := 2 ^ 17 < p); omega
  have indexEq : (InitialRegisterProvider.populate (p := p) index).val = index.toNat :=
    ZMod.val_natCast_of_lt indexP
  have built := populate_assumptions channelName image (InitialRegisterProvider.circuit image)
    (fun index => index.val) (fun _ _ _ spec => spec)
    (InitialRegisterProvider.populate index) previous data hint
    (InitialRegisterProvider.populate_assumptions index) trivial
    (by rw [indexEq]; have := index.isLt; omega) (by rw [indexEq]; exact increases)
  simpa only [registerCircuit, indexEq] using built

end SP1Clean.OrderedInitialProvider
