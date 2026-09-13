import SP1Clean.FormalModel.Contracts.SnapshotMemory
import ToClean.Circuit.InteractionRecovery
import SP1Clean.Native.Operations.InitialMemoryRead
import SP1Clean.Native.Operations.AddressOperation

/-! # Source RAM values authenticated by an arbitrary finite snapshot

The word-read circuit authenticates eight bytes. The address circuit proves that their base is
an aligned, non-reserved SP1 RAM address. The resulting zero-time record is pushed directly to
the instruction chips' Memory bus. This provider has no activity selector: an empty table needs
no padding, and each present row supplies exactly one initial record.
-/

namespace SP1Clean.SnapshotRamProvider

open Circuit SP1Clean.Model.Core SP1Clean.Semantics SP1Clean.Channels
open SP1Clean.Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

abbrev Inputs := InitialMemoryRead.Inputs

/-- The address gadget checks an aligned read without an immediate offset. -/
def addressInput {R : Type} [Zero R] [One R] (input : Inputs R) : AddressOperation.Inputs R :=
  ⟨input.bytes[0].address, #v[0, 0, 0, 0], 0, 0, 0, 1⟩

/-- The actual message emitted by the provider; the address is the checked gadget's output. -/
def message {R : Type} [Zero R] (address : Extracted.AddressOperation R)
    (value : Word R) : MemoryMsg R :=
  ⟨0, 0, address.addr_operation.value[0], address.addr_operation.value[1],
    address.addr_operation.value[2], value⟩

omit [Fact (2 ^ 17 < p)] in
private theorem zero_u64 : Word.isU64 (#v[0, 0, 0, 0] : Word (ZMod p)) := by
  apply Word.isU64_of_cases <;> norm_num

omit [Fact (2 ^ 17 < p)] in
private theorem address_assumptions (input : Inputs (ZMod p))
    (bound : Word.isU64 input.bytes[0].address) :
    AddressOperation.SoundnessAssumptions (addressInput input) :=
  ⟨bound, zero_u64, Or.inr rfl⟩

private theorem key_reorder (a b c total : ℕ)
    (equal : a + 65536 * b + 65536 ^ 2 * c = total) :
    a + b * 2 ^ 16 + c * 2 ^ 32 = total := by
  norm_num at equal ⊢
  omega

omit [Fact (2 ^ 17 < p)] in
/-- Aligned 48-bit addresses decode to exactly the RAM word that was authenticated. -/
private theorem ram_location (input : Inputs (ZMod p))
    (value : Word (ZMod p)) (address : Extracted.AddressOperation (ZMod p))
    (footprint : Word.toNat input.bytes[0].address + 8 ≤ 2 ^ 48)
    (checked : AddressOperation.Spec (addressInput input) address) :
    (MemoryMsg.locOf (message address value)).CanonicalAddress ∧
      Word.toNat (MemoryBoundary.address (message address value)) =
        (MemoryMsg.locOf (message address value)).busAddress := by
  have facts := AddressOperation.validAddress_of_spec checked
  have zero_nat : Word.toNat (#v[0, 0, 0, 0] : Word (ZMod p)) = 0 := by
    simp [Word.toNat]
  simp only [AddressOperation.ValidAddress, addressInput, zero_nat,
    Nat.mod_eq_of_lt (by omega : Word.toNat input.bytes[0].address < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : Word.toNat input.bytes[0].address < 2 ^ 48),
    ZMod.val_zero, mul_zero, add_zero] at facts
  have sumEq : (Word.toNat (addressInput input).b + Word.toNat (addressInput input).cc) % 2 ^ 48 =
      Word.toNat input.bytes[0].address := by
    exact (congrArg (fun value => (Word.toNat input.bytes[0].address + value) % 2 ^ 48) zero_nat).trans
      ((congrArg (fun value => value % 2 ^ 48) (Nat.add_zero _)).trans
        (Nat.mod_eq_of_lt (by omega)))
  have location := MemoryBoundary.ram_location_of_key (message address value) _ facts.2.1 facts.1 facts.2.2.symm
    ((key_reorder _ _ _ _ checked.1).trans sumEq)
  exact ⟨location.1, location.2.1⟩

omit [Fact (2 ^ 17 < p)] in
private theorem address_eq (input : Inputs (ZMod p)) (value : Word (ZMod p))
    (address : Extracted.AddressOperation (ZMod p))
    (footprint : Word.toNat input.bytes[0].address + 8 ≤ 2 ^ 48)
    (checked : AddressOperation.Spec (addressInput input) address) :
    Word.toNat (MemoryBoundary.address (message address value)) = Word.toNat input.bytes[0].address := by
  have raw := key_reorder _ _ _ _ checked.1
  have packed : Word.toNat (MemoryBoundary.address (message address value)) =
      (Word.toNat (addressInput input).b + Word.toNat (addressInput input).cc) % 2 ^ 48 := by
    simpa only [MemoryBoundary.address, message, Word.toNat, circuit_norm, ZMod.val_zero,
      zero_mul, add_zero] using raw
  have zero_nat : Word.toNat (#v[0, 0, 0, 0] : Word (ZMod p)) = 0 := by simp [Word.toNat]
  exact packed.trans
    ((congrArg (fun value => (Word.toNat input.bytes[0].address + value) % 2 ^ 48) zero_nat).trans
      ((congrArg (fun value => value % 2 ^ 48) (Nat.add_zero _)).trans
        (Nat.mod_eq_of_lt (by omega))))

omit [Fact (2 ^ 17 < p)] in
/-- The pushed RAM record has the canonical value from the supplied finite snapshot. -/
theorem snapshotSpec (snapshot : MemorySnapshot) (input : Inputs (ZMod p))
    (value : Word (ZMod p)) (address : Extracted.AddressOperation (ZMod p))
    (read : InitialMemoryRead.Spec snapshot.memory input value)
    (checked : AddressOperation.Spec (addressInput input) address) :
    MemoryBoundary.SnapshotAtSpec snapshot (Word.toNat input.bytes[0].address) (message address value) := by
  refine ⟨?_, address_eq input value address read.2.1 checked⟩
  have location := ram_location input value address read.2.1 checked
  have queryEq := address_eq input value address read.2.1 checked
  have lower := (AddressOperation.validAddress_of_spec checked).2.1
  simp only [addressInput, show Word.toNat (#v[0, 0, 0, 0] : Word (ZMod p)) = 0 by
    simp [Word.toNat], add_zero,
    Nat.mod_eq_of_lt (by have := read.2.1; omega : Word.toNat input.bytes[0].address < 2 ^ 48)] at lower
  have content : snapshot.read (MemoryMsg.locOf (message address value)) = Word.toBitVec64 value := by
    rw [snapshot.read_of_ram_address _ (by rw [← location.2, queryEq]; omega),
      ← location.2, queryEq]
    exact read.2.2.2.symm
  exact ⟨read.2.2.1, by simp [MemoryMsg.ClkBound, message],
    by simp [MemoryMsg.timeNat, clkNat, message], location.1,
    content,
    ⟨by
      apply Word.isU64_of_cases
      · exact checked.2.2.2.2.2.2.2.1
      · exact checked.2.2.2.2.2.2.2.2.1
      · exact checked.2.2.2.2.2.2.2.2.2
      · norm_num [MemoryBoundary.address], location.2⟩⟩

omit [Fact (2 ^ 17 < p)] in
private theorem eval_base (env : Environment (ZMod p))
    (vars : Vector (Var InitialMemoryLookup.Inputs (ZMod p)) 8)
    (values : Vector (InitialMemoryLookup.Inputs (ZMod p)) 8)
    (equal : eval env vars = values) :
    Vector.map (Expression.eval env) vars[0].address = values[0].address := by
  have first := eval_vector_eq_get env vars values equal 0 (by decide)
  generalize vars[0] = row at first ⊢
  rcases row with ⟨address, interval, lower, upper⟩
  simpa only [circuit_norm] using congrArg InitialMemoryLookup.Inputs.address first

def main (snapshot : MemorySnapshot) (input : Var Inputs (ZMod p)) :
    Circuit (ZMod p) (Var MemoryMsg (ZMod p)) := do
  let value ← InitialMemoryRead.circuit snapshot.memory input
  let address ← AddressOperation.circuit (addressInput input)
  let record := message address value
  memoryChannel.push record
  return record

instance elaborated (snapshot : MemorySnapshot) :
    ElaboratedCircuit (ZMod p) Inputs MemoryMsg (main snapshot) := by
  elaborate_circuit

theorem main_memory_interactions (snapshot : MemorySnapshot) (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main snapshot input).operations offset).interactionsWith memoryChannel.toRaw =
      [(memoryChannel.pushed ((elaborated snapshot).output input offset)).toRaw] := by
  have readEmpty (n : ℕ) := InteractionRecovery.interactionsWith_main_eq_nil
    (InitialMemoryRead.circuit snapshot.memory).base memoryChannel.toRaw input n (by
      simp [ InitialMemoryRead.circuit, circuit_norm, memoryChannel, byteChannel])
  have addressEmpty (n : ℕ) := InteractionRecovery.interactionsWith_main_eq_nil
    AddressOperation.circuit.base memoryChannel.toRaw (addressInput input) n (by
      simp [ AddressOperation.circuit, circuit_norm, memoryChannel, byteChannel])
  simp only [main, circuit_norm]
  simp only [Operations.interactionsWith] at readEmpty addressEmpty ⊢
  simp only [GeneralFormalCircuit.toSubcircuit_interactions, readEmpty, addressEmpty, List.nil_append]
  rfl

def circuit (snapshot : MemorySnapshot) : GeneralFormalCircuit (ZMod p) Inputs MemoryMsg where
  main := main snapshot
  elaborated := elaborated snapshot
  Spec input output _ := MemoryBoundary.SnapshotAtSpec snapshot (Word.toNat input.bytes[0].address) output
  ProverAssumptions input _ _ :=
    InitialMemoryRead.ProverAssumptions snapshot.memory input ∧
      AddressOperation.Assumptions (addressInput input)
  channelsWithRequirements := [memoryChannel.toRaw]
  soundness := by
    circuit_proof_start [InitialMemoryRead.circuit, AddressOperation.circuit, addressInput, message]
    rw [eval_base env _ _ h_input] at h_holds
    have checked := (h_holds.2 (address_assumptions ⟨input_bytes⟩ h_holds.1.1)).2.2.2 rfl
    have valid := snapshotSpec snapshot ⟨input_bytes⟩ _ _ h_holds.1 checked
    simp only [message, circuit_norm] at valid
    exact ⟨valid, fun _ _ => ⟨valid.1.1, valid.1.2.1⟩⟩
  completeness := by
    circuit_proof_start [InitialMemoryRead.circuit, AddressOperation.circuit, addressInput, message]
    rw [eval_base env.toEnvironment _ _ h_input]
    exact h_assumptions

/-- Construct a row from a semantic address, rejecting unaligned or reserved memory. -/
def populate? (snapshot : MemorySnapshot) (address : ℕ) : Option (Inputs (ZMod p)) :=
  if 2 ^ 16 ≤ address ∧ address % 8 = 0 then
    InitialMemoryRead.populate? snapshot.memory address
  else none

theorem populate?_sound (snapshot : MemorySnapshot) (address : ℕ) (input : Inputs (ZMod p))
    (found : populate? snapshot address = some input) :
    InitialMemoryRead.ProverAssumptions snapshot.memory input ∧
      AddressOperation.Assumptions (addressInput input) ∧
        Word.toNat input.bytes[0].address = address := by
  unfold populate? at found
  split at found
  next valid =>
    have read := InitialMemoryRead.populate?_sound snapshot.memory address input found
    have footprint := (InitialMemoryRead.populate?_isSome_iff (p := p) snapshot.memory address).mp
      (by rw [found]; rfl)
    refine ⟨read.1, ?_, read.2⟩
    change Word.isU64 input.bytes[0].address ∧ _
    refine ⟨(read.1 0).1.1, zero_u64, Or.inr rfl, ?_,
      Or.inl rfl, Or.inl rfl, Or.inl rfl, ?_, ?_⟩ <;>
      simp only [addressInput, show Word.toNat (#v[0, 0, 0, 0] : Word (ZMod p)) = 0 by
        simp [Word.toNat], read.2, ZMod.val_zero, mul_zero, add_zero,
        Nat.mod_eq_of_lt (by omega : address < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : address < 2 ^ 48)]
    · omega
    · exact fun _ => valid.1
    · exact valid.2.symm
  next invalid => contradiction

omit [Fact (2 ^ 17 < p)] in
/-- Row construction is total on exactly the semantic domain of aligned guest RAM cells. -/
theorem populate?_isSome_iff (snapshot : MemorySnapshot) (address : ℕ) :
    (populate? (p := p) snapshot address).isSome = true ↔
      2 ^ 16 ≤ address ∧ address < 2 ^ 48 ∧ address % 8 = 0 := by
  unfold populate?
  split
  next valid =>
    rw [InitialMemoryRead.populate?_isSome_iff]
    omega
  next invalid =>
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro ⟨lower, _, aligned⟩
    exact invalid ⟨lower, aligned⟩

end SP1Clean.SnapshotRamProvider
