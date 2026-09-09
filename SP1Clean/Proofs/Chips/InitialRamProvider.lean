import SP1Clean.FormalModel.Contracts.MemoryBoundary
import SP1Clean.Native.Operations.InitialMemoryRead
import SP1Clean.Native.Operations.AddressOperation

/-! # Initial RAM values authenticated by the native image

The word-read circuit authenticates eight bytes. The address circuit proves that their base is
an aligned, non-reserved SP1 RAM address. The resulting zero-time record is pushed directly to
the instruction chips' Memory bus. This provider has no activity selector: an empty table needs
no padding, and each present row supplies exactly one initial record.
-/

namespace SP1Clean.InitialRamProvider

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

omit [Fact (2 ^ 17 < p)] in
private theorem aligned_cell (address : ℕ) (bound : address < 2 ^ 48)
    (aligned : address % 8 = 0) :
    (BitVec.ofNat 61 (address / 8)).toNat * 8 = address := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : address / 8 < 2 ^ 61)]
  omega

omit [Fact (2 ^ 17 < p)] in
private theorem ram_location_of_key (record : MemoryMsg (ZMod p)) (address : ℕ)
    (lower : 2 ^ 16 ≤ address) (upper : address < 2 ^ 48) (alignment : address % 8 = 0)
    (key : record.addr0.val + record.addr1.val * 2 ^ 16 + record.addr2.val * 2 ^ 32 = address) :
    (MemoryMsg.locOf record).CanonicalAddress ∧
      Word.toNat (MemoryBoundary.address record) = (MemoryMsg.locOf record).busAddress ∧
      ∀ state, locContent state (MemoryMsg.locOf record) =
        ramWord64? state (BitVec.ofNat 64 address) := by
  have notRegister : ¬ (record.addr0.val < 32 ∧ record.addr1 = 0 ∧ record.addr2 = 0) := by
    rintro ⟨small, one, two⟩
    simp only [one, two, ZMod.val_zero, zero_mul, add_zero] at key
    omega
  let cell : RamCell := BitVec.ofNat 61 (address / 8)
  have aligned : cell.toNat * 8 = address := aligned_cell address upper alignment
  have decoded : MemoryMsg.locOf record = MemLoc.ram cell := by
    simp only [MemoryMsg.locOf, if_neg notRegister, key, cell]
  have base : cell.baseAddr = BitVec.ofNat 64 address :=
    congrArg (BitVec.ofNat 64) aligned
  refine ⟨?_, ?_, ?_⟩
  · rw [decoded]
    change 32 ≤ cell.toNat * 8 ∧ cell.toNat * 8 < 2 ^ 48
    rw [aligned]
    exact ⟨by omega, upper⟩
  · rw [decoded]
    change Word.toNat (MemoryBoundary.address record) = cell.toNat * 8
    simpa only [MemoryBoundary.address, Word.toNat, circuit_norm, ZMod.val_zero,
      zero_mul, add_zero, aligned] using key
  · intro state
    rw [decoded]
    change ramWord64? state cell.baseAddr = _
    rw [base]

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
        (MemoryMsg.locOf (message address value)).busAddress ∧
      ∀ state, locContent state (MemoryMsg.locOf (message address value)) =
        ramWord64? state (Word.toBitVec64 input.bytes[0].address) := by
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
  exact ram_location_of_key _ _ facts.2.1 facts.1 facts.2.2.symm
    ((key_reorder _ _ _ _ checked.1).trans sumEq)

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
/-- The pushed RAM record has its canonical value in the actual native boot state. -/
theorem initialSpec (image : ProgramImage) (input : Inputs (ZMod p))
    (value : Word (ZMod p)) (address : Extracted.AddressOperation (ZMod p))
    (read : InitialMemoryRead.Spec image.initialMemory input value)
    (checked : AddressOperation.Spec (addressInput input) address) :
    MemoryBoundary.InitialAtSpec image (Word.toNat input.bytes[0].address) (message address value) := by
  refine ⟨?_, address_eq input value address read.2.1 checked⟩
  have location := ram_location input value address read.2.1 checked
  exact ⟨read.2.2.1, by simp [MemoryMsg.ClkBound, message],
    by simp [MemoryMsg.timeNat, clkNat, message], location.1,
    (location.2.2 image.initialSailState).trans (read.initialSailState image input value),
    ⟨by
      apply Word.isU64_of_cases
      · exact checked.2.2.2.2.2.2.2.1
      · exact checked.2.2.2.2.2.2.2.2.1
      · exact checked.2.2.2.2.2.2.2.2.2
      · norm_num [MemoryBoundary.address], location.2.1⟩⟩

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

def main (image : ProgramImage) (input : Var Inputs (ZMod p)) :
    Circuit (ZMod p) (Var MemoryMsg (ZMod p)) := do
  let value ← InitialMemoryRead.circuit image.initialMemory input
  let address ← AddressOperation.circuit (addressInput input)
  let record := message address value
  memoryChannel.push record
  return record

instance elaborated (image : ProgramImage) :
    ElaboratedCircuit (ZMod p) Inputs MemoryMsg (main image) := by
  elaborate_circuit

def circuit (image : ProgramImage) : GeneralFormalCircuit (ZMod p) Inputs MemoryMsg where
  main := main image
  elaborated := elaborated image
  Spec input output _ := MemoryBoundary.InitialAtSpec image (Word.toNat input.bytes[0].address) output
  ProverAssumptions input _ _ :=
    InitialMemoryRead.ProverAssumptions image.initialMemory input ∧
      AddressOperation.Assumptions (addressInput input)
  channelsWithRequirements := [memoryChannel.toRaw]
  soundness := by
    circuit_proof_start [InitialMemoryRead.circuit, AddressOperation.circuit, addressInput, message]
    rw [eval_base env _ _ h_input] at h_holds
    have checked := (h_holds.2 (address_assumptions ⟨input_bytes⟩ h_holds.1.1)).2.2.2 rfl
    have valid := initialSpec image ⟨input_bytes⟩ _ _ h_holds.1 checked
    simp only [message, circuit_norm] at valid
    exact ⟨valid, fun _ _ => ⟨valid.1.1, valid.1.2.1⟩⟩
  completeness := by
    circuit_proof_start [InitialMemoryRead.circuit, AddressOperation.circuit, addressInput, message]
    rw [eval_base env.toEnvironment _ _ h_input]
    exact h_assumptions

/-- Construct a row from a semantic address, rejecting unaligned or reserved memory. -/
def populate? (image : ProgramImage) (address : ℕ) : Option (Inputs (ZMod p)) :=
  if 2 ^ 16 ≤ address ∧ address % 8 = 0 then
    InitialMemoryRead.populate? image.initialMemory address
  else none

theorem populate?_sound (image : ProgramImage) (address : ℕ) (input : Inputs (ZMod p))
    (found : populate? image address = some input) :
    InitialMemoryRead.ProverAssumptions image.initialMemory input ∧
      AddressOperation.Assumptions (addressInput input) ∧
        Word.toNat input.bytes[0].address = address := by
  unfold populate? at found
  split at found
  next valid =>
    have read := InitialMemoryRead.populate?_sound image.initialMemory address input found
    have footprint := (InitialMemoryRead.populate?_isSome_iff (p := p) image.initialMemory address).mp
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
theorem populate?_isSome_iff (image : ProgramImage) (address : ℕ) :
    (populate? (p := p) image address).isSome = true ↔
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

end SP1Clean.InitialRamProvider
