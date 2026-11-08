import ToClean.Circuit.Guarded
import ToClean.Gadgets.LookupProjection
import SP1Clean.FormalModel.Contracts.MemoryBoundary
import ToClean.Circuit.InteractionRecovery
import ToClean.Circuit.EmittedInteraction
import SP1Clean.Model.Channels
import Clean.Gadgets.Bits
import Clean.Utils.Tactics

/-! # Canonical register finalization

Each physical row consumes one final Memory record. Its address must be a five-bit register index;
the higher address limbs must vanish. The bundled address check establishes canonical locations
without Memory guarantees; the finalizer additionally pulls the complete record.
-/

namespace SP1Clean.FinalRegisterProvider

open Circuit SP1Clean.Semantics SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact p.Prime] in
private theorem indexBound : 2 ^ 5 < p := by
  have := Fact.out (p := 2 ^ 17 < p)
  omega

omit [Fact (2 ^ 17 < p)] in
theorem canonical (record : MemoryMsg (ZMod p)) (small : record.addr0.val < 32)
    (one : record.addr1 = 0) (two : record.addr2 = 0) : MemoryBoundary.CanonicalSpec record := by
  have decoded : MemoryMsg.locOf record = .reg (BitVec.ofNat 5 record.addr0.val) := by
    simp only [MemoryMsg.locOf, small, one, two, and_self, ite_true]
  refine ⟨by rw [decoded]; trivial, ?_, ?_⟩
  · apply Word.isU64_of_cases
    · exact lt_trans small (by norm_num)
    all_goals simp [MemoryBoundary.address, one, two]
  · rw [decoded]
    simp [MemoryBoundary.address, Word.toNat, one, two, MemLoc.busAddress,
      Nat.mod_eq_of_lt small]

/-- The semantic domain of a register finalization row. -/
def Domain (record : MemoryMsg (ZMod p)) : Prop :=
  record.addr0.val < 32 ∧ record.addr1 = 0 ∧ record.addr2 = 0

instance (record : MemoryMsg (ZMod p)) : Decidable (Domain record) := by
  unfold Domain
  infer_instance

/-- Validate the register index and preserve the complete Memory message. -/
@[circuit_norm]
def addressMain (input : Var MemoryMsg (ZMod p)) : Circuit (ZMod p) (Var MemoryMsg (ZMod p)) := do
  assertion (Gadgets.ToBits.rangeCheck 5 indexBound) input.addr0
  assertZero input.addr1
  assertZero input.addr2
  return input

/-- Canonical register addressing needs no value or timestamp authentication. -/
def addressCircuit : GeneralFormalCircuit (ZMod p) MemoryMsg MemoryMsg where
  name := "sp1.native.memory.final.registers.address"
  main := addressMain
  Spec input output _ := MemoryBoundary.FinalAtSpec (Word.toNat (MemoryBoundary.address input)) output
  ProverAssumptions input _ _ := Domain input
  soundness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck, MemoryBoundary.address]
    exact ⟨canonical ⟨input_clk_high, input_clk_low, input_addr0, input_addr1, input_addr2, input_value⟩
      h_holds.1 h_holds.2.1 h_holds.2.2, rfl⟩
  completeness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck]
    exact h_assumptions

instance addressSupported : Guarded.Supported (addressCircuit (p := p)) :=
  Guarded.Supported.of_emitted_requirements _
    (by intro input offset; simp [addressCircuit, Gadgets.ToBits.rangeCheck,
      Gadgets.ToBits.toBits, circuit_norm])
    (by intro selected member; simp [addressCircuit, circuit_norm] at member)
    (by simp [addressCircuit])

def main (input : Var MemoryMsg (ZMod p)) : Circuit (ZMod p) (Var MemoryMsg (ZMod p)) := do
  let record ← addressCircuit input
  memoryChannel.pull record
  return record

theorem main_memory_interactions (input : Var MemoryMsg (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      [(memoryChannel.pulled input).toRaw] := by
  have empty := InteractionRecovery.interactionsWith_main_eq_nil addressCircuit.base memoryChannel.toRaw
    input offset (by simp [addressCircuit, circuit_norm])
  change Operations.interactionsWith memoryChannel.toRaw [Operation.subcircuit (addressCircuit.toSubcircuit offset input),
    Operation.interact (memoryChannel.pulled input).toRaw] = _
  simp only [Operations.interactionsWith] at empty
  simp only [circuit_norm, GeneralFormalCircuit.toSubcircuit_interactions, empty, List.nil_append]

instance elaborated : ElaboratedCircuit (ZMod p) MemoryMsg MemoryMsg main where
  localLength _ := 5
  output input _ := input
  channelsWithGuarantees := [memoryChannel.toRaw]

def circuit : GeneralFormalCircuit (ZMod p) MemoryMsg MemoryMsg where
  name := "sp1.native.memory.final.registers"
  main
  elaborated := elaborated
  Spec input output _ := MemoryBoundary.FinalAtSpec (Word.toNat (MemoryBoundary.address input)) output
  ProverAssumptions input data _ := Domain input ∧ memoryChannel.Guarantees input data
  channelsWithRequirements := [memoryChannel.toRaw]
  soundness := by
    circuit_proof_start [addressCircuit]
    exact h_holds.1
  completeness := by
    circuit_proof_start [addressCircuit]
    exact h_assumptions

/-- Register finalization adds no static lookup table. -/
@[circuit_norm] theorem main_lookups (input : Var MemoryMsg (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).lookups = [] := by
  simp [main, addressCircuit, Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits, circuit_norm]

/-- Every physical interaction supports Boolean row activity without a legacy lookup. -/
instance guardSupported : Guarded.Supported (circuit (p := p)) :=
  Guarded.Supported.of_emitted_requirements _
    (fun input offset => main_lookups input offset)
    (by
      intro selected member
      change selected ∈ [memoryChannel.toRaw, memoryChannel.toRaw] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
      subst selected
      infer_instance)
    (by
      intro input offset selected member outside
      have same : selected = memoryChannel.toRaw := by
        simpa only [circuit, List.mem_singleton] using member
      subst selected
      exact False.elim (outside (by change memoryChannel.toRaw ∈ [memoryChannel.toRaw]; simp)))

end SP1Clean.FinalRegisterProvider
