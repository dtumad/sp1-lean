import SP1Clean.FormalModel.Contracts.FinalRamValue
import SP1Clean.Native.Operations.InitialMemoryRead
import Clean.Gadgets.Equality
import SP1Clean.Math.WordEquality
import ToClean.Circuit.InteractionRecovery

/-! # Target RAM authentication through the shared byte-read circuit

All eight target bytes are checked, including unchanged bytes in a partially written word.
The fixed target table has a distinct export name from the incoming memory table.
-/

namespace SP1Clean.FinalRamValue

open Circuit Model.Core Channels Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def main (target : MemorySnapshot) (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let value ← InitialMemoryRead.circuitNamed target.memory "sp1.native.target_memory" input.read
  assertion (Gadgets.Equality.circuit Word) (input.read.bytes[0].address, MemoryBoundary.address input.record)
  assertion (Gadgets.Equality.circuit Word) (value, input.record.value)
  (FinalMemoryValue.channel true).pull input.record

instance elaborated (target : MemorySnapshot) :
    ElaboratedCircuit (ZMod p) Inputs unit (main target) := by elaborate_circuit

theorem receipt_values (target : MemorySnapshot) (input : Var Inputs (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p)) :
    ((main target input).operations offset).interactionValuesWith (FinalMemoryValue.channel true).toRaw env =
      [(FinalMemoryValue.channel true).pulledValue (eval env input.record)] := by
  have readEmpty (n : ℕ) := InteractionRecovery.interactionsWith_main_eq_nil
    (InitialMemoryRead.circuitNamed target.memory "sp1.native.target_memory").base
    (FinalMemoryValue.channel true).toRaw input.read n (by
      simp [circuit_norm, FinalMemoryValue.channel, byteChannel, Channel.toRaw])
  have equalEmpty (left right : Var Word (ZMod p)) (n : ℕ) :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil (Gadgets.Equality.circuit Word)
      (FinalMemoryValue.channel true).toRaw (left, right) (by simp [circuit_norm])
      (by simp [circuit_norm]) (n := n)
  have raw : ((main target input).operations offset).interactionsWith (FinalMemoryValue.channel true).toRaw =
      [((FinalMemoryValue.channel true).pulled input.record).toRaw] := by
    simp only [main, circuit_norm, equalEmpty, List.nil_append]
    simp only [Operations.interactionsWith] at readEmpty ⊢
    simp only [GeneralFormalCircuit.toSubcircuit_interactions, readEmpty, List.nil_append]
  rw [Operations.interactionValuesWith, raw]
  exact congrArg (fun value => [value]) Channel.eval_pulled

def circuit (target : MemorySnapshot) : GeneralFormalCircuit (ZMod p) Inputs unit where
  main := main target
  elaborated := elaborated target
  Spec input _ _ := Spec target input.record
  ProverAssumptions input _ _ :=
    InitialMemoryRead.ProverAssumptions target.memory input.read ∧
      input.read.bytes[0].address = MemoryBoundary.address input.record ∧
      Word.ofBytes (input.read.bytes.map fun byte => byte.interval.value) = input.record.value
  channelsWithRequirements := [(FinalMemoryValue.channel true).toRaw]
  soundness := by
    circuit_proof_start [InitialMemoryRead.circuitNamed, Gadgets.Equality.circuit,
      FinalMemoryValue.channel, MemoryBoundary.address]
    rw [InitialMemoryRead.eval_base env _ _ h_input.2] at h_holds
    obtain ⟨read, address, value⟩ := h_holds
    have addressWord : input_read_bytes[0].address =
        #v[input_record_addr0, input_record_addr1, input_record_addr2, 0] := by
      exact Vector.toArray_inj.mp address
    simpa only [InitialMemoryRead.Spec, addressWord, value] using read
  completeness := by
    circuit_proof_start [InitialMemoryRead.circuitNamed, Gadgets.Equality.circuit,
      FinalMemoryValue.channel, MemoryBoundary.address]
    rw [InitialMemoryRead.eval_base env.toEnvironment _ _ h_input.2]
    exact ⟨h_assumptions.1, h_assumptions.2.1,
      (InitialMemoryRead.eval_result env.toEnvironment _ _ h_input.2).trans h_assumptions.2.2⟩

instance (target : MemorySnapshot) (record : MemoryMsg (ZMod p)) : Decidable (Spec target record) := by
  unfold Spec Word.isU64
  infer_instance

/-- All interval selections and comparisons are computed from the supplied target and record. -/
def populate? (target : MemorySnapshot) (record : MemoryMsg (ZMod p)) : Option (Inputs (ZMod p)) :=
  if Spec target record then
    some ⟨record, InitialMemoryRead.populate target.memory (Word.toNat (MemoryBoundary.address record))⟩
  else none

omit [Fact (2 ^ 17 < p)] in
theorem populate?_isSome_iff (target : MemorySnapshot) (record : MemoryMsg (ZMod p)) :
    (populate? target record).isSome = true ↔ Spec target record := by
  unfold populate?
  split <;> simp_all

theorem populate?_sound (target : MemorySnapshot) (record : MemoryMsg (ZMod p))
    (input : Inputs (ZMod p)) (found : populate? target record = some input)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (circuit target).ProverAssumptions input data hint ∧ input.record = record := by
  unfold populate? at found
  split at found
  next valid =>
    obtain rfl := Option.some.inj found
    have constructed := InitialMemoryRead.populate?_sound (p := p) target.memory
      (Word.toNat (MemoryBoundary.address record))
      (InitialMemoryRead.populate target.memory (Word.toNat (MemoryBoundary.address record)))
      (by simp only [InitialMemoryRead.populate?, if_pos valid.2.1])
    have read := constructed.1.spec target.memory _
    refine ⟨⟨constructed.1, Word.eq_of_toNat_eq read.1 valid.1 constructed.2, ?_⟩, rfl⟩
    apply Word.eq_of_toBitVec64_eq read.2.2.1 valid.2.2.1
    rw [read.2.2.2, constructed.2, valid.2.2.2]
  next invalid => contradiction

end SP1Clean.FinalRamValue
