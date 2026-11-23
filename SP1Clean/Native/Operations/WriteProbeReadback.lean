import SP1Clean.FormalModel.Contracts.WriteReadback
import ToClean.Circuit.EmittedInteraction
import Clean.Air.FlatComponent
import Clean.Gadgets.Boolean
import SP1Clean.Semantics.Transition.MicroTime
import SP1Clean.Native.Operations.ClockParts
import ToClean.Air.HintIndex

/-! # Supplying true intervals from read-back receipts

One row consumes each mandatory source receipt, even if its query count is zero. Active output
multiplicity may fund repeated probes. The circuit checks 16/8/8/16-bit pieces so the two
24-bit Memory limbs and the three 16-bit version limbs represent the same natural timestamp.
A read-back preserves the word at both ends of the closed interval.
-/

namespace SP1Clean.WriteProbe.ReadbackSupply

open Circuit Air.Flat Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- Input records have no independent clock or version columns. Both messages use these same cells. -/
structure Inputs (F : Type) where
  /-- The complete Memory address copied from the source. -/
  key : fields 3 F
  /-- Split lower endpoint. -/
  previous : ClockParts F
  /-- Split upper endpoint. -/
  current : ClockParts F
  /-- Word copied verbatim from the source receipt. -/
  value : Word F
  /-- One for a genuine receipt and zero for padding. -/
  active : F
  /-- Number of private version queries funded by this row. -/
  count : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- Original receipt reconstructed in the Memory bus clock layout. -/
def Inputs.receipt {F} [Add F] [Mul F] [OfNat F 256] [OfNat F 65536] (r : Inputs F) : Readback F :=
  ⟨r.key, r.previous.high24, r.previous.low24, r.current.high24, r.current.low24, r.value⟩

/-- Probe version using the same clock chunks, address and word. -/
def Inputs.version {F} [Add F] [Mul F] [OfNat F 256] (r : Inputs F) : Version F :=
  ⟨r.key, r.previous.address, r.current.address, r.value⟩

/-- Binary activity, disabled counts and canonical clock chunks for one physical row. -/
def Valid (r : Inputs (ZMod p)) : Prop :=
  (r.active = 0 ∨ r.active = 1) ∧ (r.active = 0 → r.count = 0) ∧
    r.previous.Bounded ∧ r.current.Bounded

/-- Consume an active source and publish its converted version with the chosen count. -/
def main (r : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertZero (r.active * (r.active - 1))
  assertZero ((1 - r.active) * r.count)
  assertion ClockParts.circuit r.previous
  assertion ClockParts.circuit r.current
  readbackChannel.pullIf r.active r.receipt
  versionChannel.emit r.count r.version

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by
  unfold main
  elaborate_circuit_with { channelsWithGuarantees := [readbackChannel.toRaw] }

/-- Local checker for distributing a genuine read-back version at any query count. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := "sp1.native.write_readback_supply"
  main
  elaborated
  channelsWithRequirements := [versionChannel.toRaw]
  Spec r _ _ := Valid r
  ProverAssumptions r _ _ := Valid r
  soundness := by
    circuit_proof_start [main, ClockParts.circuit, Valid,
      readbackChannel, versionChannel]
    obtain ⟨binary, count, previous, current⟩ := h_holds
    have bit := bool_of_mul_pred binary
    exact ⟨⟨bit, fun zero => by simpa [zero] using count, previous, current⟩, bit⟩
  completeness := by
    circuit_proof_start [main, ClockParts.circuit, Valid,
      readbackChannel, versionChannel]
    obtain ⟨binary, count, previous, current⟩ := h_assumptions
    refine ⟨?_, ?_, previous, current⟩
    · rcases binary with off | on <;> simp [*]
    · rcases binary with off | on
      · simp [off, count off]
      · simp [on]
  requirementsChannelsLawful input offset := by
    preserve_tactic_target
    simp only [main, ClockParts.circuit, circuit_norm, readbackChannel, versionChannel]
    constructor
    · intro ch member
      rcases member with rfl | rfl
      · exact Or.inl List.mem_cons_self
      · exact Or.inr rfl
    · intro env checked
      exact bool_of_mul_pred checked.1

/-- A counted supply row has a mandatory original receipt with the same address and unchanged
word, and the closed interval is the actual pair of natural Memory timestamps. -/
theorem Valid.counted {r : Inputs (ZMod p)} (valid : Valid r) (counted : r.count ≠ 0) :
    r.active = 1 ∧ r.version.key = r.receipt.key ∧ r.version.value = r.receipt.value ∧
      Address.toNat r.version.lower = clkNat r.receipt.previousHigh r.receipt.previousLow ∧
      Address.toNat r.version.upper = clkNat r.receipt.currentHigh r.receipt.currentLow :=
  ⟨valid.1.resolve_left (fun off => counted (valid.2.1 off)), rfl, rfl,
    r.previous.time valid.2.2.1, r.current.time valid.2.2.2⟩

/-- Query multiplicity is the only freely selected datum of an active source row. -/
def populate (record : Readback (ZMod p)) (count : ZMod p) : Inputs (ZMod p) :=
  ⟨record.key, .split record.previousHigh record.previousLow, .split record.currentHigh record.currentLow,
    record.value, 1, count⟩

/-- Every genuine bounded receipt yields a valid physical source and reconstructs all its fields. -/
theorem populate_valid (record : Readback (ZMod p)) (count : ZMod p)
    (ph : record.previousHigh.val < 2 ^ 24) (pl : record.previousLow.val < 2 ^ 24)
    (ch : record.currentHigh.val < 2 ^ 24) (cl : record.currentLow.val < 2 ^ 24) :
    Valid (populate record count) ∧ (populate record count).receipt = record := by
  obtain ⟨previous, high, low⟩ := ClockParts.split_spec _ _ ph pl
  obtain ⟨current, high', low'⟩ := ClockParts.split_spec _ _ ch cl
  exact ⟨⟨Or.inr rfl, fun impossible => (one_ne_zero impossible).elim, previous, current⟩, by
    cases record
    simp only [populate, Inputs.receipt, high, low, high', low']⟩

private def splitFE (hi lo : Expression (ZMod p)) : ClockParts (Witgen.FExpr (ZMod p)) :=
  ⟨(lo.val % 65536).toField, (lo.val / 65536).toField, (hi.val % 256).toField, (hi.val / 256).toField⟩

/-- Every genuine receipt is consumed exactly once by the normal scheduler. The private
count index uses the full original receipt as a tuple, including its value and both clocks. -/
def generation : WitnessGeneration.Generation (ZMod p) Inputs :=
  .demand {
    channel := readbackChannel
    trigger := .push
    input msg := do
      let keys := (toElements (M := Readback) msg).toList.map (·.val)
      let count := Witgen.HintIndex.inputKeys (Input := field) "sp1.native.write_readback_counts" keys
      let input : Inputs (Witgen.FExpr (ZMod p)) :=
        ⟨msg.key.map Witgen.FExpr.expr, splitFE msg.previousHigh msg.previousLow, splitFE msg.currentHigh msg.currentLow,
          msg.value.map Witgen.FExpr.expr, 1, count⟩
      pure (fromElements ((toElements input).map WitnessGeneration.Cell.witness))
  }

/-- The source component has its own scheduler and local physical checks. -/
def component : Component (ZMod p) :=
  { circuit, generation, Assumptions := circuit.Assumptions }

end SP1Clean.WriteProbe.ReadbackSupply
