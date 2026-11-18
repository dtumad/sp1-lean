import SP1Clean.FormalModel.Contracts.OrdinaryObservation
import SP1Clean.Native.Operations.InstructionReceipt
import SP1Clean.Native.Operations.ClockOrder
import SP1Clean.Native.Operations.WordRangeCheck
import SP1Clean.Proofs.Operations.AddOperation.Formal
import Clean.Gadgets.Boolean

/-! # Consuming ordinary receipts in strict clock order

Every row consumes one receipt, with no padding selector. The existing clock comparator and
addition gadget establish chronological retirement, including 64-bit counter wraparound. The
increment is the chain's own Boolean retirement flag, so one table serves every segment.
Counter result ranges use the actual Byte ledger; the complete mixed installation must retain
these pulls. Endpoint binding and exhaustive ordering are separate global obligations.
-/

namespace SP1Clean.OrdinaryObservation

open Circuit Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- The existing word gadgets need only the weaker field bound. -/
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- An instruction receipt advances the observation chain and retirement counter by the chain's
Boolean flag. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let _ ← ClockOrder.circuit input.clock
  assertBool input.previous.enabled
  assertion WordRangeCheck.circuit input.previous.counter
  assertion AddOperation.circuit
    ⟨input.previous.counter, increment input.previous.enabled, ⟨input.counter⟩, 1⟩
  InstructionReceipt.channel.pull input.receipt
  stateChannel.pull input.previous
  stateChannel.push input.next

/-- Compose the original gadgets' metadata without a second arithmetic implementation. -/
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by
  elaborate_circuit

omit [Fact (2 ^ 25 < p)] in
/-- A Boolean flag is a bounded increment word. -/
theorem increment_isU64 {enabled : ZMod p} (flag : IsBool enabled) : Word.isU64 (increment enabled) := by
  rcases flag with rfl | rfl <;> apply Word.isU64_of_cases <;> norm_num [increment, ZMod.val_one]

omit [Fact (2 ^ 25 < p)] in
/-- The limb encoding denotes the flag's value as the counter increment. -/
theorem increment_bits (enabled : ZMod p) :
    Word.toBitVec64 (increment enabled) = BitVec.ofNat 64 enabled.val := by
  simp [increment, Word.toBitVec64, Word.toNat]

omit [Fact (2 ^ 25 < p)] in
private theorem eval_increment (enabled : Expression (ZMod p)) (env : Environment (ZMod p)) :
    Eval.eval env (increment enabled) = increment (Eval.eval env enabled) := by
  simp only [increment, circuit_norm]

/-- Local arithmetic and ordering follow from the composed circuit contracts. -/
theorem soundness :
    GeneralFormalCircuit.Soundness (Output := unit) (ZMod p) main
      (fun _ _ => True) (fun input _ _ => Spec input) := by
  circuit_proof_start [ClockOrder.circuit, assertBool, WordRangeCheck.circuit, WordRangeCheck.Spec,
    WordRangeCheck.Assumptions, AddOperation.circuit, Inputs.clock,
    InstructionReceipt.channel, stateChannel, eval_increment]
  obtain ⟨clock, flag, previous, addition⟩ := h_holds
  have result := addition ⟨fun _ => ⟨previous, increment_isU64 flag⟩, Or.inr rfl⟩ rfl
  exact ⟨clock, flag, previous, result.1, by simpa only [increment_bits] using result.2⟩

/-- Any semantic observation update supplies the existing gadgets' completeness premises. -/
theorem completeness :
    GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) main
      (fun input _ _ => Spec input) (fun _ _ _ => True) := by
  circuit_proof_start [ClockOrder.circuit, assertBool, WordRangeCheck.circuit, WordRangeCheck.Spec,
    WordRangeCheck.Assumptions, AddOperation.circuit, Inputs.clock,
    InstructionReceipt.channel, stateChannel, eval_increment]
  obtain ⟨clock, flag, previous, bounded, addition⟩ := h_assumptions
  refine ⟨clock, flag, previous, ?_⟩
  exact ⟨⟨fun _ => ⟨previous, increment_isU64 flag⟩, Or.inr rfl⟩,
    fun _ => ⟨bounded, by simpa only [increment_bits] using addition⟩⟩

/-- A complete local observation contract with explicit receipt and state-link requirements. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := "sp1.native.ordinary_observation"
  main := main
  computableWitnesses := by computable_witnesses [Inputs.clock, increment]
  elaborated := elaborated
  Spec input _ _ := Spec input
  ProverAssumptions input _ _ := Spec input
  soundness := soundness
  completeness := completeness
  channelsWithRequirements := [InstructionReceipt.channel.toRaw, stateChannel.toRaw]

/-- The consumer uses only the Byte channel, the receipt protocol and its observation links. -/
theorem circuit_channels_subset :
    (circuit (p := p)).channels ⊆
      [Channels.byteChannel.toRaw, InstructionReceipt.channel.toRaw, stateChannel.toRaw] := by
  intro channel member
  have channels : (circuit (p := p)).channels =
      [Channels.byteChannel.toRaw, Channels.byteChannel.toRaw, Channels.byteChannel.toRaw,
        Channels.byteChannel.toRaw, InstructionReceipt.channel.toRaw, stateChannel.toRaw,
        InstructionReceipt.channel.toRaw, stateChannel.toRaw] := rfl
  rw [channels] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
  tauto

/-- Data-only construction uses the existing addition population algorithm. -/
def populate (previous : State (ZMod p)) (receipt : StateMsg (ZMod p)) : Inputs (ZMod p) :=
  ⟨receipt, previous, AddOperation.populate previous.counter (increment previous.enabled)⟩

/-- Population is total for any Boolean-flagged, bounded incoming counter and strictly
increasing source clock. -/
theorem populate_spec (previous : State (ZMod p)) (receipt : StateMsg (ZMod p))
    (flag : IsBool previous.enabled) (bounded : Word.isU64 previous.counter)
    (clock : ClockOrder.Spec (populate previous receipt).clock) :
    Spec (populate previous receipt) := by
  have result := AddOperation.spec_populate bounded (increment_isU64 flag) 1 rfl
  exact ⟨clock, flag, bounded, result.1, by simpa only [increment_bits, populate] using result.2⟩

/-- Recovering the source clock does not hide field wraparound. The successor low limb may
exceed the 24-bit window by up to seven; it still equals the recovered source plus eight in ℕ. -/
theorem receipt_clock (input : Inputs (ZMod p)) (valid : Spec input) :
    input.receipt.clk_high.val < 2 ^ 24 ∧
      input.receipt.clk_low.val = (input.receipt.clk_low - 8).val + 8 := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  have low := valid.1.2.2.2.1
  change (input.receipt.clk_low - 8).val < 2 ^ 24 at low
  refine ⟨valid.1.2.2.1, ?_⟩
  have eight : (8 : ZMod p).val = 8 := ZMod.val_natCast_of_lt (n := p) (a := 8) (by omega)
  have sum := ZMod.val_add_of_lt (a := input.receipt.clk_low - 8) (b := (8 : ZMod p))
    (by rw [eight]; omega)
  simpa only [sub_add_cancel, eight] using sum

end SP1Clean.OrdinaryObservation
