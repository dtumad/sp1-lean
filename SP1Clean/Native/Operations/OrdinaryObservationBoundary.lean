import SP1Clean.FormalModel.Contracts.OrdinaryObservationBoundary
import Clean.Gadgets.Bits
import Clean.Gadgets.IsZeroField
import ToClean.Circuit.InteractionRecovery
import ToClean.Air.HintIndex

/-! # Terminal of the ordinary observation chain

One terminal row pulls the chain's last observation, checks that its clock is bounded and agrees
with its mode, and pushes the same counter, nextPC and flag at the mode's sentinel clock. The mode
uses two base-65536 carries to normalize the raw successor PC; `nonempty` also witnesses the clock limbs' zero
tests through Clean's bundled `IsZeroField`. The three modes are separate tables, all installed:
the verifier pulls only the sentinel of the mode the target fixes, so another mode's push cannot
balance.
-/

namespace SP1Clean.OrdinaryObservation

open Circuit
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- Each mode's terminal table name. -/
def terminalName : Mode → String
  | .empty => "sp1.native.ordinary_observation.terminal.empty"
  | .nonempty => "sp1.native.ordinary_observation.terminal.nonempty"
  | .any => "sp1.native.ordinary_observation.terminal.any"

/-- The one private routing tag distinguishes an all-zero last observation from an absent hint. -/
def terminalModeHint : String := "sp1.native.ordinary_observation.terminal_mode"

omit [Fact p.Prime] in
private theorem limbBound : 2 ^ 24 < p := by have := Fact.out (p := 2 ^ 25 < p); omega

/-- No ordinary retirement: the last observation is the start, at clock zero. -/
def emptyMain (input : Var TerminalInputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertBool input.carryLow
  assertBool input.carryMiddle
  assertion (Gadgets.ToBits.rangeCheck 24 limbBound) input.previous.clkHigh
  assertion (Gadgets.ToBits.rangeCheck 24 limbBound) input.previous.clkLow
  assertZero input.previous.clkHigh
  assertZero input.previous.clkLow
  stateChannel.pull input.previous
  stateChannel.push (final .empty input.previous.counter input.pc input.previous.enabled)

/-- Some ordinary retirement: the last observation is a receipt, at a nonzero clock. -/
def nonemptyMain (input : Var TerminalInputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertBool input.carryLow
  assertBool input.carryMiddle
  assertion (Gadgets.ToBits.rangeCheck 24 limbBound) input.previous.clkHigh
  assertion (Gadgets.ToBits.rangeCheck 24 limbBound) input.previous.clkLow
  let high ← Gadgets.IsZeroField.circuit input.previous.clkHigh
  let low ← Gadgets.IsZeroField.circuit input.previous.clkLow
  high * low === 0
  stateChannel.pull input.previous
  stateChannel.push (final .nonempty input.previous.counter input.pc input.previous.enabled)

/-- The target's bookkeeping does not distinguish the two cases. -/
def anyMain (input : Var TerminalInputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertBool input.carryLow
  assertBool input.carryMiddle
  assertion (Gadgets.ToBits.rangeCheck 24 limbBound) input.previous.clkHigh
  assertion (Gadgets.ToBits.rangeCheck 24 limbBound) input.previous.clkLow
  stateChannel.pull input.previous
  stateChannel.push (final .any input.previous.counter input.pc input.previous.enabled)

/-- The terminal when the target records no ordinary retirement. -/
def terminalEmpty : GeneralFormalCircuit (ZMod p) TerminalInputs unit where
  name := terminalName .empty
  main := emptyMain
  Spec input _ _ := TerminalInputs.Valid .empty input
  ProverAssumptions input _ _ := TerminalInputs.Valid .empty input
  channelsWithRequirements := [stateChannel.toRaw]
  soundness := by
    circuit_proof_start [emptyMain, Gadgets.ToBits.rangeCheck, assertBool, stateChannel, final, Mode.sentinel, TerminalInputs.Valid, TerminalSpec]
    simp_all
  completeness := by
    circuit_proof_start [emptyMain, Gadgets.ToBits.rangeCheck, assertBool, stateChannel, final, Mode.sentinel, TerminalInputs.Valid, TerminalSpec]
    simp_all

/-- The terminal when the target records at least one ordinary retirement. -/
def terminalNonempty : GeneralFormalCircuit (ZMod p) TerminalInputs unit where
  name := terminalName .nonempty
  main := nonemptyMain
  Spec input _ _ := TerminalInputs.Valid .nonempty input
  ProverAssumptions input _ _ := TerminalInputs.Valid .nonempty input
  channelsWithRequirements := [stateChannel.toRaw]
  soundness := by
    circuit_proof_start [nonemptyMain, Gadgets.ToBits.rangeCheck, Gadgets.IsZeroField.circuit,
      assertBool, stateChannel, final, Mode.sentinel, TerminalInputs.Valid, TerminalSpec]
    obtain ⟨carryLow, carryMiddle, highBound, lowBound, rest⟩ := h_holds
    refine ⟨carryLow, carryMiddle, highBound, lowBound, ?_⟩
    rintro ⟨high, low⟩
    simp_all
    obtain ⟨highZero, lowZero, product | product⟩ := rest <;> simp_all
  completeness := by
    circuit_proof_start [nonemptyMain, Gadgets.ToBits.rangeCheck, Gadgets.IsZeroField.circuit,
      assertBool, stateChannel, final, Mode.sentinel, TerminalInputs.Valid, TerminalSpec]
    obtain ⟨carryLow, carryMiddle, high, low, nonzero⟩ := h_assumptions
    refine ⟨carryLow, carryMiddle, high, low, ?_⟩
    by_cases zero : input_previous_clkHigh = 0 <;> simp_all

/-- The terminal when the target does not distinguish the two cases. -/
def terminalAny : GeneralFormalCircuit (ZMod p) TerminalInputs unit where
  name := terminalName .any
  main := anyMain
  Spec input _ _ := TerminalInputs.Valid .any input
  ProverAssumptions input _ _ := TerminalInputs.Valid .any input
  channelsWithRequirements := [stateChannel.toRaw]
  soundness := by
    circuit_proof_start [anyMain, Gadgets.ToBits.rangeCheck, assertBool, stateChannel, final, Mode.sentinel, TerminalInputs.Valid, TerminalSpec]
    simp_all
  completeness := by
    circuit_proof_start [anyMain, Gadgets.ToBits.rangeCheck, assertBool, stateChannel, final, Mode.sentinel, TerminalInputs.Valid, TerminalSpec]
    simp_all

/-- The terminal for a static mode. -/
def terminal : Mode → GeneralFormalCircuit (ZMod p) TerminalInputs unit
  | .empty => terminalEmpty
  | .nonempty => terminalNonempty
  | .any => terminalAny

/-- Exactly the complete private last observation routes the chain's final occurrence. A valid
chain has one terminal row, so its physical height needs no padding. -/
def terminalGeneration (mode : Mode) : Air.Flat.WitnessGeneration.Generation (ZMod p) TerminalInputs :=
  .demand {
    channel := stateChannel
    trigger := .push
    guard message :=
      let candidate : TerminalInputs (Witgen.FExpr (ZMod p)) :=
        fromElements (Vector.ofFn fun column => .hintGet (terminalName mode) (size TerminalInputs) 0 column)
      .and ((Witgen.FExpr.hintGet terminalModeHint 1 0 0 : Witgen.FExpr (ZMod p)) =?
        Witgen.FExpr.const (mode.sentinel : ZMod p))
        (Witgen.HintIndex.messageEq candidate.previous message)
    input message := do
      let carryLow ← Witgen.letU (message.pc[0].val / 65536)
      let carryMiddle ← Witgen.letU ((message.pc[1].val + carryLow) / 65536)
      pure ⟨fromElements ((toElements (M := State) message).map
        (fun value => Air.Flat.WitnessGeneration.Cell.witness (.expr value))),
        carryLow.toField, carryMiddle.toField⟩
  }

omit [Fact (2 ^ 25 < p)] in
private theorem range_empty (target : RawChannel (ZMod p)) (n : ℕ) (bound : 2 ^ n < p)
    (input : Expression (ZMod p)) (offset : ℕ) :
    (FlatOperation.interactions ((Gadgets.ToBits.rangeCheck n bound).toSubcircuit offset input).ops.toFlat).filter
      (fun (i : AbstractInteraction (ZMod p)) => decide (i.channel = target)) = [] :=
  InteractionRecovery.filter_interactions_formalAssertion_eq_nil
    (Gadgets.ToBits.rangeCheck n bound) target input List.not_mem_nil List.not_mem_nil

/-- Each terminal emits exactly the pull of its last observation and the push of the sentinel. -/
theorem terminal_interactions (mode : Mode) (input : Var TerminalInputs (ZMod p)) (offset : ℕ) :
    (((terminal mode).main input).operations offset).interactionsWith stateChannel.toRaw =
      [(stateChannel.pulled input.previous).toRaw,
        (stateChannel.pushed (final mode input.previous.counter input.pc input.previous.enabled)).toRaw] := by
  have boolEmpty (value : Expression (ZMod p)) (n : ℕ) :
      (FlatOperation.interactions ((assertBool (p := p)).toSubcircuit n value).ops.toFlat).filter
        (fun i => decide (i.channel = stateChannel.toRaw)) = [] :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil
      assertBool stateChannel.toRaw value List.not_mem_nil List.not_mem_nil
  simp only [circuit_norm] at boolEmpty
  cases mode <;>
    simp only [terminal, terminalEmpty, terminalNonempty, terminalAny, emptyMain, nonemptyMain,
      anyMain, circuit_norm, range_empty, boolEmpty, List.nil_append,
      @InteractionRecovery.filter_interactions_formalAssertion_eq_nil (ZMod p) _
        (ProvablePair field field) ProvablePair.instance (Gadgets.Equality.circuit field)
        stateChannel.toRaw _ _ List.not_mem_nil List.not_mem_nil,
      InteractionRecovery.interactionsWith_formalSubcircuit_eq_nil Gadgets.IsZeroField.circuit
        stateChannel.toRaw _ _ List.not_mem_nil List.not_mem_nil]

/-- Every sentinel is strictly later than every bounded observation. -/
theorem terminal_strict {mode : Mode} (input : State (ZMod p)) (valid : TerminalSpec mode input) :
    Semantics.clkNat input.clkHigh input.clkLow <
      Semantics.clkNat (final mode input.counter input.pc input.enabled).clkHigh
        (final mode input.counter input.pc input.enabled).clkLow := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  have sentinel : 2 ^ 24 ≤ (Mode.sentinel (R := ZMod p) mode).val := by
    cases mode <;> simp only [Mode.sentinel] <;> rw [ZMod.val_ofNat_of_lt (lt_trans (by norm_num) hp)] <;> norm_num
  obtain ⟨high, low, _⟩ := valid
  simp only [Semantics.clkNat, final, ZMod.val_zero]
  omega

end SP1Clean.OrdinaryObservation
