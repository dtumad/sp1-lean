import SP1Clean.FormalModel.Contracts.OrdinaryObservationBoundary
import Clean.Gadgets.Bits
import Clean.Gadgets.IsZeroField
import ToClean.Circuit.InteractionRecovery
import ToClean.Air.HintIndex

/-! # Terminal of the ordinary observation chain

One terminal row pulls the chain's last observation, checks that its clock is bounded and agrees
with the static mode, and pushes the same counter and nextPC at the sentinel clock `2^48`. The
mode needs no extra column when it is `empty` or `any`; `nonempty` witnesses the two clock limbs'
zero tests through Clean's bundled `IsZeroField`. The three modes are separate circuits, so each
has fully elaborated metadata.
-/

namespace SP1Clean.OrdinaryObservation

open Circuit
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- The terminal's table name, shared by the three modes. -/
def terminalName : String := "sp1.native.ordinary_observation.terminal"

omit [Fact p.Prime] in
private theorem limbBound : 2 ^ 24 < p := by have := Fact.out (p := 2 ^ 25 < p); omega

/-- No ordinary retirement: the last observation is the start, at clock zero. -/
def emptyMain (input : Var State (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion (Gadgets.ToBits.rangeCheck 24 limbBound) input.clkHigh
  assertion (Gadgets.ToBits.rangeCheck 24 limbBound) input.clkLow
  assertZero input.clkHigh
  assertZero input.clkLow
  stateChannel.pull input
  stateChannel.push (final input.counter input.pc)

/-- Some ordinary retirement: the last observation is a receipt, at a nonzero clock. -/
def nonemptyMain (input : Var State (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion (Gadgets.ToBits.rangeCheck 24 limbBound) input.clkHigh
  assertion (Gadgets.ToBits.rangeCheck 24 limbBound) input.clkLow
  let high ← Gadgets.IsZeroField.circuit input.clkHigh
  let low ← Gadgets.IsZeroField.circuit input.clkLow
  high * low === 0
  stateChannel.pull input
  stateChannel.push (final input.counter input.pc)

/-- The target's bookkeeping does not distinguish the two cases. -/
def anyMain (input : Var State (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion (Gadgets.ToBits.rangeCheck 24 limbBound) input.clkHigh
  assertion (Gadgets.ToBits.rangeCheck 24 limbBound) input.clkLow
  stateChannel.pull input
  stateChannel.push (final input.counter input.pc)

/-- The terminal when the target records no ordinary retirement. -/
def terminalEmpty : GeneralFormalCircuit (ZMod p) State unit where
  name := terminalName
  main := emptyMain
  Spec input _ _ := TerminalSpec .empty input
  ProverAssumptions input _ _ := TerminalSpec .empty input
  channelsWithRequirements := [stateChannel.toRaw]
  soundness := by
    circuit_proof_start [emptyMain, Gadgets.ToBits.rangeCheck, stateChannel, final, TerminalSpec]
    simp_all
  completeness := by
    circuit_proof_start [emptyMain, Gadgets.ToBits.rangeCheck, stateChannel, final, TerminalSpec]
    simp_all

/-- The terminal when the target records at least one ordinary retirement. -/
def terminalNonempty : GeneralFormalCircuit (ZMod p) State unit where
  name := terminalName
  main := nonemptyMain
  Spec input _ _ := TerminalSpec .nonempty input
  ProverAssumptions input _ _ := TerminalSpec .nonempty input
  channelsWithRequirements := [stateChannel.toRaw]
  soundness := by
    circuit_proof_start [nonemptyMain, Gadgets.ToBits.rangeCheck, Gadgets.IsZeroField.circuit,
      stateChannel, final, TerminalSpec]
    refine ⟨h_holds.1, h_holds.2.1, ?_⟩
    rintro ⟨high, low⟩
    simp_all
    obtain ⟨highZero, lowZero, product | product⟩ := h_holds <;> simp_all
  completeness := by
    circuit_proof_start [nonemptyMain, Gadgets.ToBits.rangeCheck, Gadgets.IsZeroField.circuit,
      stateChannel, final, TerminalSpec]
    obtain ⟨high, low, nonzero⟩ := h_assumptions
    refine ⟨high, low, ?_⟩
    by_cases zero : input_clkHigh = 0 <;> simp_all

/-- The terminal when the target does not distinguish the two cases. -/
def terminalAny : GeneralFormalCircuit (ZMod p) State unit where
  name := terminalName
  main := anyMain
  Spec input _ _ := TerminalSpec .any input
  ProverAssumptions input _ _ := TerminalSpec .any input
  channelsWithRequirements := [stateChannel.toRaw]
  soundness := by
    circuit_proof_start [anyMain, Gadgets.ToBits.rangeCheck, stateChannel, final, TerminalSpec]
    simp_all
  completeness := by
    circuit_proof_start [anyMain, Gadgets.ToBits.rangeCheck, stateChannel, final, TerminalSpec]
    simp_all

/-- The terminal for a static mode. -/
def terminal : Mode → GeneralFormalCircuit (ZMod p) State unit
  | .empty => terminalEmpty
  | .nonempty => terminalNonempty
  | .any => terminalAny

/-- Exactly the complete private last observation routes the chain's final occurrence. A valid
chain has one terminal row, so its physical height needs no padding. -/
def terminalGeneration : Air.Flat.WitnessGeneration.Generation (ZMod p) State :=
  .demand {
    channel := stateChannel
    trigger := .push
    guard message :=
      let candidate : State (Witgen.FExpr (ZMod p)) :=
        fromElements (Vector.ofFn fun column => .hintGet terminalName (size State) 0 column)
      Witgen.HintIndex.messageEq candidate message
    input message := pure (fromElements ((toElements (M := State) message).map
      (fun value => Air.Flat.WitnessGeneration.Cell.witness (.expr value))))
  }

omit [Fact (2 ^ 25 < p)] in
private theorem range_empty (target : RawChannel (ZMod p)) (n : ℕ) (bound : 2 ^ n < p)
    (input : Expression (ZMod p)) (offset : ℕ) :
    (FlatOperation.interactions ((Gadgets.ToBits.rangeCheck n bound).toSubcircuit offset input).ops.toFlat).filter
      (fun (i : AbstractInteraction (ZMod p)) => decide (i.channel = target)) = [] :=
  InteractionRecovery.filter_interactions_formalAssertion_eq_nil
    (Gadgets.ToBits.rangeCheck n bound) target input List.not_mem_nil List.not_mem_nil

/-- Each terminal emits exactly the pull of its last observation and the push of the sentinel. -/
theorem terminal_interactions (mode : Mode) (input : Var State (ZMod p)) (offset : ℕ) :
    (((terminal mode).main input).operations offset).interactionsWith stateChannel.toRaw =
      [(stateChannel.pulled input).toRaw, (stateChannel.pushed (final input.counter input.pc)).toRaw] := by
  cases mode <;>
    simp only [terminal, terminalEmpty, terminalNonempty, terminalAny, emptyMain, nonemptyMain,
      anyMain, circuit_norm, range_empty, List.nil_append,
      @InteractionRecovery.filter_interactions_formalAssertion_eq_nil (ZMod p) _
        (ProvablePair field field) ProvablePair.instance (Gadgets.Equality.circuit field)
        stateChannel.toRaw _ _ List.not_mem_nil List.not_mem_nil,
      InteractionRecovery.interactionsWith_formalSubcircuit_eq_nil Gadgets.IsZeroField.circuit
        stateChannel.toRaw _ _ List.not_mem_nil List.not_mem_nil]

/-- The sentinel is strictly later than every bounded observation. -/
theorem terminal_strict {mode : Mode} (input : State (ZMod p)) (valid : TerminalSpec mode input) :
    Semantics.clkNat input.clkHigh input.clkLow <
      Semantics.clkNat (final input.counter input.pc).clkHigh (final input.counter input.pc).clkLow := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  have sentinel : (16777216 : ZMod p).val = 2 ^ 24 := by
    change ((16777216 : ℕ) : ZMod p).val = 2 ^ 24
    rw [ZMod.val_natCast_of_lt (by omega)]
    norm_num
  simp only [Semantics.clkNat, final, sentinel, ZMod.val_zero]
  obtain ⟨high, low, _⟩ := valid
  omega

end SP1Clean.OrdinaryObservation
