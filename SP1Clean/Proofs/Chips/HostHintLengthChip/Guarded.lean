import SP1Clean.Proofs.Chips.HostHintLengthChip.Ledger
import ToClean.Circuit.Guarded
import ToClean.Air.HintIndex
import ToClean.Air.GuardedDemandTable

/-! # Demand-padded HINT_LEN handler

An occupied row consumes the complete guest call and performs its active host effects. An inactive row retains
all physical interaction sites with zero multiplicity and has no constraint on the active child's opcode or clock.
-/

namespace SP1Clean.HostHintLengthChip
open Circuit HostHintQueue Air.Flat
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- Original active input followed by its physical activity cell. -/
abbrev RowInput := ProvablePair Inputs field

attribute [local circuit_norm] ClockOrder.circuit ClockOrder.main Gadgets.IsZeroField.circuit
  Gadgets.Equality.circuit Gadgets.Equality.main Gadgets.ToBits.rangeCheck Gadgets.ToBits.toBits Gadgets.ToBits.main
  GeneralFormalCircuit.toSubcircuit_lookups FormalAssertion.toSubcircuit_toFlat
  Operations.lookups_toFlat Operations.lookups Operations.toNested_toFlat FlatOperation.lookups

/-- All active handler operations have channel or algebraic semantics compatible with Boolean guarding. -/
instance guardSupported (empty : Bool) : Guarded.Supported (circuit (p := p) empty) :=
  Guarded.Supported.of_emitted_requirements _
    (by intro input offset; change ((main empty input).operations offset).lookups = []; cases empty <;> simp [main, circuit_norm, List.ofFn_succ])
    (by
      intro ch present
      have ids : ch = HostCallChip.channel.toRaw ∨ ch = stateChannel.toRaw ∨ ch = nodeChannel.toRaw := by
        cases empty <;> simp [GeneralFormalCircuit.channels, circuit, elaborated, circuit_norm] at present <;> tauto
      rcases ids with rfl | rfl | rfl <;> infer_instance)
    (by intro _ _ ch req missing _ _; exfalso; apply missing; cases empty <;> simp_all [circuit, elaborated, circuit_norm])

/-- Actual demand row circuit, with every child constraint and channel multiplicity behind the activity cell. -/
def guardedCircuit (empty : Bool) : GeneralFormalCircuit (ZMod p) RowInput unit := Guarded.circuit (circuit empty) inferInstance

/-- The indexed hint must carry the entire actual call and have activity one. Clean's zero padding is inactive. -/
def generation (empty : Bool) : Air.Flat.WitnessGeneration.Generation (ZMod p) RowInput :=
  Witgen.HintIndex.unitDemand (guardedCircuit (p := p) empty).name HostCallChip.channel .push
    (fun m => m.clk_high.val * 16777216 + m.clk_low.val) (fun input => input.1.call) (fun input => input.2)

/-- Registered component accepting genuine calls and permitting silent padding. -/
def component (empty : Bool) : Component (ZMod p) where
  circuit := guardedCircuit empty
  Assumptions := (guardedCircuit empty).Assumptions
  generation := generation empty

/-- Generate the physical occupancy and padding rows on the canonical data of this table. -/
def tableFor (empty : Bool) (rows : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (fit : WitnessGeneration.demandHeight rows.length ≤ UInt64.size) : Table (ZMod p) :=
  Table.ofInputs (component empty) (WitnessGeneration.guardedRows rows) data
    ((WitnessGeneration.guardedRows_length rows).trans_le fit) (fun _ => trivial)

/-- All active semantics suffice for the padded table, including complete constraints and guarantees
on the extra fourth row of a three-call bucket. -/
theorem tableFor_valid (empty : Bool) (rows : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (fit : WitnessGeneration.demandHeight rows.length ≤ UInt64.size)
    (honest : ∀ r ∈ rows, Spec empty r) :
    (tableFor empty rows data fit).Constraints ∧ (tableFor empty rows data fit).Guarantees := by
  apply Table.ofInputs_valid
  exact WitnessGeneration.guardedRows_all _ honest

/-- The physical handoff keeps one occurrence at every row, with the original call and its checked weight. -/
theorem guarded_host_values (empty : Bool) (input : Var RowInput (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    (((guardedCircuit empty).main input).operations offset).interactionValuesWith HostCallChip.channel.toRaw env =
      [HostCallChip.channel.pulledIfValue (env input.2) (Eval.eval env input.1.call)] := by
  change ((Guarded.main (circuit empty) inferInstance input).operations offset).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  simp only [circuit, host_values, List.map_cons, List.map_nil, Channel.pulledValue, Channel.pulledIfValue, mul_one]

end SP1Clean.HostHintLengthChip
