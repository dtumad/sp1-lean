import SP1Clean.Proofs.Chips.HostHintReadChip.Ledger
import ToClean.Circuit.Guarded
import ToClean.Air.HintIndex
import ToClean.Air.GuardedDemandTable

/-! # Demand-padded HINT_READ handler

An occupied row consumes the complete guest call and performs its active host effects. An inactive row retains
all physical interaction sites with zero multiplicity and has no constraint on the active child's opcode or clock.
-/

namespace SP1Clean.HostHintReadChip
open Circuit HostHintQueue Air.Flat
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- Original active input followed by its physical activity cell. -/
abbrev RowInput := ProvablePair Inputs field

attribute [local circuit_norm] ClockOrder.circuit ClockOrder.main Gadgets.IsZeroField.circuit
  Gadgets.Equality.circuit Gadgets.Equality.main Gadgets.ToBits.rangeCheck Gadgets.ToBits.toBits Gadgets.ToBits.main
  GeneralFormalCircuit.toSubcircuit_lookups FormalAssertion.toSubcircuit_toFlat
  Operations.lookups_toFlat Operations.lookups Operations.toNested_toFlat FlatOperation.lookups
attribute [local circuit_norm] HintReadSpan.circuit HintReadSpan.main HintReadStep.circuit HintReadStep.main
  AddrAddOperation.circuit AddrAddOperation.main AddressDiv8.circuit AddressDiv8.main AddressOrder.circuit AddressOrder.main
  WordRangeCheck.circuit WordRangeCheck.main
/-- All active handler operations have channel or algebraic semantics compatible with Boolean guarding. -/
instance guardSupported : Guarded.Supported (circuit (p := p)) :=
  Guarded.Supported.of_emitted_requirements _
    (by intro input offset; change ((main input).operations offset).lookups = []; simp [main, circuit_norm, List.ofFn_succ])
    (by
      intro ch present
      have ids : ch = Channels.byteChannel.toRaw ∨ ch = HostCallChip.channel.toRaw ∨ ch = stateChannel.toRaw ∨ ch = nodeChannel.toRaw ∨ ch = wordChannel.toRaw ∨ ch = HintReadWordChip.stateChannel.toRaw := by
        simpa [GeneralFormalCircuit.channels, circuit, elaborated, circuit_norm, or_assoc, or_comm, or_left_comm] using present
      rcases ids with rfl | rfl | rfl | rfl | rfl | rfl <;> infer_instance)
    (by intro _ _ ch req missing _ _; exfalso; apply missing; simp_all [circuit, elaborated, circuit_norm])

/-- Actual demand row circuit, with every child constraint and channel multiplicity behind the activity cell. -/
def guardedCircuit : GeneralFormalCircuit (ZMod p) RowInput unit := Guarded.circuit circuit inferInstance

/-- The indexed hint must carry the entire actual call and have activity one. Clean's zero padding is inactive. -/
def generation : Air.Flat.WitnessGeneration.Generation (ZMod p) RowInput :=
  Witgen.HintIndex.unitDemand (guardedCircuit (p := p)).name HostCallChip.channel .push
    (fun m => m.clk_high.val * 16777216 + m.clk_low.val) (fun input => input.1.call) (fun input => input.2)

/-- Registered component accepting genuine calls and permitting silent padding. -/
def component : Component (ZMod p) where
  circuit := guardedCircuit
  Assumptions := (guardedCircuit).Assumptions
  generation := generation

/-- Generate the physical occupancy and padding rows on the canonical data of this table. -/
def tableFor (rows : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (fit : WitnessGeneration.demandHeight rows.length ≤ UInt64.size) : Table (ZMod p) :=
  Table.ofInputs (component) (WitnessGeneration.guardedRows rows) data
    ((WitnessGeneration.guardedRows_length rows).trans_le fit) (fun _ => trivial)

/-- All active semantics suffice for the padded table, including complete constraints and guarantees
on the extra fourth row of a three-call bucket. -/
theorem tableFor_valid (rows : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (fit : WitnessGeneration.demandHeight rows.length ≤ UInt64.size)
    (honest : ∀ r ∈ rows, ProverAssumptions r) :
    (tableFor rows data fit).Constraints ∧ (tableFor rows data fit).Guarantees := by
  apply Table.ofInputs_valid
  exact WitnessGeneration.guardedRows_all _ honest

/-- The physical handoff keeps one occurrence at every row, with the original call and its checked weight. -/
theorem guarded_host_values (input : Var RowInput (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    (((guardedCircuit).main input).operations offset).interactionValuesWith HostCallChip.channel.toRaw env =
      [HostCallChip.channel.pulledIfValue (env input.2) (Eval.eval env input.1.call)] := by
  change ((Guarded.main (circuit) inferInstance input).operations offset).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  simp only [circuit, host_values, List.map_cons, List.map_nil, Channel.pulledValue, Channel.pulledIfValue, mul_one]

end SP1Clean.HostHintReadChip
