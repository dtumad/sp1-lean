import SP1Clean.Proofs.Operations.WriteProbe
import ToClean.Circuit.Guarded
import ToClean.Air.HintIndex
import ToClean.Air.ChannelClosure
import Clean.Air.FlatComponent

/-! # Physical WRITE probe component and its private ledger

A live row consumes a complete interval and supplies exactly one host probe receipt.
The activity selector silences both occurrences on padding. No public channel or
guest State/Memory interaction enters the row.
-/

namespace SP1Clean.WriteProbe

open Circuit Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- All auxiliary ordering, bit, and division subcircuits are channel-free. -/
theorem main_interactions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactions =
      [(versionChannel.pulled input.version).toRaw, (readChannel.pushed input.read).toRaw] := by
  simp [main, circuit_norm, AddressDiv8.circuit, AddressDiv8.main, WordRangeCheck.circuit, WordRangeCheck.main,
    AddressOrder.circuit, AddressOrder.main, Gadgets.IsZeroField.circuit, Gadgets.Equality.main,
    Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits, Gadgets.ToBits.main, Operations.interactions,
    FormalAssertion.toSubcircuit_interactions, FormalCircuit.toSubcircuit_interactions,
    GeneralFormalCircuit.toSubcircuit_interactions]

instance guardSupported : Guarded.Supported (circuit (p := p)) where
  noLookups := by
    intro input offset
    simp [circuit, main, circuit_norm, AddressDiv8.circuit, AddressDiv8.main, WordRangeCheck.circuit,
      WordRangeCheck.main, AddressOrder.circuit, AddressOrder.main, Gadgets.IsZeroField.circuit,
      Gadgets.Equality.main, Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits, Gadgets.ToBits.main,
      Operations.lookups]
  channelsNeutral := by
    intro selected member
    change selected ∈ [versionChannel.toRaw, (readChannel (p := p)).toRaw] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> infer_instance
  declared := by
    intro input offset interaction member carries
    rw [GeneralFormalCircuit.toSubcircuit_interactions] at member
    change interaction ∈ ((main input).operations offset).interactions at member
    rw [main_interactions] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · simp [circuit, elaborated, circuit_norm]
    · contradiction

/-- Guarded physical row format, with unit multiplicity for each active occurrence. -/
abbrev RowInput := ProvablePair Inputs field

/-- Active and padding rows share a single table. -/
def guarded : GeneralFormalCircuit (ZMod p) RowInput unit :=
  Guarded.circuit circuit guardSupported

/-- The flat row constraints force Boolean activity and the checked observation contract for
every live row. The private version bus has a structural payload; the provider supplies its value. -/
theorem guarded_spec_of_constraints (input : Var RowInput (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (checked : ((guarded.main input).operations offset).ConstraintsHold env) :
    IsBool (eval env input).2 ∧ ((eval env input).2 = 1 → Spec (eval env input).1) := by
  apply (guarded.original_full_soundness offset env input (fun _ => trivial) checked ?_).1
  rw [Operations.guarantees_iff _ _ _ (guarded.in_channels_or_guarantees_full input offset env)]
  intro selected member
  change selected ∈ [versionChannel.toRaw] at member
  obtain rfl := List.mem_singleton.mp member
  exact Operations.channelGuarantees_of_trivial _ (by simp [versionChannel, Channel.toRaw]) _ _

/-- Route requests by their absolute clock and location. The built-in demand guard checks
the whole read receipt, including its four-limb value, before accepting a private input. -/
def generation : WitnessGeneration.Generation (ZMod p) RowInput :=
  Witgen.HintIndex.unitDemandKeys (guarded (p := p)).name readChannel .pull
    (fun read => [read.clock[0].val + read.clock[1].val * 65536 + read.clock[2].val * 4294967296,
      read.key[0].val + read.key[1].val * 65536 + read.key[2].val * 4294967296])
    (fun input => input.1.read) (fun input => input.2)

/-- Physical native observation component for installation on the private read/version buses. -/
def component : Component (ZMod p) where
  circuit := guarded
  generation := generation
  Assumptions := guarded.Assumptions
  circuit_assumptions_of_assumptions := fun _ _ _ _ _ assumed => assumed

omit [Fact (2 ^ 17 < p)] in
private theorem eval_read (env : Environment (ZMod p)) (input : Var Inputs (ZMod p)) :
    Eval.eval env input.read = (ProvableStruct.eval env input).read := by
  rcases input with ⟨⟨_, _, _, _⟩, _, _⟩
  simp only [Inputs.read, circuit_norm]

private theorem version_values (input : Var Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main input).operations offset).interactionValuesWith versionChannel.toRaw env =
      [versionChannel.pulledValue (eval env input.version)] := by
  have occurrences : ((main input).operations offset).interactionsWith versionChannel.toRaw =
      [(versionChannel.pulled input.version).toRaw] := by
    rw [Operations.interactionsWith, main_interactions]
    simp [versionChannel, readChannel, Channel.toRaw, circuit_norm]
  rw [Operations.interactionValuesWith, occurrences]
  simp only [List.map_cons, List.map_nil, Channel.eval_pulled]

private theorem read_values (input : Var Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main input).operations offset).interactionValuesWith readChannel.toRaw env =
      [readChannel.pushedValue (ProvableStruct.eval env input).read] := by
  have occurrences : ((main input).operations offset).interactionsWith readChannel.toRaw =
      [(readChannel.pushed input.read).toRaw] := by
    rw [Operations.interactionsWith, main_interactions]
    simp [versionChannel, readChannel, Channel.toRaw, circuit_norm]
  rw [Operations.interactionValuesWith, occurrences]
  simp only [List.map_cons, List.map_nil, Channel.eval_pushed]
  exact congrArg (fun read => [readChannel.pushedValue read]) (eval_read env input)

/-- The signed version occurrence is retained at the actual physical activity, including zero. -/
theorem guarded_versions (input : Var RowInput (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((guarded.main input).operations offset).interactionValuesWith versionChannel.toRaw env =
      [versionChannel.pulledIfValue (env input.2) (eval env input.1.version)] := by
  change ((Guarded.main circuit guardSupported input).operations offset).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  simp only [circuit, version_values, List.map_cons, List.map_nil, Channel.pulledValue,
    Channel.pulledIfValue, mul_one]

/-- The matching receipt reuses the selected address and value and binds the full incoming clock. -/
theorem guarded_reads (input : Var RowInput (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((guarded.main input).operations offset).interactionValuesWith readChannel.toRaw env =
      [readChannel.pushedIfValue (env input.2) (ProvableStruct.eval env input.1).read] := by
  change ((Guarded.main circuit guardSupported input).operations offset).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  simp only [circuit, read_values, List.map_cons, List.map_nil, Channel.pushedValue,
    Channel.pushedIfValue, mul_one]

/-- The versions ledger of any physical probe row, including padding. -/
theorem component_versions (env : Environment (ZMod p)) :
    component.operations.interactionValuesWith versionChannel.toRaw env =
      [versionChannel.pulledIfValue (valueFromOffset RowInput 0 env).2 (valueFromOffset RowInput 0 env).1.version] := by
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change ((guarded.main (varFromOffset RowInput 0)).operations (size RowInput)).interactionValuesWith versionChannel.toRaw env = _
  have projection (vars : Var RowInput (ZMod p)) : eval env vars.1.version = (eval env vars).1.version := by
    simp only [circuit_norm]
  have eq := guarded_versions (varFromOffset RowInput 0) (size RowInput) env
  simpa only [Guarded.eval_activity, projection, eval_varFromOffset_valueFromOffset] using eq

/-- The reads ledger of any physical probe row, including padding. -/
theorem component_reads (env : Environment (ZMod p)) :
    component.operations.interactionValuesWith readChannel.toRaw env =
      [readChannel.pushedIfValue (valueFromOffset RowInput 0 env).2 (valueFromOffset RowInput 0 env).1.read] := by
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change ((guarded.main (varFromOffset RowInput 0)).operations (size RowInput)).interactionValuesWith readChannel.toRaw env = _
  have projection (vars : Var RowInput (ZMod p)) : ProvableStruct.eval env vars.1 = (eval env vars).1 := by
    simp only [circuit_norm]
  have eq := guarded_reads (varFromOffset RowInput 0) (size RowInput) env
  simpa only [Guarded.eval_activity, projection, eval_varFromOffset_valueFromOffset] using eq

end SP1Clean.WriteProbe
