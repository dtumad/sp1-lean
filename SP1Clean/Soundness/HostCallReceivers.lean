import SP1Clean.Proofs.Chips.HostControlLedger
import SP1Clean.Proofs.Chips.HostCommitChip.Ledger
import SP1Clean.Proofs.Chips.HostHintLengthChip.Ledger
import ToClean.Air.HintIndex
import ToClean.Air.ReceiverView
import SP1Clean.Soundness.HostLocalCore

/-! # Unit receiver views for native host handlers

Each view reads the complete HostCall directly from its own physical row. Its ledger law is
proved from the existing handler circuit, so a heterogeneous installed registry can account
for every call without per-witness equations. The two no-effect calls can share a physical receiver when the selected profile permits VERIFY.
-/

namespace SP1Clean.Soundness.HostCallReceivers

open Circuit Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def halt : ReceiverView (HostCallChip.channel (p := p)) where
  component := {
    circuit := HostHaltChip.circuit
    Assumptions := (HostHaltChip.circuit).Assumptions
    generation := Witgen.HintIndex.unitDemand (HostHaltChip.circuit (p := p)).name HostCallChip.channel .push
      (fun message => message.clk_high.val * 16777216 + message.clk_low.val)
      (fun input => input.call) (fun _ => 1) }
  message env := eval env (varFromOffset HostHaltChip.Inputs 0).call
  interactions env := by
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq]
    change ((HostHaltChip.main (varFromOffset HostHaltChip.Inputs 0)).operations
      (size HostHaltChip.Inputs)).interactionValuesWith HostCallChip.channel.toRaw env = _
    exact HostHaltChip.host_values _ _ env

private def noopReceiver (circuit : GeneralFormalCircuit (ZMod p) HostNoopChip.Inputs unit)
    (values : ∀ input offset env,
      ((circuit.main input).operations offset).interactionValuesWith HostCallChip.channel.toRaw env =
        [HostCallChip.channel.pulledValue (Eval.eval env input)]) :
    ReceiverView (HostCallChip.channel (p := p)) where
  component := {
    circuit
    Assumptions := circuit.Assumptions
    generation := Witgen.HintIndex.unitDemand circuit.name HostCallChip.channel .push
      (fun message => message.clk_high.val * 16777216 + message.clk_low.val)
      (fun input => input) (fun _ => 1) }
  message env := eval env (varFromOffset HostNoopChip.Inputs 0)
  interactions env := by
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq]
    exact values _ _ env

/-- A typed receiver for the released ENTER or VERIFY handoff, including its generation slot. -/
def noop (kind : HostNoopChip.Kind) : ReceiverView (HostCallChip.channel (p := p)) :=
  noopReceiver (HostNoopChip.circuit kind) (HostNoopChip.host_values kind)

/-- The no-effect receipt slot admits ENTER alone or both no-effect calls, according to the installation. -/
def profileNoop (includeVerify : Bool) : ReceiverView (HostCallChip.channel (p := p)) :=
  if includeVerify then noopReceiver HostNoopChip.choiceCircuit HostNoopChip.choice_host_values else noop .enter

def commit (deferred : Bool) (slot : Fin 8) : ReceiverView (HostCallChip.channel (p := p)) where
  component := { circuit := HostCommitChip.circuit deferred slot, Assumptions := (HostCommitChip.circuit deferred slot).Assumptions, generation := HostCommitChip.generation deferred slot }
  message env := eval env (varFromOffset HostCommitChip.RowInput 0).1.call
  activity := (varFromOffset HostCommitChip.RowInput 0).2
  activity_of_constraints := by
    intro env valid
    rw [Component.constraintsHold_iff] at valid
    exact Guarded.activity_of_constraints (HostCommitChip.activeCircuit deferred slot) inferInstance
      (varFromOffset HostCommitChip.RowInput 0) (size HostCommitChip.RowInput) env valid
  interactions env := by
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq]
    change (((HostCommitChip.circuit deferred slot).main (varFromOffset HostCommitChip.RowInput 0)).operations
      (size HostCommitChip.RowInput)).interactionValuesWith HostCallChip.channel.toRaw env = _
    exact HostCommitChip.guarded_host_values deferred slot _ _ env

def hintLength (empty : Bool) : ReceiverView (HostCallChip.channel (p := p)) where
  component := {
    circuit := HostHintLengthChip.circuit empty
    Assumptions := (HostHintLengthChip.circuit empty).Assumptions
    generation := Witgen.HintIndex.unitDemand (HostHintLengthChip.circuit (p := p) empty).name HostCallChip.channel .push
      (fun message => message.clk_high.val * 16777216 + message.clk_low.val)
      (fun input => input.call) (fun _ => 1) }
  message env := eval env (varFromOffset HostHintLengthChip.Inputs 0).call
  interactions env := by
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq]
    change ((HostHintLengthChip.main empty (varFromOffset HostHintLengthChip.Inputs 0)).operations
      (size HostHintLengthChip.Inputs)).interactionValuesWith HostCallChip.channel.toRaw env = _
    exact HostHintLengthChip.host_values empty _ _ env

/-- The receiver reads the complete call from the physical HALT row. -/
theorem halt_message (env : Environment (ZMod p)) :
    (HostCallReceivers.halt (p := p)).message env = (valueFromOffset HostHaltChip.Inputs 0 env).call := by
  have evaluated (input : Var HostHaltChip.Inputs (ZMod p)) : eval env input.call = (eval env input).call := by
    cases input
    simp only [circuit_norm]
  simp only [HostCallReceivers.halt, evaluated, eval_varFromOffset_valueFromOffset]

omit [Fact (2 ^ 25 < p)] in
/-- Both no-effect receivers read the complete call directly from their physical row. -/
theorem noop_message (kind : HostNoopChip.Kind) (env : Environment (ZMod p)) :
    (HostCallReceivers.noop (p := p) kind).message env = valueFromOffset HostNoopChip.Inputs 0 env := by
  simp only [HostCallReceivers.noop, noopReceiver, eval_varFromOffset_valueFromOffset]

/-- Both profiles retain the original complete message at the no-effect receiver. -/
theorem profileNoop_message (includeVerify : Bool) (env : Environment (ZMod p)) :
    (profileNoop (p := p) includeVerify).message env = valueFromOffset HostNoopChip.Inputs 0 env := by
  cases includeVerify <;> simp only [profileNoop, Bool.false_eq_true, ite_false, ite_true, noop,
    noopReceiver, eval_varFromOffset_valueFromOffset]

/-- A physical no-effect row identifies its selected call and proves the corresponding release contract. -/
theorem profileNoop_spec (includeVerify : Bool) (env : Environment (ZMod p))
    (checked : (profileNoop includeVerify).component.operations.ConstraintsHold env) :
    ∃ kind, (kind = .enter ∨ includeVerify = true) ∧
      HostNoopChip.Spec kind (valueFromOffset HostNoopChip.Inputs 0 env) := by
  cases includeVerify with
  | false => exact ⟨.enter, Or.inl rfl, HostNoopChip.row_spec_of_constraints .enter env
      ((Component.constraintsHold_iff env).mp checked)⟩
  | true =>
    rcases HostNoopChip.choice_spec_of_constraints env ((Component.constraintsHold_iff env).mp checked) with enter | verify
    · exact ⟨.enter, Or.inl rfl, enter⟩
    · exact ⟨.verify, Or.inr rfl, verify⟩

/-- Each commitment receiver reads its row's complete call. -/
theorem commit_message (deferred : Bool) (slot : Fin 8) (env : Environment (ZMod p)) :
    (HostCallReceivers.commit (p := p) deferred slot).message env =
      (valueFromOffset HostCommitChip.RowInput 0 env).1.call := by
  have evaluated (input : Var HostCommitChip.Inputs (ZMod p)) : eval env input.call = (eval env input).call := by
    cases input
    simp only [circuit_norm]
  change eval env (varFromOffset HostCommitChip.RowInput 0).1.call = _
  rw [evaluated]
  have decoded := eval_varFromOffset_valueFromOffset HostCommitChip.RowInput 0 env
  rw [CircuitType.eval_var_provablePair] at decoded
  exact congrArg (fun input : HostCommitChip.Inputs (ZMod p) => input.call) (congrArg Prod.fst decoded)

/-- A commitment receiver uses the same guard as its bank transition view. -/
theorem commit_activity (deferred : Bool) (slot : Fin 8) :
    (commit (p := p) deferred slot).activity = (varFromOffset HostCommitChip.RowInput 0).2 := by
  simp only [commit]

/-- The implemented non-RAM handlers: control, both eight-slot commitment families,
and empty/nonempty HINT_LEN. HINT_READ adds its own receiver and RAM resources. -/
def availableFor (includeVerify : Bool) : List (ReceiverView (HostCallChip.channel (p := p))) :=
  [halt, profileNoop includeVerify] ++ (List.ofFn fun slot => commit false slot) ++
    (List.ofFn fun slot => commit true slot) ++ [hintLength false, hintLength true]

/-- The receivers in the original six-call assembly retain their original physical positions. -/
abbrev available := availableFor (p := p) false

/-- All available handlers satisfy the CPU chronology interface by their static channel metadata. -/
theorem auxiliaryInterface (includeVerify : Bool := false) : HostLocalCore.AuxiliaryInterface ((availableFor (p := p) includeVerify).map (·.component)) := by
  apply HostLocalCore.AuxiliaryInterface.of_channels
  · have checked : ((availableFor (p := p) includeVerify).map (·.component)).all (fun component =>
        !(component.circuit.channelsWithRequirements.map RawChannel.name).contains (Channels.byteChannel (p := p)).toRaw.name) = true := by cases includeVerify <;> rfl
    intro component member used
    have valid := List.all_eq_true.mp checked component member
    have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
    rw [present] at valid
    contradiction
  · have checked : ((availableFor (p := p) includeVerify).map (·.component)).all (fun component =>
        !(component.circuit.channels.map RawChannel.name).contains (Channels.stateChannel (p := p)).toRaw.name) = true := by cases includeVerify <;> rfl
    intro component member used
    have valid := List.all_eq_true.mp checked component member
    have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
    rw [present] at valid
    contradiction

end SP1Clean.Soundness.HostCallReceivers
