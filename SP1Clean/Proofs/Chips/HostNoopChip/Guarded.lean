import SP1Clean.Proofs.Chips.HostControlLedger
import ToClean.Circuit.Guarded
import ToClean.Air.HintIndex
import ToClean.Air.GuardedDemandTable

/-! # Demand-padded no-effect host receiver

The profile selects the permitted full call codes. The same activity cell gates every
opcode and return constraint, as well as the physical handoff multiplicity.
-/

namespace SP1Clean.HostNoopChip
open Circuit Air.Flat
variable {p : Nat} [Fact p.Prime] [Fact (2^17 < p)]

/-- The complete instruction handoff and the physical row activity. -/
abbrev RowInput := ProvablePair Inputs field

/-- The occupied row checks the two return codes or only ENTER, according to its profile. -/
def activeCircuit (includeVerify : Bool) : GeneralFormalCircuit (ZMod p) Inputs unit :=
  if includeVerify then choiceCircuit else circuit .enter

attribute [local circuit_norm] Gadgets.Equality.main Gadgets.Equality.circuit
  FormalAssertion.toSubcircuit_toFlat Operations.lookups_toFlat Operations.lookups Operations.toNested_toFlat FlatOperation.lookups

/-- The control leaf contains algebraic constraints and the ordinary guard-compatible host channel. -/
instance guardSupported (includeVerify : Bool) : Guarded.Supported (activeCircuit (p := p) includeVerify) :=
  Guarded.Supported.of_emitted_requirements _
    (by intro input offset; cases includeVerify <;> simp [activeCircuit, choiceCircuit, circuit, choiceMain, main, circuit_norm])
    (by
      intro ch member
      have only : ch = HostCallChip.channel.toRaw := by
        cases includeVerify <;>
          simp [activeCircuit, GeneralFormalCircuit.channels, choiceCircuit, circuit, elaborated, choiceElaborated, circuit_norm] at member <;>
          exact member
      subst ch
      infer_instance)
    (by intro _ _ ch req missing _ _; exfalso; apply missing; cases includeVerify <;>
        simp_all [activeCircuit, circuit, choiceCircuit, elaborated, choiceElaborated, circuit_norm])

/-- The actual padded receiver at the original control slot. -/
def guardedCircuit (includeVerify : Bool) : GeneralFormalCircuit (ZMod p) RowInput unit :=
  Guarded.circuit (activeCircuit includeVerify) inferInstance

/-- Every fired handler reads its own active, correctly keyed witness hint. -/
def generation (includeVerify : Bool) : WitnessGeneration.Generation (ZMod p) RowInput :=
  Witgen.HintIndex.unitDemand (guardedCircuit (p := p) includeVerify).name HostCallChip.channel .push
    (fun m => m.clk_high.val * 16777216 + m.clk_low.val) Prod.fst Prod.snd

/-- Component shared by the physical soundness reader, row constructor, and backend. -/
def component (includeVerify : Bool) : Component (ZMod p) where
  circuit := guardedCircuit includeVerify
  Assumptions := (guardedCircuit includeVerify).Assumptions
  generation := generation includeVerify

/-- The registered row has one host interaction even when its activity is zero. -/
theorem guarded_host_values (includeVerify : Bool) (input : Var RowInput (ZMod p)) (offset : Nat) (env : Environment (ZMod p)) :
    (((guardedCircuit includeVerify).main input).operations offset).interactionValuesWith HostCallChip.channel.toRaw env =
      [HostCallChip.channel.pulledIfValue (env input.2) (Eval.eval env input.1)] := by
  change ((Guarded.main (activeCircuit includeVerify) inferInstance input).operations offset).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  cases includeVerify <;>
    simp [activeCircuit, circuit, choiceCircuit, host_values, choice_host_values, Channel.pulledValue, Channel.pulledIfValue]

/-- Every enabled row of this component has a permitted full call code and x5 result. -/
theorem spec_of_active (includeVerify : Bool) (env : Environment (ZMod p))
    (checked : (component includeVerify).operations.ConstraintsHold env)
    (enabled : env (varFromOffset RowInput 0).2 = 1) :
    ∃ kind, (kind = .enter ∨ includeVerify = true) ∧ Spec kind (valueFromOffset RowInput 0 env).1 := by
  have sound := (Component.weakSoundness (component := component (p := p) includeVerify) (by intro _; cases includeVerify <;> trivial) checked (by
    rw [Operations.guarantees_iff _ _ _ ((component includeVerify).inChannelsOrGuarantees env)]
    intro ch member
    have only : ch = HostCallChip.channel.toRaw := by
      cases includeVerify <;> change ch ∈ [HostCallChip.channel.toRaw] at member <;> exact List.mem_singleton.mp member
    subst ch
    exact Operations.channelGuarantees_of_trivial _ (by simp [HostCallChip.channel, Channel.toRaw]) _ _)).1
  have one : (valueFromOffset RowInput 0 env).2 = 1 := by
    rw [← eval_varFromOffset_valueFromOffset RowInput 0 env, ← Guarded.eval_activity]
    exact enabled
  change IsBool (valueFromOffset RowInput 0 env).2 ∧ ((valueFromOffset RowInput 0 env).2 = 1 →
    (activeCircuit includeVerify).Spec (valueFromOffset RowInput 0 env).1 () env.data) at sound
  have child := sound.2 one
  cases includeVerify
  · exact ⟨.enter, Or.inl rfl, child⟩
  · rcases child with enter | verify
    · exact ⟨.enter, Or.inl rfl, enter⟩
    · exact ⟨.verify, Or.inr rfl, verify⟩

end SP1Clean.HostNoopChip
