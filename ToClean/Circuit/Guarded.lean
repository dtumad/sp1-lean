module

public import ToClean.Circuit.SubcircuitProjection
public import Clean.Gadgets.Boolean

/-! # Boolean activity for bundled circuits

Clean has no generic bundled wrapper that disables a row's assertions and channel obligations.
This addition scales its existing assertions and interaction multiplicities by a Boolean input,
retaining every physical occurrence, message, witness program and witness offset. The reusable
boundary is a `GeneralFormalCircuit`; legacy lookups must be absent and channels must admit zero
multiplicity. No exporter or witness interpreter is introduced. Intended for `Clean/Circuit`.
-/

@[expose] public section

variable {F : Type} [FiniteField F]

/-- A disabled interaction has no local channel obligations. Typed channels have this law. -/
class RawChannel.ZeroNeutral (channel : RawChannel F) : Prop where
  /-- Zero multiplicity contributes no assumed channel meaning. -/
  guarantees : ∀ message data, channel.Guarantees 0 message data
  /-- Zero multiplicity contributes no required channel meaning. -/
  requirements : ∀ message data, channel.Requirements 0 message data

instance {Message : TypeMap} [ProvableType Message] (channel : Channel F Message) :
    channel.toRaw.ZeroNeutral where
  guarantees := by intros; simp [Channel.toRaw]
  requirements := by intros; simp [Channel.toRaw]

namespace AbstractInteraction

/-- Keep the complete message and physical occurrence while scaling its multiplicity. -/
def guard (enabled : Expression F) (interaction : AbstractInteraction F) : AbstractInteraction F :=
  { interaction with mult := enabled * interaction.mult }

/-- Evaluation keeps the original payload and changes only the interaction's multiplicity. -/
@[circuit_norm] theorem eval_guard (enabled : Expression F) (interaction : AbstractInteraction F)
    (env : Environment F) :
    eval env (guard enabled interaction) =
      { eval env interaction with mult := env enabled * (eval env interaction).mult } := rfl

theorem guard_guarantees_one (enabled : Expression F) (interaction : AbstractInteraction F)
    (env : Environment F) (active : env enabled = 1) :
    (guard enabled interaction).Guarantees env ↔ interaction.Guarantees env := by
  simp [guard, Guarantees, Expression.eval, active]

theorem guard_requirements_one (enabled : Expression F) (interaction : AbstractInteraction F)
    (env : Environment F) (active : env enabled = 1) :
    (guard enabled interaction).Requirements env ↔ interaction.Requirements env := by
  simp [guard, Requirements, Expression.eval, active]

theorem guard_guarantees_zero (enabled : Expression F) (interaction : AbstractInteraction F)
    [interaction.channel.ZeroNeutral] (env : Environment F) (inactive : env enabled = 0) :
    (guard enabled interaction).Guarantees env := by
  intro _
  simpa [guard, Expression.eval, inactive] using
    RawChannel.ZeroNeutral.guarantees (channel := interaction.channel)
      (interaction.msg.map env) env.data

theorem guard_requirements_zero (enabled : Expression F) (interaction : AbstractInteraction F)
    [interaction.channel.ZeroNeutral] (env : Environment F) (inactive : env enabled = 0) :
    (guard enabled interaction).Requirements env := by
  simpa [guard, Requirements, Expression.eval, inactive] using
    RawChannel.ZeroNeutral.requirements (channel := interaction.channel)
      (interaction.msg.map env) env.data

end AbstractInteraction

namespace FlatOperation

/-- Scale assertions and interactions; retain witness programs and legacy lookups literally.
Disabled validity below requires the explicit structural fact that lookups are absent. -/
def guard (enabled : Expression F) : FlatOperation F → FlatOperation F
  | .witness size program => .witness size program
  | .assert expression => .assert (enabled * expression)
  | .lookup query => .lookup query
  | .interact interaction => .interact (interaction.guard enabled)

omit [FiniteField F] in
theorem constraints_guard (enabled : Expression F) (ops : List (FlatOperation F)) :
    constraints (ops.map (guard enabled)) = (constraints ops).map (enabled * ·) := by
  induction ops with
  | nil => rfl
  | cons op ops ih => cases op <;> simp [guard, constraints, ih]

omit [FiniteField F] in
theorem lookups_guard (enabled : Expression F) (ops : List (FlatOperation F)) :
    lookups (ops.map (guard enabled)) = lookups ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih => cases op <;> simp [guard, lookups, ih]

omit [FiniteField F] in
theorem interactions_guard (enabled : Expression F) (ops : List (FlatOperation F)) :
    interactions (ops.map (guard enabled)) =
      (interactions ops).map (AbstractInteraction.guard enabled) := by
  induction ops with
  | nil => rfl
  | cons op ops ih => cases op <;> simp [guard, interactions, ih]

omit [FiniteField F] in
theorem localLength_guard (enabled : Expression F) (ops : List (FlatOperation F)) :
    localLength (ops.map (guard enabled)) = localLength ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih => cases op <;> simp [guard, localLength, ih]

omit [FiniteField F] in
theorem witnessOperations_guard (enabled : Expression F) (ops : List (FlatOperation F)) :
    witnessOperations (ops.map (guard enabled)) = witnessOperations ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih => cases op <;> simp [guard, witnessOperations, ih]

theorem constraints_guard_one (enabled : Expression F) (ops : List (FlatOperation F))
    (env : Environment F) (active : env enabled = 1) :
    ConstraintsHoldFlat env (ops.map (guard enabled)) ↔ ConstraintsHoldFlat env ops := by
  simp [constraintsHoldFlat_iff_forall_mem, constraints_guard, lookups_guard,
    Expression.eval, active]

theorem constraints_guard_zero (enabled : Expression F) (ops : List (FlatOperation F))
    (noLookups : lookups ops = []) (env : Environment F) (inactive : env enabled = 0) :
    ConstraintsHoldFlat env (ops.map (guard enabled)) := by
  simp [constraintsHoldFlat_iff_forall_mem, constraints_guard, lookups_guard, noLookups,
    Expression.eval, inactive]

theorem guarantees_guard_one (enabled : Expression F) (ops : List (FlatOperation F))
    (env : Environment F) (active : env enabled = 1) :
    Guarantees env (ops.map (guard enabled)) ↔ Guarantees env ops := by
  simp only [guarantees_iff_forall_mem, interactions_guard, List.forall_mem_map,
    AbstractInteraction.guard_guarantees_one enabled _ env active]

theorem requirements_guard_one (enabled : Expression F) (ops : List (FlatOperation F))
    (env : Environment F) (active : env enabled = 1) :
    Requirements env (ops.map (guard enabled)) ↔ Requirements env ops := by
  simp only [requirements_iff_forall_mem, interactions_guard, List.forall_mem_map,
    AbstractInteraction.guard_requirements_one enabled _ env active]

theorem guarantees_guard_zero (enabled : Expression F) (ops : List (FlatOperation F))
    (neutral : ∀ interaction ∈ interactions ops, interaction.channel.ZeroNeutral)
    (env : Environment F) (inactive : env enabled = 0) :
    Guarantees env (ops.map (guard enabled)) := by
  rw [guarantees_iff_forall_mem, interactions_guard, List.forall_mem_map]
  intro interaction member
  let := neutral interaction member
  exact interaction.guard_guarantees_zero enabled env inactive

theorem requirements_guard_zero (enabled : Expression F) (ops : List (FlatOperation F))
    (neutral : ∀ interaction ∈ interactions ops, interaction.channel.ZeroNeutral)
    (env : Environment F) (inactive : env enabled = 0) :
    Requirements env (ops.map (guard enabled)) := by
  rw [requirements_iff_forall_mem, interactions_guard, List.forall_mem_map]
  intro interaction member
  let := neutral interaction member
  exact interaction.guard_requirements_zero enabled env inactive

end FlatOperation

namespace ProverEnvironment

/-- Guarding does not change a witness program or the offset at which it runs. -/
theorem usesLocalWitnessesFlat_guard (env : ProverEnvironment F) (enabled : Expression F)
    (ops : List (FlatOperation F)) (offset : ℕ) :
    env.UsesLocalWitnessesFlat offset (ops.map (FlatOperation.guard enabled)) ↔
      env.UsesLocalWitnessesFlat offset ops := by
  simp only [UsesLocalWitnessesFlat]
  induction ops generalizing offset with
  | nil => rfl
  | cons op ops ih =>
    cases op <;> simp [FlatOperation.guard, FlatOperation.forAll, ih]

end ProverEnvironment

namespace Subcircuit

/-- Guard an already bundled circuit. Its witness programs and physical interaction occurrences
remain unchanged; a Boolean activity cell controls the assertions and multiplicities. -/
def guard {offset : ℕ} (original : Subcircuit F offset) (enabled : Expression F)
    (noLookups : FlatOperation.lookups original.ops.toFlat = [])
    (neutral : ∀ interaction ∈ FlatOperation.interactions original.ops.toFlat,
      interaction.channel.ZeroNeutral) : Subcircuit F offset :=
  let operations := FlatOperation.assert (enabled * (enabled - 1)) ::
    original.ops.toFlat.map (FlatOperation.guard enabled)
  let nested := NestedOperations.nested ("guarded", operations.map NestedOperations.single)
  have flat : nested.toFlat = operations := by
    simp [nested, NestedOperations.toFlat, List.flatMap_map]
  {
    ops := nested
    Assumptions env := env enabled = 1 → original.Assumptions env
    Spec env := IsBool (env enabled) ∧ (env enabled = 1 → original.Spec env)
    ProverAssumptions env := IsBool (env.toEnvironment enabled) ∧
      (env.toEnvironment enabled = 1 → original.ProverAssumptions env)
    ProverSpec := original.ProverSpec
    localLength := original.localLength
    channelsWithGuarantees := original.channelsWithGuarantees
    channelsWithRequirements := original.channelsWithRequirements
    soundness := by
      intro env assumptions constraints guarantees
      rw [flat] at constraints guarantees ⊢
      have boolean : IsBool (env enabled) := by
        apply IsBool.iff_mul_sub_one.mpr
        simpa [eval_sub, Expression.eval] using constraints.1
      have childConstraints := constraints.2
      have childGuarantees : FlatOperation.Guarantees env
          (original.ops.toFlat.map (FlatOperation.guard enabled)) := by
        simpa only [operations, FlatOperation.guarantees_iff_forall_mem,
          FlatOperation.interactions] using guarantees
      refine ⟨⟨boolean, ?_⟩, ?_⟩
      · intro active
        exact (original.soundness env (assumptions active)
          ((FlatOperation.constraints_guard_one enabled _ env active).mp childConstraints)
          ((FlatOperation.guarantees_guard_one enabled _ env active).mp childGuarantees)).1
      · simp only [operations, FlatOperation.requirements_iff_forall_mem,
          FlatOperation.interactions]
        apply FlatOperation.requirements_iff_forall_mem.mp
        rcases boolean with inactive | active
        · exact FlatOperation.requirements_guard_zero enabled _ neutral env inactive
        · apply (FlatOperation.requirements_guard_one enabled _ env active).mpr
          exact (original.soundness env (assumptions active)
            ((FlatOperation.constraints_guard_one enabled _ env active).mp childConstraints)
            ((FlatOperation.guarantees_guard_one enabled _ env active).mp childGuarantees)).2
    completeness := by
      intro env witnesses
      rw [flat] at witnesses ⊢
      rw [← env.usesLocalWitnessesFlat_iff_extends] at witnesses
      have childWitnesses : env.UsesLocalWitnessesFlat offset original.ops.toFlat := by
        apply (env.usesLocalWitnessesFlat_guard enabled _ offset).mp
        simpa only [operations, ProverEnvironment.UsesLocalWitnessesFlat,
          FlatOperation.forAll_cons, Condition.applyFlat, FlatOperation.singleLocalLength,
          true_and, Nat.zero_add] using witnesses
      have child := original.completeness env
        ((env.usesLocalWitnessesFlat_iff_extends offset).mp childWitnesses)
      refine ⟨?_, child.2⟩
      intro assumptions
      have boolean : env.toEnvironment (enabled * (enabled - 1)) = 0 := by
        simpa [eval_sub, Expression.eval] using IsBool.iff_mul_sub_one.mp assumptions.1
      refine ⟨⟨boolean, ?_⟩, ?_⟩
      · rcases assumptions.1 with inactive | active
        · exact FlatOperation.constraints_guard_zero enabled _ noLookups env.toEnvironment inactive
        · exact (FlatOperation.constraints_guard_one enabled _ env.toEnvironment active).mpr
            (child.1 (assumptions.2 active)).1
      · simp only [operations, FlatOperation.guarantees_iff_forall_mem,
          FlatOperation.interactions]
        apply FlatOperation.guarantees_iff_forall_mem.mp
        rcases assumptions.1 with inactive | active
        · exact FlatOperation.guarantees_guard_zero enabled _ neutral env.toEnvironment inactive
        · exact (FlatOperation.guarantees_guard_one enabled _ env.toEnvironment active).mpr
            (child.1 (assumptions.2 active)).2
    localLength_eq := by
      rw [flat]
      simp only [operations, FlatOperation.localLength, FlatOperation.localLength_guard]
      exact original.localLength_eq
  }

/-- Keep the existing channel interface when every guarantee-carrying occurrence is declared.
This is structural: arbitrary environments need not satisfy the activity constraint. -/
theorem guard_channelsLawful {offset : ℕ} (original : Subcircuit F offset)
    (lawful : original.ChannelsLawful) (enabled : Expression F)
    (noLookups : FlatOperation.lookups original.ops.toFlat = [])
    (neutral : ∀ interaction ∈ FlatOperation.interactions original.ops.toFlat,
      interaction.channel.ZeroNeutral)
    (declared : ∀ interaction ∈ FlatOperation.interactions original.ops.toFlat,
      interaction.assumeGuarantees = true → interaction.channel ∈ original.channelsWithGuarantees) :
    (original.guard enabled noLookups neutral).ChannelsLawful := by
  have flat : (original.guard enabled noLookups neutral).ops.toFlat =
      FlatOperation.assert (enabled * (enabled - 1)) ::
        original.ops.toFlat.map (FlatOperation.guard enabled) := by
    simp [guard, NestedOperations.toFlat, List.flatMap_map, Function.comp_def, ← List.map_eq_flatMap]
  change (∀ env, FlatOperation.InChannelsOrGuarantees original.channelsWithGuarantees env _) ∧
    (∀ env, ConstraintsHoldFlat env _ →
      FlatOperation.InChannelsOrRequirements original.channelsWithRequirements env _) ∧ _
  refine ⟨?_, ?_, ?_⟩
  · intro env
    rw [FlatOperation.inChannelsOrGuarantees_iff_forall_mem, flat]
    simp only [FlatOperation.interactions, FlatOperation.interactions_guard, List.forall_mem_map]
    intro interaction member
    by_cases carries : interaction.assumeGuarantees = true
    · exact Or.inl (declared interaction member carries)
    · exact Or.inr (by intro assumed; exact False.elim (carries assumed))
  · intro env constraints
    rw [flat] at constraints
    have boolean : IsBool (env enabled) := by
      apply IsBool.iff_mul_sub_one.mpr
      simpa [eval_sub, Expression.eval] using constraints.1
    rw [FlatOperation.inChannelsOrRequirements_iff_forall_mem, flat]
    simp only [FlatOperation.interactions, FlatOperation.interactions_guard, List.forall_mem_map]
    intro interaction member
    rcases boolean with inactive | active
    · let := neutral interaction member
      exact Or.inr (interaction.guard_requirements_zero enabled env inactive)
    · have old := (FlatOperation.inChannelsOrRequirements_iff_forall_mem.mp
        (lawful.2.1 env
          ((FlatOperation.constraints_guard_one enabled _ env active).mp constraints.2)))
          interaction member
      exact old.imp id ((interaction.guard_requirements_one enabled env active).mpr)
  · change FlatOperation.channels _ ⊆
      original.channelsWithGuarantees ++ original.channelsWithRequirements
    rw [flat]
    simpa only [FlatOperation.channels, FlatOperation.interactions,
      FlatOperation.interactions_guard, List.map_map, AbstractInteraction.guard,
      Function.comp_def] using lawful.2.2

end Subcircuit

namespace Circuit.Guarded

variable {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]

/-- Structural capabilities of the bundled child; none are assumptions on a physical witness. -/
structure Supported (provider : GeneralFormalCircuit F Input Output) : Prop where
  /-- Legacy lookup operations have no activity multiplier and must be absent. -/
  noLookups : ∀ input offset,
    FlatOperation.lookups (provider.toSubcircuit offset input).ops.toFlat = []
  /-- Disabled occurrences have no channel obligations, for every message and data context. -/
  neutral : ∀ input offset interaction,
    interaction ∈ FlatOperation.interactions (provider.toSubcircuit offset input).ops.toFlat →
      interaction.channel.ZeroNeutral
  /-- The child declares every occurrence that can assume a channel guarantee. -/
  declared : ∀ input offset interaction,
    interaction ∈ FlatOperation.interactions (provider.toSubcircuit offset input).ops.toFlat →
      interaction.assumeGuarantees = true → interaction.channel ∈ provider.channelsWithGuarantees

/-- Append an activity field to the child's input and call its guarded bundled subcircuit. -/
def main (provider : GeneralFormalCircuit F Input Output) (supported : Supported provider)
    (input : Var (ProvablePair Input field) F) : Circuit F (Var Output F) := fun offset =>
  (provider.output input.1 offset,
    [.subcircuit ((provider.toSubcircuit offset input.1).guard input.2
      (supported.noLookups input.1 offset) (supported.neutral input.1 offset))])

/-- The guard retains the child's witness count and output expressions at the actual offset. -/
instance elaborated (provider : GeneralFormalCircuit F Input Output) (supported : Supported provider) :
    ElaboratedCircuit F (ProvablePair Input field) Output (main provider supported) where
  localLength input := provider.localLength input.1
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm, Subcircuit.guard]
  output input offset := provider.output input.1 offset
  output_eq := by intros; rfl
  subcircuitsConsistent := by
    intro input offset
    simp only [main, circuit_norm]
  channelsWithGuarantees := provider.channelsWithGuarantees
  channelsLawful := by
    intro input offset
    have lawful := Subcircuit.guard_channelsLawful (provider.toSubcircuit offset input.1)
      provider.toSubcircuit_channelsLawful input.2
      (supported.noLookups input.1 offset) (supported.neutral input.1 offset)
      (supported.declared input.1 offset)
    simpa only [main, circuit_norm, Subcircuit.guard] using lawful

/-- An active row has the child's semantic meaning; a disabled row has no child obligations. -/
def circuit (provider : GeneralFormalCircuit F Input Output) (supported : Supported provider) :
    GeneralFormalCircuit F (ProvablePair Input field) Output where
  name := provider.name
  main := main provider supported
  elaborated := elaborated provider supported
  Assumptions input data := input.2 = 1 → provider.Assumptions input.1 data
  Spec input output data := IsBool input.2 ∧ (input.2 = 1 → provider.Spec input.1 output data)
  ProverAssumptions input data hint := IsBool input.2 ∧
    (input.2 = 1 → provider.ProverAssumptions input.1 data hint)
  ProverSpec input output hint := input.2 = 1 → provider.ProverSpec input.1 output hint
  channelsWithRequirements := provider.channelsWithRequirements
  requirementsChannelsLawful := by
    preserve_tactic_target
    intro input offset
    simp only [main, circuit_norm, Subcircuit.guard]
  soundness := by
    circuit_proof_start [main, Subcircuit.guard]
    subst input
    exact ⟨h_holds h_assumptions, Or.inr h_assumptions⟩
  completeness := by
    circuit_proof_start [main, Subcircuit.guard]
    subst input
    refine ⟨h_assumptions, ?_⟩
    intro active
    exact (h_env (h_assumptions.2 active)).2

/-- Flattening retains the child operations, guarded at their actual witness offset. -/
theorem main_toFlat (provider : GeneralFormalCircuit F Input Output) (supported : Supported provider)
    (input : Var (ProvablePair Input field) F) (offset : ℕ) :
    ((main provider supported input).operations offset).toFlat =
      .assert (input.2 * (input.2 - 1)) ::
        ((provider.main input.1).operations offset).toFlat.map (FlatOperation.guard input.2) := by
  simp [main, Circuit.operations, Subcircuit.guard, Operations.toFlat,
    NestedOperations.toFlat, List.flatMap_map, Function.comp_def, ← List.map_eq_flatMap,
    GeneralFormalCircuit.toSubcircuit_toFlat]

/-- The complete interaction list retains its order and every zero-multiplicity occurrence. -/
@[circuit_norm] theorem main_interactions
    (provider : GeneralFormalCircuit F Input Output) (supported : Supported provider)
    (input : Var (ProvablePair Input field) F) (offset : ℕ) :
    ((main provider supported input).operations offset).interactions =
      ((provider.main input.1).operations offset).interactions.map
        (AbstractInteraction.guard input.2) := by
  rw [← Operations.interactions_toFlat, main_toFlat]
  simp only [FlatOperation.interactions, FlatOperation.interactions_guard,
    Operations.interactions_toFlat]

/-- A channel projection retains its complete payloads while scaling only multiplicities. -/
@[circuit_norm] theorem main_interactionsWith
    (provider : GeneralFormalCircuit F Input Output) (supported : Supported provider)
    (input : Var (ProvablePair Input field) F) (offset : ℕ) (channel : RawChannel F) :
    ((main provider supported input).operations offset).interactionsWith channel =
      (((provider.main input.1).operations offset).interactionsWith channel).map
        (AbstractInteraction.guard input.2) := by
  classical
  simp only [Operations.interactionsWith, main_interactions, List.filter_map,
    Function.comp_def, AbstractInteraction.guard]
  congr 1

/-- Guarded rows contain no legacy lookups. -/
@[circuit_norm] theorem main_lookups
    (provider : GeneralFormalCircuit F Input Output) (supported : Supported provider)
    (input : Var (ProvablePair Input field) F) (offset : ℕ) :
    ((main provider supported input).operations offset).lookups = [] := by
  rw [← Operations.lookups_toFlat, main_toFlat]
  simp only [FlatOperation.lookups, FlatOperation.lookups_guard]
  rw [← GeneralFormalCircuit.toSubcircuit_toFlat]
  exact supported.noLookups input.1 offset

end Circuit.Guarded
