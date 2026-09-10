import Clean.Air.FlatEnsemble

/-! # Closing a channel from its actual provider requirements

Clean supplies channel consistency and an ordered-table induction, but no direct ensemble rule
for a channel whose provider requirements are already proved. Such a channel needs no table
ordering: consistency applies to the actual balanced ledger, and each table inherits the result.
The component-level corollary keeps these static proofs independent of witness layout. This is
intended for `Clean/Air/FlatEnsemble.lean`; it uses no application-specific messages or tables.
-/

namespace Air.Flat

variable {F : Type} [FiniteField F] [DecidableEq F]
variable {PublicIO : TypeMap} [ProvableType PublicIO] {ens : Ensemble F PublicIO}

omit [DecidableEq F] in
/-- A component with no incoming guarantees proves its contract and outgoing requirements
directly from constraints and its local assumptions. -/
theorem Component.weakSoundness_of_no_guarantees (component : Component F)
    (noGuarantees : component.circuit.channelsWithGuarantees = [])
    {env : Environment F} (assumptions : component.Assumptions env)
    (constraints : component.operations.ConstraintsHold env) :
    component.Spec env ∧ component.operations.FullRequirements env := by
  have interface := component.inChannelsOrGuarantees env
  rw [noGuarantees] at interface
  exact Component.weakSoundness assumptions constraints
    ((Operations.guarantees_iff component.operations [] env interface).mpr (by simp))

/-- Channel consistency closes every pull when the actual balanced ledger's pushes satisfy
their requirements. Tables may appear in any order, and all use the witness's shared data. -/
theorem EnsembleWitness.channelGuarantees_of_requirements (witness : EnsembleWitness ens)
    (channel : RawChannel F) [channel.Consistent]
    (balanced : witness.BalancedChannel channel)
    (requirements : ∀ table ∈ witness.allTables, table.ChannelRequirements channel) :
    ∀ table ∈ witness.allTables, table.ChannelGuarantees channel := by
  have allRequirements : ∀ interaction ∈ witness.interactionsWith channel,
      interaction.channel = channel ∧ interaction.Requirements witness.data := by
    intro interaction member
    obtain ⟨table, member, emitted⟩ := EnsembleWitness.mem_interactionsWith.mp member
    have required := (table.channelRequirements_iff_forall channel).mp
      (requirements table member) interaction emitted
    exact ⟨table.channel_eq_of_mem_interactionsWith emitted, by
      rwa [witness.data_eq_of_mem_allTables table member] at required⟩
  have guarantees := (inferInstance : channel.Consistent).consistent
    (witness.interactionsWith channel) witness.data balanced allRequirements
  intro table member
  rw [table.channelGuarantees_iff_forall channel, witness.data_eq_of_mem_allTables table member]
  intro interaction emitted
  exact guarantees interaction (EnsembleWitness.mem_interactionsWith.mpr ⟨table, member, emitted⟩)

/-- Proved component-local requirements and raw constraints suffice to close a channel.
No witness-specific provider validity or positional consumer/provider partition is needed. -/
theorem EnsembleWitness.channelGuarantees_of_component_requirements (witness : EnsembleWitness ens)
    (channel : RawChannel F) [channel.Consistent]
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel channel)
    (requirements : ∀ component ∈ ens.allTables, ∀ env,
      component.operations.ConstraintsHold env → component.operations.ChannelRequirements channel env) :
    ∀ table ∈ witness.allTables, table.ChannelGuarantees channel := by
  apply witness.channelGuarantees_of_requirements channel balanced
  intro table member row rowMember
  apply requirements table.component (EnsembleWitness.mem_allTables_component_of_mem_allTables member)
  exact constraints table member row rowMember

end Air.Flat
