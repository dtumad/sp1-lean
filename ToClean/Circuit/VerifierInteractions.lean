module

public import Clean.Air.Verifier

/-! # Certified interaction lists in a public verifier

Clean's verifier accepts one interaction at a time together with its unconditional opposite-side
proof. This adapter imports an existing circuit's literal interaction list using the same proof
obligation. It preserves order, repeated messages and zero multiplicities; no new operation format
or extraction path is introduced. Move it upstream beside `Verifier.addOperation`.
-/

@[expose] public section

namespace Verifier

variable {F : Type} [FiniteField F]

/-- Import existing interactions only when each satisfies Clean's verifier admission rule. -/
def ofInteractions (interactions : List (AbstractInteraction F))
    (valid : ∀ interaction ∈ interactions, ∀ env,
      interaction.direction = .pull → interaction.Requirements env) :
    VerifierM F Unit :=
  ((), interactions.attach.map fun interaction =>
    .interact interaction.val (fun assumes env => by
      exact valid interaction.val interaction.property env assumes))

/-- Importing certified operations retains the literal source interaction list. -/
theorem ofInteractions_interactions (interactions : List (AbstractInteraction F)) (valid) :
    (ofInteractions interactions valid).circuitOperations.interactions = interactions := by
  simp [VerifierM.circuitOperations, Operations.circuitOperations_interactions, ofInteractions,
    VerifierM.operations, Operations.interactions, Operation.interaction]

/-- Every selected channel keeps all of its evaluated occurrences. -/
theorem ofInteractions_values (ops : _root_.Operations F) (valid)
    (channel : RawChannel F) (env : Environment F) :
    (ofInteractions ops.interactions valid).circuitOperations.interactionValuesWith channel env =
      ops.interactionValuesWith channel env := by
  simp only [_root_.Operations.interactionValuesWith, _root_.Operations.interactionsWith,
    ofInteractions_interactions]

/-- The public verifier's channel partition has the same support as its literal ledger. -/
theorem Program.mem_channels_iff {PublicIO : TypeMap} [ProvableType PublicIO]
    (program : Program F PublicIO) (channel : RawChannel F) :
    channel ∈ program.channels ↔ channel ∈ program.circuitOperations.channels := by
  change channel ∈ program.operations.channelsWithGuarantees ++
    program.operations.channelsWithRequirements ↔ _
  rw [_root_.Operations.channels, Verifier.Operations.circuitOperations_interactions]
  constructor
  · intro member
    rcases List.mem_append.mp member with member | member
    all_goals
      obtain ⟨⟨interaction, valid⟩, used, selected⟩ := List.mem_filterMap.mp member
      refine List.mem_map.mpr ⟨interaction, List.mem_map.mpr ⟨_, used, rfl⟩, ?_⟩
      cases direction : interaction.direction <;>
        simp_all [Operation.guaranteeChannel, Operation.requirementChannel]
  · rintro member
    obtain ⟨interaction, used, rfl⟩ := List.mem_map.mp member
    exact Verifier.Operations.channel_mem_of_mem_interactions used

end Verifier
