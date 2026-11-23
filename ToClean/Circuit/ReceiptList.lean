module

public import ToClean.Circuit.Receipt

/-! # A finite list of typed observations on one existing circuit

Clean's single receipt wrapper adds one projection. Folding it in physical order retains
each occurrence and its symbolic multiplicity, including zero and repeated messages.
-/

@[expose] public section

namespace Circuit.Receipt

variable {F : Type} [FiniteField F]
  {Input Output Message : TypeMap} [ProvableType Input] [ProvableType Output] [ProvableType Message]

/-- Publish each projection in order on the same channel, reusing the original row cells. -/
def many (provider : GeneralFormalCircuit F Input Output) (channel : Channel F Message)
    (trivial : ∀ message data, channel.Guarantees message data)
    (projections : List (Projection F Input Message)) : GeneralFormalCircuit F Input Output :=
  projections.foldl (fun previous next => circuit previous channel trivial next) provider

variable (provider : GeneralFormalCircuit F Input Output) (channel : Channel F Message)
  (trivial : ∀ message data, channel.Guarantees message data) (projections : List (Projection F Input Message))

theorem many_name : (many provider channel trivial projections).name = provider.name := by
  induction projections generalizing provider with
  | nil => rfl
  | cons first rest ih => exact ih _

/-- A single publication appends one declared channel to the circuit. -/
theorem channel_of_receipt (projection : Projection F Input Message) {selected : RawChannel F}
    (used : selected ∈ (circuit provider channel trivial projection).channels) :
    selected ∈ provider.channels ∨ selected = channel.toRaw := by
  change selected ∈ provider.channelsWithGuarantees ++ (provider.channelsWithRequirements ++ [channel.toRaw]) at used
  change selected ∈ provider.channelsWithGuarantees ++ provider.channelsWithRequirements ∨ _
  simpa only [← List.append_assoc, List.mem_append, List.mem_singleton] using used

/-- The only extra registry entry required by any number of projections is their shared
destination. Repetition and the original channels retain their physical multiplicities. -/
theorem many_channels {selected : RawChannel F}
    (used : selected ∈ (many provider channel trivial projections).channels) :
    selected ∈ provider.channels ∨ selected = channel.toRaw := by
  induction projections generalizing provider with
  | nil => exact Or.inl used
  | cons first rest ih =>
    rcases ih (circuit provider channel trivial first) used with previous | added
    · exact channel_of_receipt provider channel trivial first previous
    · exact Or.inr added

theorem many_assumptions : (many provider channel trivial projections).Assumptions = provider.Assumptions := by
  induction projections generalizing provider with
  | nil => rfl
  | cons first rest ih => exact ih _

theorem many_proverAssumptions : (many provider channel trivial projections).ProverAssumptions = provider.ProverAssumptions := by
  induction projections generalizing provider with
  | nil => rfl
  | cons first rest ih => exact ih _

theorem many_width : (many provider channel trivial projections).size = provider.size := by
  induction projections generalizing provider with
  | nil => rfl
  | cons first rest ih => exact (ih _).trans (width provider channel trivial first)

theorem many_constraints : ((many provider channel trivial projections).instantiate.operations 0).constraints =
    (provider.instantiate.operations 0).constraints := by
  induction projections generalizing provider with
  | nil => rfl
  | cons first rest ih => exact (ih _).trans (constraints provider channel trivial first)

theorem many_lookups : ((many provider channel trivial projections).instantiate.operations 0).lookups =
    (provider.instantiate.operations 0).lookups := by
  induction projections generalizing provider with
  | nil => rfl
  | cons first rest ih => exact (ih _).trans (lookups provider channel trivial first)

theorem many_interactions (selected : RawChannel F) (different : selected ≠ channel.toRaw) :
    ((many provider channel trivial projections).instantiate.operations 0).interactionsWith selected =
      (provider.instantiate.operations 0).interactionsWith selected := by
  induction projections generalizing provider with
  | nil => rfl
  | cons first rest ih => exact (ih _).trans (interactions provider channel trivial first selected different)

theorem many_receipts (input : Var Input F) (offset : ℕ) :
    (((many provider channel trivial projections).main input).operations offset).interactionsWith channel.toRaw =
      ((provider.main input).operations offset).interactionsWith channel.toRaw ++
        projections.map (fun pr => (channel.pushedIf (pr.gate input offset) (pr.message input offset)).toRaw) := by
  induction projections generalizing provider with
  | nil => simp [many]
  | cons first rest ih =>
    change (((many (circuit provider channel trivial first) channel trivial rest).main input).operations offset).interactionsWith _ = _
    rw [ih, receipt_interactions]
    simp only [List.map_cons, List.append_assoc, List.singleton_append]

end Circuit.Receipt
