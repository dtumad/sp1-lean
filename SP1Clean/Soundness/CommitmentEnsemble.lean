import SP1Clean.Native.Operations.CommitmentStatement
import SP1Clean.Native.Operations.CommitmentBoundary
import ToClean.Air.EnsembleProjection
import ToClean.Air.TableBuild

/-! # Installing the immutable commitment statement

The fixed declaration provider and public assertions share one verifier-owned statement.
Existing physical positions are preserved. The new table uses Clean's ordinary preprocessed
payload provider; neither the prover's mutable bank nor per-call PublicValues echoes select it.
Forgetting the provider and the statement checks returns the original assembly's rows. Canonical
data changes only at the provider's name, so lookup-free original components keep their
constraints, and every original channel other than the declarations keeps its balance.
-/

namespace SP1Clean.Soundness.CommitmentEnsemble

open Circuit Air.Flat Model.Core

variable {p : ℕ} [Fact p.Prime]

/-- Append the provider, retaining every original row, channel occurrence and table position. -/
def withSource (statement : CommitmentStatement) (base : Ensemble (ZMod p) SP1PublicIO)
    (fresh : (CommitmentDeclaration.source (p := p) statement).circuit.name ∉ base.tables.map (·.circuit.name)) :
    Ensemble (ZMod p) SP1PublicIO where
  tables := base.tables ++ [CommitmentDeclaration.source statement]
  unique_names := by
    simpa only [List.map_append, List.map_cons, List.map_nil, List.concat_eq_append] using base.unique_names.concat fresh
  channels := base.channels ++ [CommitmentDeclaration.channel.toRaw]
  verifier := base.verifier

/-- Public bytes, deferred elements and flags are bound to the same fixed provider. -/
def install (statement : CommitmentStatement) (base : Ensemble (ZMod p) SP1PublicIO)
    (fresh : (CommitmentDeclaration.source (p := p) statement).circuit.name ∉ base.tables.map (·.circuit.name)) :
    Ensemble (ZMod p) SP1PublicIO :=
  (CommitmentBoundary.checker statement).install (withSource statement base fresh)

/-- Forget the statement checks and the appended provider, retaining every original physical row. -/
def project {statement : CommitmentStatement} {base : Ensemble (ZMod p) SP1PublicIO}
    {fresh : (CommitmentDeclaration.source (p := p) statement).circuit.name ∉ base.tables.map (·.circuit.name)}
    (witness : EnsembleWitness (install statement base fresh)) : EnsembleWitness base :=
  ((CommitmentBoundary.checker statement).project witness).projectPrefix base
    (by simp [withSource])
    (fun index => by simp [withSource, List.getElem_append_left index.isLt])
    (fun index => by simp [withSource, List.getElem_append_left index.isLt])

variable {statement : CommitmentStatement} {base : Ensemble (ZMod p) SP1PublicIO}
  {fresh : (CommitmentDeclaration.source (p := p) statement).circuit.name ∉ base.tables.map (·.circuit.name)}

@[simp] theorem project_publicInput (witness : EnsembleWitness (install statement base fresh)) :
    (project witness).publicInput = witness.publicInput := rfl

/-- Lookup-free original components keep their constraints across the changed canonical data. -/
theorem project_constraints (witness : EnsembleWitness (install statement base fresh))
    (lookupFree : ∀ component ∈ base.tables, component.operations.lookups = [])
    (checked : witness.Constraints) : (project witness).Constraints := by
  apply EnsembleWitness.projectPrefix_constraints_of _ _ _ _ ?_
    (((CommitmentBoundary.checker statement).project_constraints witness).mp checked)
  intro index row width valid
  have same : (withSource statement base fresh).tables[index.val]'(by simp [withSource]) =
      base.tables[index.val] := List.getElem_append_left index.isLt
  rw [same] at valid width
  rw [← width, Array.extract_size]
  exact Component.constraintsHold_setData _ (lookupFree _ (List.getElem_mem _)) valid

/-- Every original channel except the declarations keeps its complete ledger and balance. -/
theorem project_balancedChannel (witness : EnsembleWitness (install statement base fresh))
    (balanced : witness.BalancedChannels) (channel : RawChannel (ZMod p))
    (registered : channel ∈ base.channels) (different : channel ≠ CommitmentDeclaration.channel.toRaw) :
    (project witness).BalancedChannel channel := by
  have source := (((CommitmentBoundary.checker statement).project_balanced_iff witness).mp balanced).1
  let retained := (CommitmentBoundary.checker statement).project witness
  have preserves : ∀ index : Fin base.tables.length, ∀ row,
      row.size = ((withSource statement base fresh).tables[index.val]'(by simp [withSource])).width →
      base.tables[index.val].operations.interactionValuesWith channel
          (Environment.fromArray (row.extract 0 base.tables[index.val].width) (project witness).data) =
        ((withSource statement base fresh).tables[index.val]'(by simp [withSource])).operations.interactionValuesWith
          channel (Environment.fromArray row retained.data) := by
    intro index row width
    have same : (withSource statement base fresh).tables[index.val]'(by simp [withSource]) =
        base.tables[index.val] := List.getElem_append_left index.isLt
    rw [same] at width ⊢
    rw [← width, Array.extract_size]
    exact Component.interactionValuesWith_setData _ channel
  have silent : (retained.tables.drop base.tables.length).flatMap (·.interactionsWith channel) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro table member
    apply table.interactionsWith_nil_of_channel_not_mem
    have components := congrArg (List.drop base.tables.length) retained.tables_map_component
    rw [← List.map_drop] at components
    change _ = (base.tables ++ [CommitmentDeclaration.source statement]).drop base.tables.length at components
    rw [List.drop_left] at components
    have provider : table.component = CommitmentDeclaration.source statement := by
      have mapped := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
      rw [components] at mapped
      exact List.mem_singleton.mp mapped
    rw [provider]
    simp only [CommitmentDeclaration.source, StaticTable.payloadComponent, StaticTable.payloadProvider]
    simp only [circuit_norm, List.mem_append, List.mem_singleton, not_or]
    exact ⟨List.not_mem_nil, different⟩
  have ledger : (project witness).interactionsWith channel = retained.interactionsWith channel :=
    retained.projectPrefix_interactions (target := base) _ _ _ rfl channel preserves silent
  change BalancedInteractions ((project witness).interactionsWith channel)
  rw [ledger]
  exact source channel (List.mem_append_left _ registered)

end SP1Clean.Soundness.CommitmentEnsemble
