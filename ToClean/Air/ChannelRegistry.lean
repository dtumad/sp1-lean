module

public import ToClean.Air.EnsembleBuild

/-! # Reindexing an ensemble's channel registry

Clean requires unique channel names and complete coverage. This addition reorders the registry
while preserving both invariants: physical tables, the public verifier, data,
public inputs, and every interaction occurrence remain unchanged. Full `RawChannel` membership,
including the channel predicate, is the required equivalence; matching names alone is insufficient.
-/

@[expose] public section

namespace Air.Flat

variable {F : Type} [FiniteField F] {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Reorder the channel registry, preserving unique names and complete channel coverage. -/
def Ensemble.withChannels (ens : Ensemble F PublicIO) (channels : List (RawChannel F))
    (same : channels.Perm ens.channels) : Ensemble F PublicIO :=
  { ens with
    channels
    unique_channel_names := (same.map RawChannel.name).nodup_iff.mpr ens.unique_channel_names
    tables_channels := fun table member _ used => same.mem_iff.mpr (ens.tables_channels table member used)
    verifier_channels := fun _ used => same.mem_iff.mpr (ens.verifier_channels used) }

/-- Reuse the identical witness after reordering only the channel registry. -/
def EnsembleWitness.withChannels {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens)
    (channels : List (RawChannel F)) (same : channels.Perm ens.channels) :
    EnsembleWitness (ens.withChannels channels same) :=
  witness.withEnsemble _ rfl

/-- Changing registry order preserves all raw assertions and lookups. -/
theorem EnsembleWitness.withChannels_constraints {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness ens) (channels : List (RawChannel F)) (same) :
    (witness.withChannels channels same).Constraints ↔ witness.Constraints := Iff.rfl

/-- Channel permutation preserves the abstract balance facts. -/
theorem EnsembleWitness.withChannels_balanced {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness ens) (channels : List (RawChannel F)) (same) :
    (witness.withChannels channels same).BalancedChannels ↔ witness.BalancedChannels := by
  change (∀ channel ∈ channels, witness.BalancedChannel channel) ↔
    ∀ channel ∈ ens.channels, witness.BalancedChannel channel
  simp only [same.mem_iff]

end Air.Flat
