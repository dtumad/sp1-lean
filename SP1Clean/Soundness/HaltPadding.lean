import SP1Clean.Native.Chips.HaltPaddingChip

/-! # Installing the padding-only legacy HALT table

Only a local selector assertion is added. Projection retains all arrays, all channels, the
verifier, and shared data; the existing execution engine can therefore consume the same rows.
-/

namespace SP1Clean.Soundness.HaltPadding

open Circuit Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
  {PublicIO : TypeMap} [ProvableType PublicIO]

def install (ens : Ensemble (ZMod p) PublicIO) (index : Fin ens.tables.length) : Ensemble (ZMod p) PublicIO :=
  { ens with tables := ens.tables.set index.val HaltPaddingChip.component }

variable {ens : Ensemble (ZMod p) PublicIO} {index : Fin ens.tables.length}

private theorem bound (witness : EnsembleWitness (install ens index)) : index.val < witness.tables.length := by
  rw [← witness.same_length]
  simpa only [install, List.length_set] using index.isLt

def project (same : ens.tables[index.val] = HaltPaddingChip.original)
    (witness : EnsembleWitness (install ens index)) : EnsembleWitness ens :=
  EnsembleWitness.ofTables ens
    (witness.tables.set index.val ((witness.tables[index.val]'(bound witness)).withComponent HaltPaddingChip.original))
    witness.data witness.publicInput
    (by
      rw [List.map_set, witness.tables_map_component]
      change (ens.tables.set index.val HaltPaddingChip.component).set index.val HaltPaddingChip.original = ens.tables
      rw [List.set_set, ← same, List.set_getElem_self])
    (by
      intro table member
      rcases List.mem_or_eq_of_mem_set member with old | rfl
      · exact witness.same_data table old
      · change (witness.tables[index.val]'(bound witness)).data = witness.data
        exact witness.same_data _ (List.getElem_mem _))

theorem table_component (witness : EnsembleWitness (install ens index)) :
    (witness.tables[index.val]'(bound witness)).component = HaltPaddingChip.component := by
  rw [← witness.same_circuits]
  exact List.getElem_set_self (by simpa only [install, List.length_set] using index.isLt)

theorem constraints (same : ens.tables[index.val] = HaltPaddingChip.original)
    (witness : EnsembleWitness (install ens index)) (checked : witness.Constraints) :
    (project same witness).Constraints := by
  rw [EnsembleWitness.Constraints, EnsembleWitness.forall_mem_allTables_iff]
  refine ⟨?_, ?_⟩
  · exact checked witness.verifierTable witness.mem_allTables_verifierTable
  · intro table member
    rcases List.mem_or_eq_of_mem_set member with old | rfl
    · exact checked table (witness.mem_allTables_of_mem_tables old)
    · apply Table.withComponent_constraints_of
      · rw [table_component]
        exact fun env valid => ((HaltPaddingChip.constraints env).mp valid).1
      · exact checked _ (witness.mem_allTables_of_mem_tables (List.getElem_mem _))

theorem interactions (same : ens.tables[index.val] = HaltPaddingChip.original)
    (witness : EnsembleWitness (install ens index)) (channel : RawChannel (ZMod p)) :
    (project same witness).interactionsWith channel = witness.interactionsWith channel := by
  have row := Table.withComponent_interactions (witness.tables[index.val]'(bound witness))
    HaltPaddingChip.original channel (by rw [table_component, HaltPaddingChip.interactions])
  change witness.verifierTable.interactionsWith channel ++
      (witness.tables.set index.val _).flatMap (·.interactionsWith channel) =
    witness.verifierTable.interactionsWith channel ++ witness.tables.flatMap (·.interactionsWith channel)
  congr 1
  rw [List.flatMap, List.map_set, row, ← List.getElem_map (l := witness.tables) (i := index.val)
    (f := fun table : Table (ZMod p) => table.interactionsWith channel), List.set_getElem_self]
  · rfl
  · simpa only [List.length_map] using bound witness

theorem balanced (same : ens.tables[index.val] = HaltPaddingChip.original)
    (witness : EnsembleWitness (install ens index)) (balance : witness.BalancedChannels) :
    (project same witness).BalancedChannels := by
  intro channel member
  change BalancedInteractions ((project same witness).interactionsWith channel)
  rw [interactions]
  exact balance channel member

theorem drop_tables (same : ens.tables[index.val] = HaltPaddingChip.original)
    (witness : EnsembleWitness (install ens index)) (count : ℕ) (after : index.val < count) :
    (project same witness).tables.drop count = witness.tables.drop count :=
  List.drop_set_of_lt after

end SP1Clean.Soundness.HaltPadding
