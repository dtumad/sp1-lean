module

public import ToClean.Air.EnsembleBuild

/-! # Physical witness projection between flat ensembles

Upstream Clean can split an ensemble's table list, but cannot replace components while retaining
their physical rows. An extension that adds only interactions needs this transport: project a
prefix to its original components, prove preservation of assertions and lookups, and compare each
retained channel's exact ledger. Neither row validity nor channel balance is assumed by the
constructor. The lemmas below expose the corresponding proof obligations over opaque components.
Pointwise constraint and channel-guarantee transports also support extensions that add witness
cells or requirements. Individual channels can be retained without projecting global balance.
-/

@[expose] public section

namespace Operations

variable {F : Type} [FiniteField F]

/-- Retaining a subset of one channel's actual interactions retains its local guarantees. -/
theorem channelGuarantees_of_interactionsWith_subset (original extended : Operations F)
    (channel : RawChannel F) (subset : original.interactionsWith channel ⊆ extended.interactionsWith channel)
    (env : Environment F) (guarantees : extended.ChannelGuarantees channel env) :
    original.ChannelGuarantees channel env := by
  intro interaction member same
  have selected : interaction ∈ original.interactionsWith channel := List.mem_filter.mpr ⟨member, by simp [same]⟩
  exact guarantees interaction (List.mem_filter.mp (subset selected)).1 same

/-- The corresponding transport for local channel requirements. -/
theorem channelRequirements_of_interactionsWith_subset (original extended : Operations F)
    (channel : RawChannel F) (subset : original.interactionsWith channel ⊆ extended.interactionsWith channel)
    (env : Environment F) (requirements : extended.ChannelRequirements channel env) :
    original.ChannelRequirements channel env := by
  intro interaction member same
  have selected : interaction ∈ original.interactionsWith channel := List.mem_filter.mpr ⟨member, by simp [same]⟩
  exact requirements interaction (List.mem_filter.mp (subset selected)).1 same

end Operations

namespace Air.Flat

variable {F : Type} [FiniteField F] {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Replace only the component interpreting a table's unchanged physical rows. -/
def Table.withComponent (table : Table F) (component : Component F) : Table F :=
  { table with component := component }

theorem Table.withComponent_constraints (table : Table F) (component : Component F)
    (assertions : component.operations.constraints = table.component.operations.constraints)
    (lookups : component.operations.lookups = table.component.operations.lookups) :
    (table.withComponent component).Constraints ↔ table.Constraints := by
  simp only [Constraints, withComponent, environment, Operations.ConstraintsHold, assertions, lookups]

theorem Table.withComponent_interactions (table : Table F) (component : Component F)
    (channel : RawChannel F)
    (same : component.operations.interactionsWith channel =
      table.component.operations.interactionsWith channel) :
    (table.withComponent component).interactionsWith channel = table.interactionsWith channel := by
  simp only [interactionsWith, withComponent, environment, Operations.interactionValuesWith, same]

/-- A stronger component can project constraints without equality of assertion lists. -/
theorem Table.withComponent_constraints_of (table : Table F) (component : Component F)
    (preserves : ∀ env, table.component.operations.ConstraintsHold env → component.operations.ConstraintsHold env)
    (constraints : table.Constraints) : (table.withComponent component).Constraints :=
  fun row member => preserves _ (constraints row member)

/-- Local channel guarantees transport independently of the table's multiplicities on that channel. -/
theorem Table.withComponent_channelGuarantees_of (table : Table F) (component : Component F)
    (channel : RawChannel F)
    (preserves : ∀ env, table.component.operations.ChannelGuarantees channel env →
      component.operations.ChannelGuarantees channel env)
    (guarantees : table.ChannelGuarantees channel) : (table.withComponent component).ChannelGuarantees channel :=
  fun row member => preserves _ (guarantees row member)

namespace EnsembleWitness

variable {source target : Ensemble F PublicIO}

/-- Transfer channel guarantees along the actual evaluated ledger, with shared prover data.
Unlike balance, this property survives dropping interactions and does not require equal public
input types or matching table layouts. -/
theorem channelGuarantees_of_interactions_subset
    {OtherIO : TypeMap} [ProvableType OtherIO] {other : Ensemble F OtherIO}
    (original : EnsembleWitness source) (projected : EnsembleWitness other)
    (channel : RawChannel F) (data : projected.data = original.data)
    (subset : projected.interactionsWith channel ⊆ original.interactionsWith channel)
    (guarantees : ∀ table ∈ original.allTables, table.ChannelGuarantees channel) :
    ∀ table ∈ projected.allTables, table.ChannelGuarantees channel := by
  intro table member
  rw [Table.channelGuarantees_iff_forall, projected.data_eq_of_mem_allTables table member, data]
  intro interaction present
  obtain ⟨sourceTable, sourceMember, emitted⟩ := EnsembleWitness.mem_interactionsWith.mp
    (subset (EnsembleWitness.mem_interactionsWith.mpr ⟨table, member, present⟩))
  have valid := (sourceTable.channelGuarantees_iff_forall channel).mp
    (guarantees sourceTable sourceMember) interaction emitted
  rwa [original.data_eq_of_mem_allTables sourceTable sourceMember] at valid

/-- Retain a physical prefix and interpret it using the target's components. -/
def project (witness : EnsembleWitness source) (target : Ensemble F PublicIO)
    (length : target.tables.length ≤ source.tables.length) : EnsembleWitness target :=
  ofTables target (List.ofFn fun index : Fin target.tables.length =>
    (witness.tables[index.val]'(by rw [← witness.same_length]; omega)).withComponent
      target.tables[index.val]) witness.data witness.publicInput
    (by simp only [List.map_ofFn, Table.withComponent, Function.comp_def, List.ofFn_getElem])
    (by
      intro table member
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
      exact witness.same_data
        (witness.tables[index.val]'(by rw [← witness.same_length]; omega)) (List.getElem_mem _))

theorem project_getElem (witness : EnsembleWitness source)
    (length : target.tables.length ≤ source.tables.length) (index : Fin target.tables.length) :
    (witness.project target length).tables[index.val]'(by
      rw [← (witness.project target length).same_length]; exact index.isLt) =
      (witness.tables[index.val]'(by rw [← witness.same_length]; omega)).withComponent
        target.tables[index.val] := by
  simp only [project, ofTables_tables, List.getElem_ofFn]

/-- Reinterpreting a physical prefix preserves its shared prover data. -/
@[simp] theorem project_data (witness : EnsembleWitness source)
    (length : target.tables.length ≤ source.tables.length) :
    (witness.project target length).data = witness.data := by
  simp only [project, ofTables_data]

theorem project_verifierTable (witness : EnsembleWitness source)
    (length : target.tables.length ≤ source.tables.length)
    (verifier : target.verifier = source.verifier) :
    (witness.project target length).verifierTable = witness.verifierTable :=
  Ensemble.verifierTable_ext verifier rfl rfl

/-- A projection preserves an unchanged initial inventory as complete physical tables. -/
theorem project_take (witness : EnsembleWitness source)
    (length : target.tables.length ≤ source.tables.length) (count : ℕ)
    (bound : count ≤ target.tables.length)
    (same : ∀ index : Fin count,
      target.tables[index.val]'(by omega) = source.tables[index.val]'(by omega)) :
    (witness.project target length).tables.take count = witness.tables.take count := by
  have projectedLength := (witness.project target length).same_length
  have sourceLength := witness.same_length
  apply List.ext_getElem
  · simp only [List.length_take, ← projectedLength, ← sourceLength]
    omega
  · intro index hi hj
    have within : index < count := lt_of_lt_of_le hi (List.length_take_le ..)
    simp only [List.getElem_take]
    rw [project_getElem witness length ⟨index, by omega⟩]
    rw [same ⟨index, within⟩, witness.same_circuits]
    rfl

theorem project_constraints (witness : EnsembleWitness source)
    (length : target.tables.length ≤ source.tables.length)
    (verifier : target.verifier = source.verifier)
    (assertions : ∀ index : Fin target.tables.length,
      target.tables[index.val].operations.constraints =
        (source.tables[index.val]'(by omega)).operations.constraints)
    (lookups : ∀ index : Fin target.tables.length,
      target.tables[index.val].operations.lookups =
        (source.tables[index.val]'(by omega)).operations.lookups)
    (constraints : witness.Constraints) : (witness.project target length).Constraints := by
  rw [Constraints, forall_mem_allTables_iff]
  refine ⟨?_, ?_⟩
  · rw [project_verifierTable witness length verifier]
    exact constraints _ witness.mem_allTables_verifierTable
  · intro table member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    apply (Table.withComponent_constraints _ _ ?_ ?_).mpr
    · exact constraints _ (witness.mem_allTables_of_mem_tables (List.getElem_mem _))
    · rw [← witness.same_circuits]
      exact assertions index
    · rw [← witness.same_circuits]
      exact lookups index

/-- Project a strengthened prefix using a static implication for each component's constraints. -/
theorem project_constraints_of (witness : EnsembleWitness source)
    (length : target.tables.length ≤ source.tables.length)
    (verifier : target.verifier = source.verifier)
    (preserves : ∀ index : Fin target.tables.length, ∀ env,
      (source.tables[index.val]'(by omega)).operations.ConstraintsHold env →
        target.tables[index.val].operations.ConstraintsHold env)
    (constraints : witness.Constraints) : (witness.project target length).Constraints := by
  rw [Constraints, forall_mem_allTables_iff]
  refine ⟨?_, ?_⟩
  · rw [project_verifierTable witness length verifier]
    exact constraints _ witness.mem_allTables_verifierTable
  · intro table member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    apply Table.withComponent_constraints_of
    · rw [← witness.same_circuits]
      exact preserves index
    · exact constraints _ (witness.mem_allTables_of_mem_tables (List.getElem_mem _))

/-- Guarantees from the larger witness survive per-component projection without channel balance
in the projected witness. This permits extra Byte lookups and Memory effects in an extension. -/
theorem project_channelGuarantees_of (witness : EnsembleWitness source)
    (length : target.tables.length ≤ source.tables.length)
    (verifier : target.verifier = source.verifier) (channel : RawChannel F)
    (preserves : ∀ index : Fin target.tables.length, ∀ env,
      (source.tables[index.val]'(by omega)).operations.ChannelGuarantees channel env →
        target.tables[index.val].operations.ChannelGuarantees channel env)
    (guarantees : ∀ table ∈ witness.allTables, table.ChannelGuarantees channel) :
    ∀ table ∈ (witness.project target length).allTables, table.ChannelGuarantees channel := by
  rw [forall_mem_allTables_iff]
  refine ⟨?_, ?_⟩
  · rw [project_verifierTable witness length verifier]
    exact guarantees _ witness.mem_allTables_verifierTable
  · intro table member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    apply Table.withComponent_channelGuarantees_of
    · rw [← witness.same_circuits]
      exact preserves index
    · exact guarantees _ (witness.mem_allTables_of_mem_tables (List.getElem_mem _))

theorem project_tables_interactions (witness : EnsembleWitness source)
    (length : target.tables.length ≤ source.tables.length) (channel : RawChannel F)
    (same : ∀ index : Fin target.tables.length,
      target.tables[index.val].operations.interactionsWith channel =
        (source.tables[index.val]'(by omega)).operations.interactionsWith channel) :
    (witness.project target length).tables.flatMap (·.interactionsWith channel) =
      (witness.tables.take target.tables.length).flatMap (·.interactionsWith channel) := by
  have front : (List.ofFn fun index : Fin target.tables.length =>
      witness.tables[index.val]'(by rw [← witness.same_length]; omega)) =
      witness.tables.take target.tables.length := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_take]
      rw [Nat.min_eq_left (by rw [← witness.same_length]; exact length)]
    · intro index hi hj
      simp only [List.getElem_ofFn, List.getElem_take]
  rw [← front]
  change (List.ofFn _).flatMap _ = _
  simp only [List.flatMap, List.map_ofFn, Function.comp_def]
  congr 2
  funext index
  apply Table.withComponent_interactions
  rw [← witness.same_circuits]
  exact same index

theorem project_interactions (witness : EnsembleWitness source)
    (length : target.tables.length ≤ source.tables.length)
    (verifier : target.verifier = source.verifier) (channel : RawChannel F)
    (same : ∀ index : Fin target.tables.length,
      target.tables[index.val].operations.interactionsWith channel =
        (source.tables[index.val]'(by omega)).operations.interactionsWith channel)
    (silent : (witness.tables.drop target.tables.length).flatMap (·.interactionsWith channel) = []) :
    (witness.project target length).interactionsWith channel = witness.interactionsWith channel := by
  simp only [interactionsWith, allTables, List.flatMap_cons]
  rw [project_verifierTable witness length verifier, project_tables_interactions witness length channel same]
  conv_rhs => rw [← List.take_append_drop target.tables.length witness.tables]
  rw [List.flatMap_append, silent, List.append_nil]

end EnsembleWitness
end Air.Flat
