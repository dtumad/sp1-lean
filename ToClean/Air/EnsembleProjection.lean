module

public import ToClean.Air.EnsembleBuild
public import ToClean.Air.TableBuild
public import ToClean.Air.RowProjection

/-! # Physical prefix projection between flat ensembles

Clean's canonical data is derived from committed rows, so dropping a table or changing its input
layout may change the data environment. This addition projects actual row prefixes with explicit
width and fixed-column proofs. Constraints and channel guarantees require transport at the two
actual data environments; no global data equality is assumed. Complete retained tables preserve
their own named data entries through `EnsembleWitness.data_eq_of_common_table`.

These are proof views of existing rows, not a witness scheduler or extraction path. Exact ledger
transport retains repeated keys, zero multiplicities and occurrence counts. The missing upstream
capability is physical projection with these layout and data obligations, beside FlatEnsemble.
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

/-- View a narrower component through the exact prefix of each physical row.
Its initial data contains those rows; ensemble construction derives the complete shared data. -/
def Table.projectPrefix (table : Table F) (component : Component F)
    (width : component.width ≤ table.component.width)
    (fixed : component.FixedRowsMatch = table.component.FixedRowsMatch) : Table F where
  component := component
  table := table.table.map (·.extract 0 component.width)
  data := {
    tables := fun name n => if name = component.circuit.name then
      ((table.table.map (·.extract 0 component.width)).map (rowPrefix n)).toArray else #[]
    publicInput := table.data.publicInput }
  length_le := by simpa only [List.length_map] using table.length_le
  uniform_width := by
    intro row member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    simp only [Array.size_extract, table.uniform_width original originalMember, Nat.sub_zero,
      Nat.min_eq_left width]
  fixed_rows_match := component.fixedRowsMatch_extract table.table
    (by simp only [Component.width, GeneralFormalCircuit.size_eq]; omega)
    (fixed.symm ▸ table.fixed_rows_match)
  data_consistent := by simp

namespace Table

variable (table : Table F) (component : Component F)
  (width : component.width ≤ table.component.width)
  (fixed : component.FixedRowsMatch = table.component.FixedRowsMatch)

@[simp] theorem projectPrefix_component : (table.projectPrefix component width fixed).component = component := rfl

@[simp] theorem projectPrefix_rows :
    (table.projectPrefix component width fixed).table = table.table.map (·.extract 0 component.width) := rfl

/-- Projection retains the number and order of physical rows. -/
@[simp] theorem projectPrefix_length : (table.projectPrefix component width fixed).length = table.length :=
  List.length_map ..

/-- Equal-width interpretation preserves the literal rows, not just their values. -/
theorem projectPrefix_rows_of_width_eq (same : component.width = table.component.width) :
    (table.projectPrefix component width fixed).table = table.table := by
  rw [projectPrefix_rows]
  calc
    _ = table.table.map (fun row => row) := by
      apply List.map_congr_left
      intro row member
      rw [same, ← table.uniform_width row member, Array.extract_size]
    _ = table.table := List.map_id' _

end Table

namespace EnsembleWitness

variable {source target : Ensemble F PublicIO}

/-- Transfer guarantees along a ledger inclusion and the needed channel-specific data implication.
The original and projected verifiers are included along with their physical tables. -/
theorem channelGuarantees_of_interactions_subset
    {OtherIO : TypeMap} [ProvableType OtherIO] {other : Ensemble F OtherIO}
    (original : EnsembleWitness source) (projected : EnsembleWitness other)
    (channel : RawChannel F)
    (preservesData : ∀ interaction ∈ projected.interactionsWith channel,
      interaction.Guarantees original.data → interaction.Guarantees projected.data)
    (subset : projected.interactionsWith channel ⊆ original.interactionsWith channel)
    (verifier : source.VerifierChannelGuarantees original.data channel)
    (guarantees : ∀ table ∈ original.tables, table.ChannelGuarantees channel) :
    other.VerifierChannelGuarantees projected.data channel ∧
      ∀ table ∈ projected.tables, table.ChannelGuarantees channel := by
  have all : ∀ interaction ∈ projected.interactionsWith channel, interaction.Guarantees projected.data := by
    intro interaction member
    apply preservesData interaction member
    rcases EnsembleWitness.mem_interactionsWith.mp (subset member) with emitted | ⟨table, member, emitted⟩
    · exact EnsembleWitness.verifierChannelGuarantees_iff_forall.mp verifier interaction emitted
    · have shared : table.data = original.data := original.same_data table member
      rw [← shared]
      exact (table.channelGuarantees_iff_forall channel).mp
        (guarantees table member) interaction emitted
  constructor
  · rw [EnsembleWitness.verifierChannelGuarantees_iff_forall]
    intro interaction member
    exact all interaction (EnsembleWitness.mem_interactionsWith.mpr (Or.inl member))
  · intro table member
    rw [table.channelGuarantees_iff_forall channel]
    intro interaction emitted
    rw [projected.same_data table member]
    exact all interaction (EnsembleWitness.mem_interactionsWith.mpr (Or.inr ⟨table, member, emitted⟩))

/-- Retain a physical table prefix, taking the declared target row width at each position.
The target's data is derived from these rows, including any changed input layouts. -/
def projectPrefix (witness : EnsembleWitness source) (target : Ensemble F PublicIO)
    (length : target.tables.length ≤ source.tables.length)
    (widths : ∀ index : Fin target.tables.length,
      target.tables[index.val].width ≤ (source.tables[index.val]'(by omega)).width)
    (fixed : ∀ index : Fin target.tables.length,
      target.tables[index.val].FixedRowsMatch = (source.tables[index.val]'(by omega)).FixedRowsMatch) :
    EnsembleWitness target :=
  ofTables target (List.ofFn fun index : Fin target.tables.length =>
    (witness.tables[index.val]'(by rw [← witness.same_length]; omega)).projectPrefix
      target.tables[index.val]
      (by rw [← witness.same_circuits]; exact widths index)
      (by rw [← witness.same_circuits]; exact fixed index)) witness.publicInput
    (by simp only [List.map_ofFn, Table.projectPrefix_component, Function.comp_def, List.ofFn_getElem])

section Prefix
variable (witness : EnsembleWitness source)
  (length : target.tables.length ≤ source.tables.length)
  (widths : ∀ index : Fin target.tables.length,
    target.tables[index.val].width ≤ (source.tables[index.val]'(by omega)).width)
  (fixed : ∀ index : Fin target.tables.length,
    target.tables[index.val].FixedRowsMatch = (source.tables[index.val]'(by omega)).FixedRowsMatch)

@[simp] theorem projectPrefix_publicInput :
    (witness.projectPrefix target length widths fixed).publicInput = witness.publicInput := rfl

/-- The projected component at each position is the declared target component. -/
@[simp] theorem projectPrefix_getElem_component (index : Fin target.tables.length) :
    ((witness.projectPrefix target length widths fixed).tables[index.val]'(by
      rw [← (witness.projectPrefix target length widths fixed).same_length]; exact index.isLt)).component =
      target.tables[index.val] :=
  ((witness.projectPrefix target length widths fixed).same_circuits index.val index.isLt).symm

/-- Projection retains the exact prefix of every physical row at its original position. -/
theorem projectPrefix_getElem_rows (index : Fin target.tables.length) :
    ((witness.projectPrefix target length widths fixed).tables[index.val]'(by
      rw [← (witness.projectPrefix target length widths fixed).same_length]; exact index.isLt)).table =
      (witness.tables[index.val]'(by rw [← witness.same_length]; omega)).table.map
        (·.extract 0 target.tables[index.val].width) := by
  simp only [projectPrefix, ofTables_tables, withDerivedData, List.getElem_map,
    List.getElem_attach, List.getElem_ofFn, Table.projectPrefix]

/-- Equal component widths retain complete physical rows. -/
theorem projectPrefix_getElem_rows_of_width_eq (index : Fin target.tables.length)
    (same : target.tables[index.val].width = (source.tables[index.val]'(by omega)).width) :
    ((witness.projectPrefix target length widths fixed).tables[index.val]'(by
      rw [← (witness.projectPrefix target length widths fixed).same_length]; exact index.isLt)).table =
      (witness.tables[index.val]'(by rw [← witness.same_length]; omega)).table := by
  rw [projectPrefix_getElem_rows]
  have sourceWidth := witness.same_circuits index.val (by omega)
  rw [same, sourceWidth]
  conv_rhs => rw [← List.map_id (l := (witness.tables[index.val]'(by rw [← witness.same_length]; omega)).table)]
  apply List.map_congr_left
  intro row member
  rw [← (witness.tables[index.val]'(by rw [← witness.same_length]; omega)).uniform_width row member,
    Array.extract_size]
  rfl

/-- Canonical data agrees at an unchanged table's name, even when other keys are dropped. -/
theorem projectPrefix_data_of_same (index : Fin target.tables.length)
    (same : target.tables[index.val] = source.tables[index.val]'(by omega)) (arity : ℕ) :
    (witness.projectPrefix target length widths fixed).data.tables target.tables[index.val].circuit.name arity =
      witness.data.tables target.tables[index.val].circuit.name arity := by
  have projected := (witness.projectPrefix target length widths fixed).data_of_mem_table
    (List.getElem_mem (n := index.val) (by
      rw [← (witness.projectPrefix target length widths fixed).same_length]; exact index.isLt)) arity
  rw [projectPrefix_getElem_component] at projected
  rw [projected, Table.rowPrefixes, projectPrefix_getElem_rows_of_width_eq witness length widths fixed
    index (congrArg Component.width same), same, witness.same_circuits,
    witness.data_of_mem_table (List.getElem_mem _)]
  rfl

/-- Equal-width components with the same names retain every named data entry in the prefix. -/
theorem projectPrefix_data_of_layout
    (sameWidth : ∀ index : Fin target.tables.length,
      target.tables[index.val].width = (source.tables[index.val]'(by omega)).width)
    (names : ∀ index : Fin target.tables.length,
      target.tables[index.val].circuit.name = (source.tables[index.val]'(by omega)).circuit.name)
    (name : String) (absent : ∀ component ∈ source.tables.drop target.tables.length,
      component.circuit.name ≠ name) (arity : ℕ) :
    (witness.projectPrefix target length widths fixed).data.tables name arity =
      witness.data.tables name arity := by
  have prefixData : deriveTables (witness.projectPrefix target length widths fixed).tables =
      deriveTables (witness.tables.take target.tables.length) := by
    apply deriveTables_congr_entries
    apply List.forall₂_of_length_eq_of_get
    · simp only [← EnsembleWitness.same_length, List.length_take]
      omega
    · intro index projectedBound originalBound
      have bound : index < target.tables.length := by
        rwa [← EnsembleWitness.same_length] at projectedBound
      simp only [List.get_eq_getElem, List.getElem_take]
      refine ⟨?_, fun arity => ?_⟩
      · change (fun c : Component F => c.circuit.name)
            ((witness.projectPrefix target length widths fixed).tables[index].component) =
          (fun c : Component F => c.circuit.name) ((witness.tables.take target.tables.length)[index].component)
        rw [List.getElem_take, projectPrefix_getElem_component witness length widths fixed ⟨index, bound⟩,
          ← witness.same_circuits]
        exact names ⟨index, bound⟩
      · simp only [Table.rowPrefixes,
          projectPrefix_getElem_rows_of_width_eq witness length widths fixed ⟨index, bound⟩
            (sameWidth ⟨index, bound⟩)]
  change deriveTables _ name arity = deriveTables witness.tables name arity
  rw [prefixData]
  conv_rhs => rw [← List.take_append_drop target.tables.length witness.tables]
  symm
  apply deriveTables_append_of_not_mem
  intro table member
  apply absent table.component
  rw [← witness.tables_map_component, ← List.map_drop]
  exact List.mem_map_of_mem member

/-- Retaining the complete name and row layout preserves both canonical table data and public input. -/
theorem projectPrefix_data_eq_of_layout
    (sameWidth : ∀ index : Fin target.tables.length,
      target.tables[index.val].width = (source.tables[index.val]'(by omega)).width)
    (names : ∀ index : Fin target.tables.length,
      target.tables[index.val].circuit.name = (source.tables[index.val]'(by omega)).circuit.name)
    (sameLength : target.tables.length = source.tables.length) :
    (witness.projectPrefix target length widths fixed).data = witness.data := by
  change ProverData.mk _ (toElements witness.publicInput).toArray = ProverData.mk _ _
  apply congrArg (fun tables => ProverData.mk tables (toElements witness.publicInput).toArray)
  funext name arity
  apply witness.projectPrefix_data_of_layout length widths fixed sameWidth names name ?_ arity
  rw [sameLength, List.drop_length]
  simp

/-- An unchanged initial inventory retains its components and complete row arrays. -/
theorem projectPrefix_take (count : ℕ) (bound : count ≤ target.tables.length)
    (same : ∀ index : Fin count,
      target.tables[index.val]'(by omega) = source.tables[index.val]'(by omega)) :
    ((witness.projectPrefix target length widths fixed).tables.take count).map
        (fun table => (table.component, table.table)) =
      (witness.tables.take count).map (fun table => (table.component, table.table)) := by
  have projectedLength := (witness.projectPrefix target length widths fixed).same_length
  have sourceLength := witness.same_length
  apply List.ext_getElem
  · simp only [List.length_map, List.length_take, ← projectedLength, ← sourceLength]
    omega
  · intro index hi hj
    have within : index < count := by
      simp only [List.length_map, List.length_take] at hi
      omega
    simp only [List.getElem_map, List.getElem_take]
    apply Prod.ext
    · rw [projectPrefix_getElem_component witness length widths fixed ⟨index, by omega⟩,
        same ⟨index, within⟩, witness.same_circuits]
    · exact projectPrefix_getElem_rows_of_width_eq witness length widths fixed ⟨index, by omega⟩
        (congrArg Component.width (same ⟨index, within⟩))

/-- Project constraints using each component's proved implication at the actual two data environments. -/
theorem projectPrefix_constraints_of
    (preserves : ∀ index : Fin target.tables.length, ∀ row,
      row.size = (source.tables[index.val]'(by omega)).width →
      (source.tables[index.val]'(by omega)).operations.ConstraintsHold
          (Environment.fromArray row witness.data) →
        target.tables[index.val].operations.ConstraintsHold
          (Environment.fromArray (row.extract 0 target.tables[index.val].width)
            (witness.projectPrefix target length widths fixed).data))
    (checked : witness.Constraints) : (witness.projectPrefix target length widths fixed).Constraints := by
  intro table member row rowMember
  obtain ⟨index, within, rfl⟩ := List.mem_iff_getElem.mp member
  have indexBound : index < target.tables.length := by
    rwa [← EnsembleWitness.same_length] at within
  rw [projectPrefix_getElem_rows witness length widths fixed ⟨index, indexBound⟩] at rowMember
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp rowMember
  have originalTableMember := List.getElem_mem
    (l := witness.tables) (n := index) (by rw [← witness.same_length]; omega)
  have checkedRow := checked _ originalTableMember original originalMember
  simp only [Table.environment, witness.same_data _ originalTableMember,
    ← witness.same_circuits index (by omega)] at checkedRow
  have result := preserves ⟨index, indexBound⟩ original
    (by rw [witness.same_circuits]; exact (witness.tables[index]'(by rw [← witness.same_length]; omega)).uniform_width original originalMember)
    checkedRow
  simpa only [Table.environment, EnsembleWitness.data,
    (witness.projectPrefix target length widths fixed).same_data _ (List.getElem_mem within),
    ← (witness.projectPrefix target length widths fixed).same_circuits index indexBound] using result

/-- Channel guarantees have their own data transport obligation, independent of balance. -/
theorem projectPrefix_channelGuarantees_of (channel : RawChannel F)
    (preserves : ∀ index : Fin target.tables.length, ∀ row,
      row.size = (source.tables[index.val]'(by omega)).width →
      (source.tables[index.val]'(by omega)).operations.ChannelGuarantees channel
          (Environment.fromArray row witness.data) →
        target.tables[index.val].operations.ChannelGuarantees channel
          (Environment.fromArray (row.extract 0 target.tables[index.val].width)
            (witness.projectPrefix target length widths fixed).data))
    (guarantees : ∀ table ∈ witness.tables, table.ChannelGuarantees channel) :
    ∀ table ∈ (witness.projectPrefix target length widths fixed).tables,
      table.ChannelGuarantees channel := by
  intro table member row rowMember
  obtain ⟨index, within, rfl⟩ := List.mem_iff_getElem.mp member
  have indexBound : index < target.tables.length := by
    rwa [← EnsembleWitness.same_length] at within
  rw [projectPrefix_getElem_rows witness length widths fixed ⟨index, indexBound⟩] at rowMember
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp rowMember
  have originalTableMember := List.getElem_mem
    (l := witness.tables) (n := index) (by rw [← witness.same_length]; omega)
  have guaranteedRow := guarantees _ originalTableMember original originalMember
  simp only [Table.environment, witness.same_data _ originalTableMember,
    ← witness.same_circuits index (by omega)] at guaranteedRow
  have result := preserves ⟨index, indexBound⟩ original
    (by rw [witness.same_circuits]; exact (witness.tables[index]'(by rw [← witness.same_length]; omega)).uniform_width original originalMember)
    guaranteedRow
  simpa only [Table.environment, EnsembleWitness.data,
    (witness.projectPrefix target length widths fixed).same_data _ (List.getElem_mem within),
    ← (witness.projectPrefix target length widths fixed).same_circuits index indexBound] using result

/-- Per-row equalities preserve the projected physical ledger, with its full multiplicity and order. -/
theorem projectPrefix_tables_interactions (channel : RawChannel F)
    (preserves : ∀ index : Fin target.tables.length, ∀ row,
      row.size = (source.tables[index.val]'(by omega)).width →
      target.tables[index.val].operations.interactionValuesWith channel
          (Environment.fromArray (row.extract 0 target.tables[index.val].width)
            (witness.projectPrefix target length widths fixed).data) =
        (source.tables[index.val]'(by omega)).operations.interactionValuesWith channel
          (Environment.fromArray row witness.data)) :
    (witness.projectPrefix target length widths fixed).tables.flatMap
        (·.interactionsWith channel) =
      (witness.tables.take target.tables.length).flatMap (·.interactionsWith channel) := by
  apply congrArg List.flatten
  apply List.ext_getElem
  · simp only [List.length_map, List.length_take, ← EnsembleWitness.same_length]
    omega
  · intro index projectedBound originalBound
    have indexBound : index < target.tables.length := by
      simpa only [List.length_map, ← EnsembleWitness.same_length] using projectedBound
    simp only [List.getElem_map, List.getElem_take, Table.interactionsWith,
      projectPrefix_getElem_rows witness length widths fixed ⟨index, indexBound⟩, List.flatMap_map]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro row member
    have sourceBound : index < witness.tables.length := by rw [← witness.same_length]; omega
    have result := preserves ⟨index, indexBound⟩ row
      (by rw [witness.same_circuits]; exact (witness.tables[index]'sourceBound).uniform_width row member)
    simpa only [Table.environment, EnsembleWitness.data, EnsembleWitness.data,
      (witness.projectPrefix target length widths fixed).same_data _ (List.getElem_mem (by
        rw [← EnsembleWitness.same_length]; exact indexBound)),
      witness.same_data _ (List.getElem_mem sourceBound),
      ← (witness.projectPrefix target length widths fixed).same_circuits index indexBound,
      ← witness.same_circuits index (by omega)] using result

/-- An unchanged verifier and a silent removed suffix preserve the complete selected-channel ledger. -/
theorem projectPrefix_interactions (verifier : target.verifier = source.verifier) (channel : RawChannel F)
    (preserves : ∀ index : Fin target.tables.length, ∀ row,
      row.size = (source.tables[index.val]'(by omega)).width →
      target.tables[index.val].operations.interactionValuesWith channel
          (Environment.fromArray (row.extract 0 target.tables[index.val].width)
            (witness.projectPrefix target length widths fixed).data) =
        (source.tables[index.val]'(by omega)).operations.interactionValuesWith channel
          (Environment.fromArray row witness.data))
    (silent : (witness.tables.drop target.tables.length).flatMap (·.interactionsWith channel) = []) :
    (witness.projectPrefix target length widths fixed).interactionsWith channel = witness.interactionsWith channel := by
  have verifierLedger : (witness.projectPrefix target length widths fixed).verifierInteractionsWith channel =
      witness.verifierInteractionsWith channel := by
    simp only [verifierInteractionsWith, Ensemble.verifierOperations, verifier]
    exact Operations.interactionValuesWith_congr rfl
  simp only [interactionsWith, verifierLedger, toTables, Tables.interactionsWith]
  rw [projectPrefix_tables_interactions witness length widths fixed channel preserves]
  conv_rhs => rw [← List.take_append_drop target.tables.length witness.tables]
  rw [List.flatMap_append, silent, List.append_nil]

end Prefix
end EnsembleWitness
end Air.Flat
