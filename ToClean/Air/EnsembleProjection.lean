module

public import ToClean.Air.EnsembleBuild
public import ToClean.Air.TableBuild

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

/-- View a narrower component through the exact prefix of each physical row. -/
def Table.projectPrefix (table : Table F) (component : Component F)
    (width : component.width ≤ table.component.width)
    (fixed : component.fixedColumns = table.component.fixedColumns) : Table F where
  component := component
  table := table.table.map (·.extract 0 component.width)
  data := table.data
  length_le := by simpa only [List.length_map] using table.length_le
  uniform_width := by
    intro row member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    simp only [Array.size_extract, table.uniform_width original originalMember, Nat.sub_zero,
      Nat.min_eq_left width]
  fixed_rows_match := by
    have original := table.fixed_rows_match
    cases hcolumns : component.fixedColumns with
    | none => simp [Component.FixedRowsMatch, hcolumns]
    | some columns =>
      have bound : columns.width ≤ component.width := by
        have prefixBound := component.fixed_width_le_input
        simp only [Component.width, GeneralFormalCircuit.size_eq]
        simp only [hcolumns, Option.map_some, Option.getD_some] at prefixBound
        omega
      simpa only [Component.FixedRowsMatch, ← fixed, hcolumns, FixedColumns.RowsMatch,
        List.map_map, Function.comp_def, Array.extract_extract, Nat.zero_add,
        Nat.min_eq_left bound] using original

namespace Table

variable (table : Table F) (component : Component F)
  (width : component.width ≤ table.component.width)
  (fixed : component.fixedColumns = table.component.fixedColumns)

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

/-- The component's own prefix is the identical physical table. -/
@[simp] theorem projectPrefix_self : table.projectPrefix table.component le_rfl rfl = table := by
  rw [ext_iff]
  exact ⟨rfl, table.projectPrefix_rows_of_width_eq _ _ _ rfl, rfl⟩

/-- Constraint transport must account for both the row prefix and the actual evaluation data. -/
theorem projectPrefix_constraints_of (sourceData targetData : ProverData F)
    (preserves : ∀ row ∈ table.table,
      table.component.operations.ConstraintsHold (Environment.fromArray row sourceData) →
        component.operations.ConstraintsHold (Environment.fromArray (row.extract 0 component.width) targetData))
    (checked : ({ table with data := sourceData } : Table F).Constraints) :
    ({ table.projectPrefix component width fixed with data := targetData } : Table F).Constraints := by
  intro row member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  exact preserves original originalMember (checked original originalMember)

/-- Channel guarantees transport at their data environments; they are not generally data-free. -/
theorem projectPrefix_channelGuarantees_of (sourceData targetData : ProverData F) (channel : RawChannel F)
    (preserves : ∀ row ∈ table.table,
      table.component.operations.ChannelGuarantees channel (Environment.fromArray row sourceData) →
        component.operations.ChannelGuarantees channel
          (Environment.fromArray (row.extract 0 component.width) targetData))
    (guarantees : ({ table with data := sourceData } : Table F).ChannelGuarantees channel) :
    ({ table.projectPrefix component width fixed with data := targetData } : Table F).ChannelGuarantees channel := by
  intro row member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  exact preserves original originalMember (guarantees original originalMember)

/-- A row-level ledger equation preserves every occurrence and its original order. -/
theorem projectPrefix_interactions (sourceData targetData : ProverData F) (channel : RawChannel F)
    (preserves : ∀ row ∈ table.table,
      component.operations.interactionValuesWith channel
          (Environment.fromArray (row.extract 0 component.width) targetData) =
        table.component.operations.interactionValuesWith channel (Environment.fromArray row sourceData)) :
    ({ table.projectPrefix component width fixed with data := targetData } : Table F).interactionsWith channel =
      ({ table with data := sourceData } : Table F).interactionsWith channel := by
  simp only [interactionsWith, projectPrefix, environment, List.flatMap_map]
  exact congrArg List.flatten (List.map_congr_left preserves)

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
    (verifier : source.VerifierChannelGuarantees original.publicInput original.data channel)
    (guarantees : ∀ table ∈ original.tables, table.ChannelGuarantees channel) :
    other.VerifierChannelGuarantees projected.publicInput projected.data channel ∧
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
      target.tables[index.val].fixedColumns = (source.tables[index.val]'(by omega)).fixedColumns) :
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
    target.tables[index.val].fixedColumns = (source.tables[index.val]'(by omega)).fixedColumns)

@[simp] theorem projectPrefix_publicInput :
    (witness.projectPrefix target length widths fixed).publicInput = witness.publicInput := rfl

/-- Read the original row prefix at the same physical position, with the projected data. -/
theorem projectPrefix_getElem (index : Fin target.tables.length) :
    (witness.projectPrefix target length widths fixed).tables[index.val]'(by
      rw [← (witness.projectPrefix target length widths fixed).same_length]; exact index.isLt) =
      { (witness.tables[index.val]'(by rw [← witness.same_length]; omega)).projectPrefix
        target.tables[index.val]
        (by rw [← witness.same_circuits]; exact widths index)
        (by rw [← witness.same_circuits]; exact fixed index) with
        data := (witness.projectPrefix target length widths fixed).data } := by
  simp only [projectPrefix, ofTables_tables, ofTables_data, withDerivedData,
    List.getElem_map, List.getElem_ofFn]

/-- An unchanged component retains its physical rows, evaluated at the projected data. -/
theorem projectPrefix_getElem_of_same (index : Fin target.tables.length)
    (same : target.tables[index.val] = source.tables[index.val]'(by omega)) :
    (witness.projectPrefix target length widths fixed).tables[index.val]'(by
      rw [← (witness.projectPrefix target length widths fixed).same_length]; exact index.isLt) =
      { witness.tables[index.val]'(by rw [← witness.same_length]; omega) with
        data := (witness.projectPrefix target length widths fixed).data } := by
  simp only [projectPrefix_getElem, same, witness.same_circuits, Table.projectPrefix_self]

/-- Canonical data agrees at an unchanged table's name, even when other keys are dropped. -/
theorem projectPrefix_data_of_same (index : Fin target.tables.length)
    (same : target.tables[index.val] = source.tables[index.val]'(by omega)) (arity : ℕ) :
    (witness.projectPrefix target length widths fixed).data target.tables[index.val].circuit.name arity =
      witness.data target.tables[index.val].circuit.name arity := by
  have projected := (witness.projectPrefix target length widths fixed).data_of_mem_table
    (List.getElem_mem (n := index.val) (by
      rw [← (witness.projectPrefix target length widths fixed).same_length]; exact index.isLt)) arity
  rw [← (witness.projectPrefix target length widths fixed).same_circuits index.val index.isLt,
    projectPrefix_getElem_of_same witness length widths fixed index same] at projected
  rw [projected, same, witness.same_circuits, witness.data_of_mem_table (List.getElem_mem _)]
  rfl

/-- Equal-width components with the same names and input rows retain all keys outside the
removed suffix, even when their constraints or channel interactions differ. -/
theorem projectPrefix_data_of_layout
    (sameWidth : ∀ index : Fin target.tables.length,
      target.tables[index.val].width = (source.tables[index.val]'(by omega)).width)
    (names : ∀ index : Fin target.tables.length,
      target.tables[index.val].circuit.name = (source.tables[index.val]'(by omega)).circuit.name)
    (name : String) (absent : ∀ component ∈ source.tables.drop target.tables.length,
      component.circuit.name ≠ name) (arity : ℕ) :
    (witness.projectPrefix target length widths fixed).data name arity = witness.data name arity := by
  have prefixData : deriveProverData (witness.projectPrefix target length widths fixed).tables =
      deriveProverData (witness.tables.take target.tables.length) := by
    apply deriveProverData_congr
    apply List.forall₂_of_length_eq_of_get
    · simp only [← EnsembleWitness.same_length, List.length_take]
      omega
    · intro index projectedBound originalBound
      have bound : index < target.tables.length := by
        rwa [← EnsembleWitness.same_length] at projectedBound
      simp only [List.get_eq_getElem, List.getElem_take,
        projectPrefix_getElem witness length widths fixed ⟨index, bound⟩]
      refine ⟨?_, fun arity => ?_⟩
      · change (fun c : Component F => c.circuit.name)
          ((witness.projectPrefix target length widths fixed).tables[index].component) =
          (fun c : Component F => c.circuit.name)
            ((witness.tables.take target.tables.length)[index].component)
        rw [List.getElem_take, ← (witness.projectPrefix target length widths fixed).same_circuits,
          ← witness.same_circuits]
        exact names ⟨index, bound⟩
      · simp only [Table.proverRows]
        rw [Table.projectPrefix_rows_of_width_eq]
        rw [← witness.same_circuits]
        exact sameWidth ⟨index, bound⟩
  change deriveProverData _ name arity = deriveProverData witness.tables name arity
  rw [prefixData]
  conv_rhs => rw [← List.take_append_drop target.tables.length witness.tables]
  symm
  apply deriveProverData_append_of_not_mem
  intro table member
  apply absent table.component
  rw [← witness.tables_map_component, ← List.map_drop]
  exact List.mem_map_of_mem member

/-- Retaining an unchanged initial inventory preserves it as complete physical tables. -/
theorem projectPrefix_take (count : ℕ) (bound : count ≤ target.tables.length)
    (same : ∀ index : Fin count,
      target.tables[index.val]'(by omega) = source.tables[index.val]'(by omega)) :
    (witness.projectPrefix target length widths fixed).tables.take count =
      (witness.tables.take count).map (fun table =>
        { table with data := (witness.projectPrefix target length widths fixed).data }) := by
  have projectedLength := (witness.projectPrefix target length widths fixed).same_length
  have sourceLength := witness.same_length
  apply List.ext_getElem
  · simp only [List.length_map, List.length_take, ← projectedLength, ← sourceLength]
    omega
  · intro index hi hj
    have within : index < count := lt_of_lt_of_le hi (List.length_take_le ..)
    simp only [List.getElem_map, List.getElem_take]
    exact projectPrefix_getElem_of_same witness length widths fixed ⟨index, by omega⟩ (same ⟨index, within⟩)

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
  have preserves := preserves
  simp only [projectPrefix, ofTables_data] at preserves
  intro table member row rowMember
  simp only [projectPrefix, ofTables_tables, withDerivedData, List.map_ofFn, Function.comp_def] at member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp rowMember
  have originalTableMember := List.getElem_mem
    (l := witness.tables) (n := index.val) (by rw [← witness.same_length]; omega)
  have checkedRow := checked _ originalTableMember original originalMember
  simp only [Table.environment, witness.same_data _ originalTableMember,
    ← witness.same_circuits index.val (by omega)] at checkedRow
  exact preserves index original
    (by rw [witness.same_circuits]; exact (witness.tables[index.val]'(by rw [← witness.same_length]; omega)).uniform_width original originalMember)
    checkedRow

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
  have preserves := preserves
  simp only [projectPrefix, ofTables_data] at preserves
  intro table member row rowMember
  simp only [projectPrefix, ofTables_tables, withDerivedData, List.map_ofFn, Function.comp_def] at member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp rowMember
  have originalTableMember := List.getElem_mem
    (l := witness.tables) (n := index.val) (by rw [← witness.same_length]; omega)
  have guaranteedRow := guarantees _ originalTableMember original originalMember
  simp only [Table.environment, witness.same_data _ originalTableMember,
    ← witness.same_circuits index.val (by omega)] at guaranteedRow
  exact preserves index original
    (by rw [witness.same_circuits]; exact (witness.tables[index.val]'(by rw [← witness.same_length]; omega)).uniform_width original originalMember)
    guaranteedRow

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
  have front : (List.ofFn fun index : Fin target.tables.length =>
      witness.tables[index.val]'(by rw [← witness.same_length]; omega)) =
      witness.tables.take target.tables.length := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_take]
      rw [Nat.min_eq_left (by rw [← witness.same_length]; exact length)]
    · intro index hi hj
      simp only [List.getElem_ofFn, List.getElem_take]
  rw [← front]
  simp only [projectPrefix, ofTables_tables, withDerivedData, List.map_ofFn,
    List.flatMap, Function.comp_def]
  congr 2
  funext index
  simp only [Table.interactionsWith, Table.projectPrefix, Table.environment, List.flatMap_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro row member
  have sameData := witness.same_data _ (List.getElem_mem
    (l := witness.tables) (n := index.val) (by rw [← witness.same_length]; omega))
  have result := preserves index row
    (by rw [witness.same_circuits]; exact (witness.tables[index.val]'(by rw [← witness.same_length]; omega)).uniform_width row member)
  simp only [projectPrefix, ofTables_data] at result
  simpa only [witness.same_circuits, sameData,
    EnsembleWitness.data, Table.projectPrefix] using result

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
    simp only [verifierInteractionsWith, Ensemble.verifierOperations, verifier, projectPrefix_publicInput]
    exact Operations.interactionValuesWith_congr rfl
  simp only [interactionsWith, verifierLedger, toTables, Tables.interactionsWith]
  rw [projectPrefix_tables_interactions witness length widths fixed channel preserves]
  conv_rhs => rw [← List.take_append_drop target.tables.length witness.tables]
  rw [List.flatMap_append, silent, List.append_nil]

end Prefix
end EnsembleWitness
end Air.Flat
