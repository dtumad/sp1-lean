import SP1Clean.Proofs.Completeness.ByteProviderDemand

/-! # Building the registered Byte and Range tables from their counted requests -/

namespace SP1Clean.Soundness.ByteProviderDemand
open Air.Flat LookupAccessList

variable {p : ℕ} [Fact p.Prime] [Fact (2^25 < p)]
private local instance providerTablesWordBound : Fact (2^24 < p) := ⟨by have := Fact.out (p := 2^25 < p); omega⟩

/-- Registered physical table at a position in the original Byte provider window. -/
def component (id : Id) : Component (ZMod p) := providerTableFor (slot id)

/-- Populate the registered component's own input columns. -/
def input : (id : Id) → (slot id).Occurrence → (component (p := p) id).Input (ZMod p)
  | .inl .u8Range => ByteChip.U8Range.ofEntry
  | .inl .msb => ByteChip.MSB.ofEntry
  | .inl .andByte => ByteChip.AndByte.ofEntry
  | .inl .orByte => ByteChip.OrByte.ofEntry
  | .inl .xorByte => ByteChip.XorByte.ofEntry
  | .inl .ltu => ByteChip.Ltu.ofEntry
  | .inr _ => RangeChip.ofEntry

omit [Fact p.Prime] [Fact (2^25 < p)] in
/-- Natural reader count installed in the native multiplicity column. -/
def amount : (id : Id) → (slot id).Occurrence → ℕ
  | .inl _ => TraceGen.ByteEntry.multiplicity
  | .inr _ => TraceGen.RangeEntry.multiplicity

private theorem fixed (id : Id) : ∀ rs, (component (p := p) id).FixedRowsMatch rs := by
  rcases id with op | w
  · cases op <;> intros <;> trivial
  · intros; trivial

private theorem assumptions (id : Id) {e : (slot id).Occurrence} (valid : (slot id).Valid e)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (component (p := p) id).circuit.ProverAssumptions (input id e) data hint := by
  cases id with
  | inl op =>
    cases op
    · exact ByteChip.U8Range.proverAssumptions_of_entry valid data hint
    · exact ByteChip.MSB.proverAssumptions_of_entry valid data hint
    · exact ByteChip.AndByte.proverAssumptions_of_entry valid data hint
    · exact ByteChip.OrByte.proverAssumptions_of_entry valid data hint
    · exact ByteChip.XorByte.proverAssumptions_of_entry valid data hint
    · exact ByteChip.Ltu.proverAssumptions_of_entry valid data hint
  | inr w => exact RangeChip.proverAssumptions_of_entry w valid data hint

variable (requests : List LookupKey) (count : LookupKey → ℕ) (valid : ∀ k ∈ requests, ByteServable k) (data : ProverData (ZMod p))

include valid in
private theorem input_height (id : Id) : ((entries requests count id).map (input (p := p) id)).length ≤ UInt64.size := by
  rw [List.length_map]
  exact (height_bound requests count id valid).trans (by decide)

/-- Each demand bucket builds through the original physical component, with one counted row
per selected key and the actual zero-input padding of its demand generator. -/
def table (id : Id) : Table (ZMod p) :=
  Table.ofInputs (component id) ((entries requests count id).map (input id)) data
    (input_height requests count valid id) (fixed id)

/-- All 23 physical tables are assembled in the verifier's registered order. -/
def tables : List (Table (ZMod p)) := all.map (table requests count valid data)

theorem table_valid (id : Id) :
    (table requests count valid data id).Constraints ∧ (table requests count valid data id).Guarantees := by
  apply Table.ofInputs_valid
  intro i used
  obtain ⟨e,inside,rfl⟩ := List.mem_map.mp used
  exact assumptions id (entries_valid requests count id valid e inside) _ _

/-- The physical row count is the rounded number of distinct messages requested of this provider. -/
theorem table_height (id : Id) : (table requests count valid data id).length =
    WitnessGeneration.demandHeight (keys requests id).length :=
  (Table.ofInputs_length ..).trans ((List.length_map _).trans (height requests count id))

/-- The positional components are the exact original six Byte and seventeen Range slots. -/
theorem tables_components :
    (tables requests count valid data).map Table.component = (sp1ProviderTables (p := p)).take 23 := by
  rfl

/-- Literal evaluated signed ledger of this generated table, before dropping any padding. -/
theorem table_accesses (id : Id) : tableCleanAccesses (table requests count valid data id) =
    (entries requests count id).map fun e => actualProviderAccess (p := p) (access id e) (amount id e) := by
  have checks := entries_valid requests count id valid
  have bound := input_height (p := p) requests count valid id
  rw [List.length_map] at bound
  cases id with
  | inl op =>
    cases op
    · exact u8Range_traceTable_actualAccesses _ _ _ bound (Component.inputData_consistent ..) checks
    · exact msb_traceTable_actualAccesses _ _ _ bound (Component.inputData_consistent ..) checks
    · exact and_traceTable_actualAccesses _ _ _ bound (Component.inputData_consistent ..) checks
    · exact or_traceTable_actualAccesses _ _ _ bound (Component.inputData_consistent ..) checks
    · exact xor_traceTable_actualAccesses _ _ _ bound (Component.inputData_consistent ..) checks
    · exact ltu_traceTable_actualAccesses _ _ _ bound (Component.inputData_consistent ..) checks
  | inr w => exact range_traceTable_actualAccesses w _ _ _ bound (Component.inputData_consistent ..) checks

omit [Fact (2^25 < p)] in
/-- The paid row for a real request contains its exact four field values and the original
count cast into the native multiplicity column. -/
theorem entry_access (id : Id) {k : LookupKey} (selected : selects id k) (served : ByteServable k) (m : ℕ) :
    actualProviderAccess (p := p) (access id (entry id k m)) (amount id (entry id k m)) =
      accessAt k (signedVal (m : ZMod p)) := by
  rw [round id k m selected served]
  cases id <;> rfl

/-- Each paid row is attributable to an active request. All real padding occurrences remain
in the physical ledger with their own concrete payload and zero signed multiplicity. -/
theorem table_reader_counts (id : Id) : tableCleanAccesses (table requests count valid data id) =
    ((keys requests id).map fun k => accessAt k (signedVal (count k : ZMod p))) ++
      List.replicate (WitnessGeneration.demandPadding (keys requests id).length) (access id (padding id)) := by
  rw [table_accesses]
  simp only [entries,List.map_append,List.map_map,List.map_replicate]
  congr 1
  · apply List.map_congr_left
    intro k used
    obtain ⟨inside,selected⟩ := List.mem_filter.mp used
    exact entry_access id selected (valid k (List.mem_dedup.mp inside)) _
  · apply congrArg (List.replicate _)
    cases id with
    | inl op => cases op <;> simp [actualProviderAccess,withFieldMultiplicity,amount,padding,access,
        u8RangeAccess,msbAccess,andAccess,orAccess,xorAccess,ltuAccess,signedVal]
    | inr w => simp [actualProviderAccess,withFieldMultiplicity,amount,padding,access,rangeAccess,signedVal]

end SP1Clean.Soundness.ByteProviderDemand
