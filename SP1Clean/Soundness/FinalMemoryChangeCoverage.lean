import SP1Clean.FormalModel.Contracts.FinalMemoryChange
import ToClean.Air.UnitBalance

/-! # Complete Memory comparison from final-record and change ledgers

These are accounting lemmas for the installed boundary proof. Every validation row is tied
to the finalizer's full record by receipt permutation, and its Boolean key names that record's
semantic location. Count-bounded change-channel balance then covers the verifier's canonical
change inventory. Consequently untouched target changes cannot disappear from the final list.
The assembly must derive these inventories and local facts from its physical tables.
-/

namespace SP1Clean.Soundness.FinalMemoryChangeCoverage

open Model.Core Channels Semantics FinalMemoryChange

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- A decoded validation row together with its statically registered location kind. -/
abbrev Row (p : ℕ) := Bool × Inputs (ZMod p)

/-- The activity coefficient accompanies every physical validation row, including padding. -/
abbrev PhysicalRow (p : ℕ) := Row p × ZMod p

/-- Semantic validation rows are precisely the active physical rows. -/
def activeRows (rows : List (PhysicalRow p)) : List (Row p) :=
  (rows.filter fun row => decide (row.2 = 1)).map Prod.fst

/-- The full physical change ledger retains zero activity and zero selection separately. -/
def ledger (source target : MemorySnapshot) (rows : List (PhysicalRow p)) : List (Interaction (ZMod p)) :=
  rows.map (fun row => channel.pushedIfValue (row.2 * row.1.2.selected) (key row.1.1 row.1.2.record)) ++
    (source.changes target).map (fun loc => channel.pulledValue (encode loc))

omit [Fact (2 ^ 17 < p)] in
/-- A constrained active row belongs to the semantic projection of its original physical list. -/
theorem mem_activeRows (rows : List (PhysicalRow p)) (row : PhysicalRow p)
    (member : row ∈ rows) (active : row.2 = 1) : row.1 ∈ activeRows rows :=
  List.mem_map.mpr ⟨row, List.mem_filter.mpr ⟨member, by simpa using active⟩, rfl⟩

/-- The physical change ledger covers every computed change with an active validation row. -/
theorem changes_covered (source target : MemorySnapshot) (rows : List (PhysicalRow p))
    (activity : ∀ row ∈ rows, row.2 = 0 ∨ row.2 = 1)
    (binary : ∀ row ∈ activeRows rows, Spec row.2)
    (names : ∀ row ∈ activeRows rows, key row.1 row.2.record = encode (MemoryMsg.locOf row.2.record))
    (balanced : BalancedInteractions (ledger source target rows)) :
    source.changes target ⊆ (activeRows rows).map (fun row => MemoryMsg.locOf row.2.record) := by
  have effective : ∀ row ∈ rows, row.2 * row.1.2.selected = 0 ∨ row.2 * row.1.2.selected = 1 := by
    intro row member
    rcases activity row member with disabled | active
    · simp [disabled]
    · simpa only [active, one_mul, FinalMemoryChange.Spec] using binary row.1 (mem_activeRows rows row member active)
  have same := channel.gated_unit_perm_of_balanced rows (fun row => row.2 * row.1.2.selected)
    (fun row => key row.1.1 row.1.2.record) ((source.changes target).map encode) effective
    (by simpa only [ledger, List.map_map, Function.comp_def] using balanced)
  intro loc changed
  have member := same.mem_iff.mpr (List.mem_map_of_mem (f := encode (p := p)) changed)
  obtain ⟨row, selected, equal⟩ := List.mem_map.mp member
  have present := (List.mem_filter.mp selected).1
  have contribution : row.2 * row.1.2.selected = 1 := by
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp selected).2
  have active : row.2 = 1 := by
    rcases activity row present with disabled | active
    · simp only [disabled, zero_mul] at contribution
      exact False.elim (zero_ne_one contribution)
    · exact active
  have semantic := mem_activeRows rows row present active
  have location : MemoryMsg.locOf row.1.2.record = loc :=
    encode_injective ((names row.1 semantic).symm.trans equal)
  exact List.mem_map.mpr ⟨row.1, semantic, location⟩

/-- Target validation, complete final receipts, and the physical change ledger imply the
existing complete snapshot comparison. No Boolean comparison is assumed by this theorem. -/
theorem checkFinal_of_balanced (source target : MemorySnapshot)
    (records : List (MemoryMsg (ZMod p))) (rows : List (PhysicalRow p))
    (receipts : ((activeRows rows).map fun row => row.2.record).Perm records)
    (activity : ∀ row ∈ rows, row.2 = 0 ∨ row.2 = 1)
    (values : ∀ row ∈ activeRows rows,
      target.read (MemoryMsg.locOf row.2.record) = Word.toBitVec64 row.2.record.value)
    (binary : ∀ row ∈ activeRows rows, Spec row.2)
    (names : ∀ row ∈ activeRows rows, key row.1 row.2.record = encode (MemoryMsg.locOf row.2.record))
    (balanced : BalancedInteractions (ledger source target rows)) :
    source.checkFinal target
      (records.map fun record => (MemoryMsg.locOf record, Word.toBitVec64 record.value)) = true := by
  apply (MemorySnapshot.checkFinal_iff_changes _ _ _).mpr
  constructor
  · intro observed member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨row, rowPresent, rfl⟩ := List.mem_map.mp (receipts.mem_iff.mpr present)
    exact values row rowPresent
  · intro loc changed
    have covered := changes_covered source target rows activity binary names balanced changed
    obtain ⟨row, present, equal⟩ := List.mem_map.mp covered
    simp only [List.map_map, Function.comp_def]
    exact List.mem_map.mpr ⟨row.2.record,
      receipts.mem_iff.mp (List.mem_map_of_mem (f := fun row : Row p => row.2.record) present), equal⟩

end SP1Clean.Soundness.FinalMemoryChangeCoverage
