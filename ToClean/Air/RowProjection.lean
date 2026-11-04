module

public import Clean.Air.FlatComponent

/-! # Fixed-cell contracts under row projection

Clean records fixed cells through typed generation modes. These lemmas transport that contract
when retaining a row prefix that includes every input cell. They preserve the full number and
order of rows, including inactive and repeated rows. The missing upstream capability is this
layout transport beside `Component.FixedRowsMatch`.
-/

@[expose] public section

namespace Air.Flat

variable {F : Type} [FiniteField F]

/-- Cutting a row after its input does not change its decoded input, including zero padding. -/
theorem rowPrefix_extract (row : Array F) {input width : ℕ} (bound : input ≤ width) :
    rowPrefix input (row.extract 0 width) = rowPrefix input row := by
  ext i hi
  simp only [rowPrefix, Vector.getElem_mk, List.getElem_toArray, List.getElem_ofFn]
  rw [Array.getElem?_extract]
  by_cases present : i < row.size
  · simp [present, Nat.lt_of_lt_of_le hi bound]
  · simp only [Nat.sub_zero, Nat.min_def, Nat.zero_add]
    split <;> simp_all

/-- Fixed cells all lie in the input, so cutting off later witness cells preserves them. -/
theorem Component.fixedRowsMatch_extract (component : Component F) (rows : List (Array F))
    {width : ℕ} (bound : size component.Input ≤ width)
    (fixed : component.FixedRowsMatch rows) :
    component.FixedRowsMatch (rows.map (·.extract 0 width)) := by
  cases generation : component.generation with
  | demand mode => simp [Component.FixedRowsMatch, generation]
  | preallocated mode =>
    simp only [Component.FixedRowsMatch, generation] at fixed ⊢
    refine ⟨by simpa only [List.length_map] using fixed.1, ?_⟩
    intro i hi
    simpa only [List.getElem_map, rowPrefix_extract _ bound] using
      fixed.2 i (by simpa only [List.length_map] using hi)

end Air.Flat
