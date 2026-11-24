import SP1Clean.Soundness.RankedGrounding

/-! # Consecutive row indices from a balanced ranked trail -/

namespace SP1Clean.Soundness.RankedGrounding

open scoped Classical

private theorem indices_of_walk {R V : Type*} (edge : R → V × V) (index : V → ℕ)
    (initial final : V) (path : List R) (walk : Walk.IsWalk edge initial final path)
    (step : ∀ row ∈ path, index (edge row).2 = index (edge row).1 + 1) :
    index final = index initial + path.length ∧
      path.map (fun row => index (edge row).1) = List.range' (index initial) path.length := by
  induction path generalizing initial with
  | nil =>
    change initial = final at walk
    subst final
    simp
  | cons row rest ih =>
    obtain ⟨source, tail⟩ := walk
    have successor := step row (List.mem_cons_self ..)
    rw [source] at successor
    have result := ih _ tail (fun other member => step other (List.mem_cons_of_mem _ member))
    refine ⟨by simp only [List.length_cons]; omega, ?_⟩
    rw [List.map_cons, source, result.2, successor, List.length_cons, List.range'_succ]

private theorem context_of_walk {R V C : Type*} (edge : R → V × V) (context : V → C)
    (initial final : V) (path : List R) (walk : Walk.IsWalk edge initial final path)
    (preserve : ∀ row ∈ path, context (edge row).2 = context (edge row).1) :
    context final = context initial ∧ ∀ row ∈ path, context (edge row).1 = context initial := by
  induction path generalizing initial with
  | nil =>
    change initial = final at walk
    subst final
    simp
  | cons row rest ih =>
    obtain ⟨source, tail⟩ := walk
    have same := preserve row (List.mem_cons_self ..)
    rw [source] at same
    have result := ih _ tail (fun other member => preserve other (List.mem_cons_of_mem _ member))
    refine ⟨result.1.trans same, ?_⟩
    intro other member
    rcases List.mem_cons.mp member with rfl | member
    · rw [source]
    · exact (result.2 other member).trans same

/-- Unit-successor edges preserving a packet context cover every position between the two endpoints exactly once. -/
theorem consecutive_coverage {R V C : Type*} (edge : R → V × V) (index : V → ℕ) (context : V → C)
    (rows : List R) (initial final : V) (balance : EndpointBalanced (↑rows) edge initial final)
    (successors : ∀ row ∈ rows, index (edge row).2 = index (edge row).1 + 1)
    (preserve : ∀ row ∈ rows, context (edge row).2 = context (edge row).1) :
    ∃ path : List R, path.Perm rows ∧ Walk.IsWalk edge initial final path ∧
      index final = index initial + path.length ∧
      path.map (fun row => index (edge row).1) = List.range' (index initial) path.length ∧
      context final = context initial ∧ ∀ row ∈ path, context (edge row).1 = context initial := by
  obtain ⟨path, walk, exhaustive⟩ := exists_exhaustiveTrail_of_endpointBalanced
    (↑rows) edge index initial final balance (by
      intro row member
      rw [successors row (Multiset.mem_coe.mp member)]
      omega)
  have perm : path.Perm rows := Multiset.coe_eq_coe.mp exhaustive
  have indices := indices_of_walk edge index initial final path walk
    (fun row member => successors row (perm.mem_iff.mp member))
  have same := context_of_walk edge context initial final path walk
    (fun row member => preserve row (perm.mem_iff.mp member))
  exact ⟨path, perm, walk, indices.1, indices.2, same.1, same.2⟩

/-- A finite closed list of strictly successive cursor edges has no active row. -/
theorem nil_of_closed {R V : Type*} (edge : R → V × V) (index : V → ℕ) (rows : List R)
    (closed : (rows.map (fun row => (edge row).2)).Perm (rows.map (fun row => (edge row).1)))
    (successors : ∀ row ∈ rows, index (edge row).2 = index (edge row).1 + 1) : rows = [] := by
  classical
  cases rows with
  | nil => rfl
  | cons row rest =>
    have balanced : EndpointBalanced (↑(row :: rest)) edge (edge row).1 (edge row).1 := by
      simpa only [EndpointBalanced, Multiset.map_coe, Multiset.cons_coe, Multiset.coe_eq_coe] using
        closed.cons (edge row).1
    have empty := eq_zero_of_endpointBalanced_self (↑(row :: rest)) edge index
      (fun current member => by rw [successors current (Multiset.mem_coe.mp member)]; omega) balanced
    simp at empty

end SP1Clean.Soundness.RankedGrounding
