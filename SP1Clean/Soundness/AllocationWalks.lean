import SP1Clean.Soundness.RankedGrounding

/-! # Exhaustive walks for a ranked transition ledger with several callers

Each actual opening occurrence receives its own path, possibly empty. Ending states and
transition rows are used with their exact physical multiplicities.
-/

namespace SP1Clean.Soundness.Walk

variable {Row Vertex : Type*}

/-- A ranked, balanced family of transition edges partitions into one complete walk per
opening. The opening order is retained, while terminals and transitions are matched as multisets. -/
theorem partition_ranked (edge : Row → Vertex × Vertex) (rank : Vertex → ℕ)
    (starts : List Vertex) (ends : Multiset Vertex) (edges : Multiset Row)
    (balanced : (starts : Multiset Vertex) + edges.map (fun r => (edge r).2) =
      ends + edges.map (fun r => (edge r).1))
    (grows : ∀ r ∈ edges, rank (edge r).1 < rank (edge r).2) :
    ∃ paths : List (List Row × Vertex),
      List.Forall₂ (fun s path => IsWalk edge s path.2 path.1) starts paths ∧
      (↑(paths.map Prod.snd) : Multiset Vertex) = ends ∧
      (↑(paths.flatMap Prod.fst) : Multiset Row) = edges := by
  classical
  cases startsEq : starts with
  | nil =>
    rw [startsEq] at balanced
    have size := congrArg Multiset.card balanced
    simp only [Multiset.coe_nil, zero_add, Multiset.card_map, Multiset.card_add] at size
    have empty := Multiset.card_eq_zero.mp (by omega : ends.card = 0)
    subst ends
    have zero : edges = 0 := by
      by_contra nonempty
      obtain ⟨r, mem⟩ := Multiset.exists_mem_of_ne_zero nonempty
      apply nonempty
      apply RankedGrounding.eq_zero_of_endpointBalanced_self edges edge rank (initial := (edge r).1) grows
      exact congrArg (Multiset.cons _) (by simpa using balanced)
    exact ⟨[], .nil, rfl, zero.symm⟩
  | cons start rest =>
    rw [startsEq] at balanced
    by_cases finish : start ∈ ends
    · have h := balanced
      conv_rhs at h => rw [← Multiset.cons_erase finish]
      simp only [← Multiset.cons_coe, Multiset.cons_add, Multiset.cons_inj_right] at h
      obtain ⟨paths, runs, done, used⟩ := partition_ranked edge rank rest (ends.erase start) edges h grows
      refine ⟨([],start) :: paths, .cons rfl runs, ?_, used⟩
      rw [List.map_cons, ← Multiset.cons_coe, done, Multiset.cons_erase finish]
    · have occurs : start ∈ ends + edges.map (fun r => (edge r).1) := by
        rw [← balanced]
        exact Multiset.mem_add.mpr (.inl (List.mem_cons_self ..))
      obtain ⟨r, mem, source⟩ := Multiset.mem_map.mp ((Multiset.mem_add.mp occurs).resolve_left finish)
      have h := balanced
      rw [← Multiset.cons_erase mem] at h
      simp only [Multiset.map_cons, ← Multiset.cons_coe, Multiset.cons_add, Multiset.add_cons, source] at h
      have shifted :
          (↑((edge r).2 :: rest) : Multiset Vertex) + (edges.erase r).map (fun x => (edge x).2) =
            ends + (edges.erase r).map (fun x => (edge x).1) := by
        rw [Multiset.cons_swap (edge r).2 start] at h
        simpa only [← Multiset.cons_coe, Multiset.cons_add] using (Multiset.cons_inj_right start).mp h
      obtain ⟨paths, runs, done, used⟩ := partition_ranked edge rank ((edge r).2 :: rest) ends (edges.erase r)
        shifted (fun x hx => grows _ (Multiset.mem_of_mem_erase hx))
      cases runs with
      | @cons _ path _ tail first others =>
        refine ⟨(r :: path.1, path.2) :: tail, .cons ⟨source, first⟩ others, done, ?_⟩
        change r ::ₘ (↑(path.1 ++ tail.flatMap Prod.fst) : Multiset Row) = edges
        rw [show (↑(path.1 ++ tail.flatMap Prod.fst) : Multiset Row) = edges.erase r from used,
          Multiset.cons_erase mem]
termination_by starts.length + edges.card
decreasing_by
  · simp [startsEq]
  · classical
    have := Multiset.card_pos_iff_exists_mem.mpr ⟨r, mem⟩
    simp [startsEq, Multiset.card_erase_of_mem mem]; omega

end SP1Clean.Soundness.Walk
