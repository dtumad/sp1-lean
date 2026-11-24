import SP1Clean.Soundness.AllocationWordWalk
import SP1Clean.Soundness.AllocationWalks

/-! # Grounding complete immutable word walks in physical seed occurrences -/

namespace SP1Clean.WriteAllocation.Words
open Semantics Soundness
private abbrev F := ZMod SP1Prime
attribute [local instance 2000] FiniteField.instDecidableEq

private def nexts (r : Row F) : List (Cursor F) := if r.payload.more = 1 then [r.next] else []

private def stops (r : Row F) : List (Option (Cursor F)) := if r.payload.more = 1 then [] else [none]

private theorem ends_split (rs : List (Row F)) :
    ((rs.map (fun r => (wordEdge r).2)) : Multiset (Option (Cursor F))) =
      ↑((rs.flatMap nexts).map some) + ↑(rs.flatMap stops) := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    by_cases h : r.payload.more = 1
    · have edge : (wordEdge r).2 = some r.next := ite_eq_left h
      simp only [List.map_cons,List.flatMap_cons,edge,nexts,stops,h,ite_true,List.cons_append,
        List.nil_append,List.map_cons,← Multiset.cons_coe,Multiset.cons_add,ih]
    · have edge : (wordEdge r).2 = none := ite_eq_right h
      simp only [List.map_cons,List.flatMap_cons,edge,nexts,stops,h,ite_false,List.cons_append,
        List.nil_append,← Multiset.cons_coe,Multiset.add_cons,ih]

private def rank : Option (Cursor F) → Nat
  | some c => Address.toNat c.index
  | none => 2^48

private theorem increases (r : Row F) (v : r.Valid) : rank (wordEdge r).1 < rank (wordEdge r).2 := by
  change Address.toNat r.prior.index < rank (if r.payload.more = 1 then some r.next else none)
  split
  · change Address.toNat r.prior.index < Address.toNat r.nextIndex
    have inc := v.2.2.2.1.2.2.2
    change Address.toNat r.nextIndex = Address.toNat r.prior.index + Address.toNat (#v[1,0,0] : fields 3 F) at inc
    rw [inc,show Address.toNat (#v[1,0,0] : fields 3 F) = 1 by decide]
    exact Nat.lt_succ_self _
  · exact Address.toNat_lt v.2.2.2.1.1

/-- Consuming the exact private cursor multiset partitions all physical words among their
seeds. Strictly increasing word indices exclude disconnected components, including rows
with zero external readers. -/
theorem partition (seeds : List (Contents F)) (rows : List (Row F))
    (matchEnds : (seeds.map start ++ rows.flatMap (fun r => if r.payload.more = 1 then [r.next] else [])).Perm
      (rows.map Row.prior)) (checked : ∀ r ∈ rows, r.Valid) :
    ∃ paths : List (List (Row F)),
      List.Forall₂ (fun seed rs => Walk.IsWalk wordEdge (some (start seed)) none rs) seeds paths ∧
        paths.flatten.Perm rows := by
  let opens := seeds.map (fun s => some (start s))
  let terminals := rows.flatMap stops
  have paired := Multiset.coe_eq_coe.mpr (matchEnds.map some)
  change ((seeds.map start ++ rows.flatMap nexts).map some : Multiset (Option (Cursor F))) = ((rows.map Row.prior).map some : Multiset (Option (Cursor F))) at paired
  simp only [List.map_append,List.map_map,← Multiset.coe_add,Function.comp_def] at paired
  have ledger : (opens : Multiset _) + (rows : Multiset _).map (fun r => (wordEdge r).2) =
      (terminals : Multiset _) + (rows : Multiset _).map (fun r => (wordEdge r).1) := by
    rw [Multiset.map_coe,ends_split,Multiset.map_coe]
    change _ = ↑(rows.flatMap stops) + (rows.map (fun r : Row F => some r.prior) : Multiset (Option (Cursor F)))
    rw [← paired]
    dsimp only [opens]
    ac_rfl
  obtain ⟨paths,walks,ends,allRows⟩ := Walk.partition_ranked wordEdge
    rank opens terminals rows ledger
    (fun r m => increases r (checked r m))
  refine ⟨paths.map Prod.fst,?_,?_⟩
  · change List.Forall₂ _ (seeds.map _) paths at walks
    rw [List.forall₂_map_left_iff] at walks
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_iff_zip.mpr
    refine ⟨walks.length_eq,?_⟩
    intro seed path both
    have pathMem : path ∈ paths := (List.of_mem_zip both).2
    have mem := (Multiset.coe_eq_coe.mp ends).mem_iff.mp (List.mem_map_of_mem (f := Prod.snd) pathMem)
    obtain ⟨r,_,terminal⟩ := List.mem_flatMap.mp mem
    have stop : path.2 = none := by
      by_cases more : r.payload.more = 1
      · simp [stops,more] at terminal
      · simpa [stops,more] using terminal
    simpa only [← stop] using (List.forall₂_iff_zip.mp walks).2 both
  · simpa only [← List.flatMap_def] using Multiset.coe_eq_coe.mp allRows

end SP1Clean.WriteAllocation.Words
