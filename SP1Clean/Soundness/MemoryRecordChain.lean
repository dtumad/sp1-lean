import SP1Clean.Soundness.CoreTableProjection
import SP1Clean.Soundness.CoreRowBalance
import SP1Clean.Soundness.RankedGrounding

/-! # Chronological Memory record chains

A location has at most one incoming and one outgoing frontier record. Conservation of full
records together with strict advancement of each physical access clocks determines a single
chronological chain, including refreshes, readbacks and repeated equal word values.
-/

namespace SP1Clean.Soundness.MemoryRecordChain

open Channels Semantics TimedGrounding RankedGrounding

variable {p : ℕ}

/-- A physical access joins the complete predecessor and successor Memory records. -/
abbrev Pair (p : ℕ) := MemoryMsg (ZMod p) × MemoryMsg (ZMod p)

/-- Select all occurrence-level edges of a single location by their destination record. -/
def atLocation (loc : MemLoc) (edges : List (Pair p)) := edges.filter (fun e => MemoryMsg.locOf e.2 = loc)

/-- The physical CPU and host touches and both types of refresh have the same full record
pair representation. -/
def pairs (original : List (RowFacts p)) (extra : List (Touch p)) (refreshes : List (Pair p)) :=
  ((original.flatMap NativeCore.rowTouches ++ extra).map (fun t => (t.1.1, t.2))) ++ refreshes

private theorem selected_projection (edges : List (Pair p)) (loc : MemLoc)
    (same : ∀ e ∈ edges, MemoryMsg.locOf e.1 = MemoryMsg.locOf e.2) :
    (↑((atLocation loc edges).map Prod.snd) : Multiset (MemoryMsg (ZMod p))) =
        Multiset.filter (fun m => MemoryMsg.locOf m = loc) (↑(edges.map Prod.snd) : Multiset (MemoryMsg (ZMod p))) ∧
    (↑((atLocation loc edges).map Prod.fst) : Multiset (MemoryMsg (ZMod p))) =
        Multiset.filter (fun m => MemoryMsg.locOf m = loc) (↑(edges.map Prod.fst) : Multiset (MemoryMsg (ZMod p))) := by
  induction edges with
  | nil => simp [atLocation]
  | cons e rest ih =>
    have tail := ih (fun pair member => same pair (List.mem_cons_of_mem _ member))
    have here := same e (List.mem_cons_self ..)
    by_cases selected : MemoryMsg.locOf e.2 = loc
    · simpa [atLocation, here, selected] using tail
    · simpa [atLocation, here, selected] using tail

private theorem originals (rows : List (RowFacts p))
    (aligned : ∀ row ∈ rows, List.Forall₂ (TouchOK (StateMsg.timeNat row.statePull)) row.memPulls row.memPushes) :
    ((rows.flatMap NativeCore.rowTouches).map Prod.snd = rows.flatMap (·.memPushes)) ∧
      ((rows.flatMap NativeCore.rowTouches).map (fun t => t.1.1) = rows.flatMap (fun row => row.memPulls.map Prod.fst)) ∧
      ∀ t ∈ rows.flatMap NativeCore.rowTouches, MemoryMsg.locOf t.1.1 = MemoryMsg.locOf t.2 := by
  constructor
  · rw [List.map_flatMap]
    exact List.flatMap_congr (fun row member => List.map_snd_zip (aligned row member).length_eq.symm.le)
  constructor
  · rw [List.map_flatMap]
    apply List.flatMap_congr
    intro row member
    have pulled : (NativeCore.rowTouches row).map Prod.fst = row.memPulls :=
      List.map_fst_zip (aligned row member).length_eq.le
    simpa only [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) pulled
  · intro t member
    obtain ⟨row, rowMem, touchMem⟩ := List.mem_flatMap.mp member
    exact ((List.forall₂_iff_zip.mp (aligned row rowMem)).2 touchMem).loc_eq.symm

/-- Physical edges reproduce every aligned CPU record, additional host record, and refresh
on both sides of the per-location ledger. Grouping retains all repeated occurrences. -/
theorem projections (rows : List (RowFacts p)) (extra : List (Touch p)) (refresh : List (Pair p)) (loc : MemLoc)
    (aligned : ∀ row ∈ rows, List.Forall₂ (TouchOK (StateMsg.timeNat row.statePull)) row.memPulls row.memPushes)
    (host : ∀ t ∈ extra, MemoryMsg.locOf t.1.1 = MemoryMsg.locOf t.2)
    (preserve : ∀ e ∈ refresh, MemoryMsg.locOf e.1 = MemoryMsg.locOf e.2) :
    (↑((atLocation loc (pairs rows extra refresh)).map Prod.snd) : Multiset (MemoryMsg (ZMod p))) =
      pushesAt rows loc + Multiset.filter (fun m => MemoryMsg.locOf m = loc) (↑(extra.map Prod.snd) : Multiset (MemoryMsg (ZMod p))) +
        Multiset.filter (fun m => MemoryMsg.locOf m = loc) (↑(refresh.map Prod.snd) : Multiset (MemoryMsg (ZMod p))) ∧
    (↑((atLocation loc (pairs rows extra refresh)).map Prod.fst) : Multiset (MemoryMsg (ZMod p))) =
      pullsAt rows loc + Multiset.filter (fun m => MemoryMsg.locOf m = loc) (↑(extra.map (fun t => t.1.1)) : Multiset (MemoryMsg (ZMod p))) +
        Multiset.filter (fun m => MemoryMsg.locOf m = loc) (↑(refresh.map Prod.fst) : Multiset (MemoryMsg (ZMod p))) := by
  have original := originals rows aligned
  have selected := selected_projection (pairs rows extra refresh) loc (by
    intro e present
    rcases List.mem_append.mp present with operation | bump
    · obtain ⟨t, member, rfl⟩ := List.mem_map.mp operation
      exact (List.mem_append.mp member).elim (original.2.2 t) (host t)
    · exact preserve e bump)
  rw [selected.1, selected.2]
  simp only [pairs, List.map_append, List.map_map, Function.comp_def, filter_coe_append,
    NativeCore.pushesAt_flatMap, NativeCore.pullsAt_flatMap, original.1, original.2.1]
  trivial

/-- Either no record or access is present at the location, or all the physical edges form
one strictly ordered walk between its actual frontier records. -/
def History (rows : List (Pair p)) (initial final : Option (MemoryMsg (ZMod p))) : Prop :=
  (initial = none ∧ final = none ∧ rows = []) ∨
    ∃ first last path, initial = some first ∧ final = some last ∧ path.Perm rows ∧
      Walk.IsWalk id first last path ∧ (path.map (fun e => MemoryMsg.timeNat e.2)).Pairwise (· < ·) ∧
      ∀ e ∈ path, MemoryMsg.timeNat e.1 < MemoryMsg.timeNat e.2

/-- A nonempty history has both authenticated endpoint records, and strictly increasing
timestamps order every physical edge exactly once. -/
theorem exists_walk (rows : List (Pair p)) (initial final : Option (MemoryMsg (ZMod p)))
    (balance : optMS initial + (↑(rows.map Prod.snd) : Multiset (MemoryMsg (ZMod p))) = optMS final + (↑(rows.map Prod.fst) : Multiset (MemoryMsg (ZMod p))))
    (increase : ∀ e ∈ rows, MemoryMsg.timeNat e.1 < MemoryMsg.timeNat e.2) :
    History rows initial final := by
  classical
  have count := congrArg Multiset.card balance
  simp only [Multiset.card_add, Multiset.coe_card, List.length_map] at count
  cases initial with
  | none =>
    cases final with
    | none =>
      refine Or.inl ⟨rfl, rfl, ?_⟩
      cases rows with
      | nil => rfl
      | cons e rest =>
        have closed : EndpointBalanced (↑(e :: rest)) id e.1 e.1 := by
          change (↑((e :: rest).map Prod.snd) : Multiset (MemoryMsg (ZMod p))) = (↑((e :: rest).map Prod.fst) : Multiset (MemoryMsg (ZMod p))) at balance
          simpa only [EndpointBalanced, Multiset.map_coe, id_eq] using congrArg (Multiset.cons e.1) balance
        have empty := eq_zero_of_endpointBalanced_self (↑(e :: rest)) id MemoryMsg.timeNat
          (fun e h => increase e (Multiset.mem_coe.mp h)) closed
        simp at empty
    | some last => simp [optMS] at count
  | some first =>
    cases final with
    | none => simp [optMS] at count
    | some last =>
      have endpoints : EndpointBalanced (↑rows) id first last := by
        change (first ::ₘ 0) + _ = (last ::ₘ 0) + _ at balance
        simpa only [Multiset.cons_add, zero_add, EndpointBalanced, Multiset.map_coe, id_eq] using balance
      obtain ⟨path, walk, all⟩ := exists_exhaustiveTrail_of_endpointBalanced (↑rows) id MemoryMsg.timeNat first last
        endpoints (fun e active => increase e (Multiset.mem_coe.mp active))
      have perm := Multiset.coe_eq_coe.mp all
      exact Or.inr ⟨first, last, path, rfl, rfl, perm, walk, targetRanks_pairwise_of_isWalk id MemoryMsg.timeNat walk
        (fun e active => increase e (perm.mem_iff.mp active)), fun e active => increase e (perm.mem_iff.mp active)⟩

end SP1Clean.Soundness.MemoryRecordChain
