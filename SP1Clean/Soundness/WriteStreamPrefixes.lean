import SP1Clean.Proofs.Operations.WriteClassifiedRoute
import SP1Clean.Soundness.Walk

/-! # Semantic byte and reply prefixes on a physical WRITE tape -/

namespace SP1Clean.WriteEffects
open Semantics Soundness
private abbrev F := ZMod SP1Prime

/-- Replay the external byte counts and consumed reply ordinals of an actual dispatch
tape, using only its released descriptors and original x12 lengths. -/
def dispatchCounts (rows : List (Dispatch F)) (start : StreamCounts := ⟨0,0,0,0⟩) : StreamCounts :=
  rows.foldl (fun s d => s.record d.route d.request.header.length.toNat) start

private theorem fold_walk {R V S : Type} (edge : R → V × V) (read : V → S) (step : S → R → S)
    {a b : V} {rs : List R} (walk : Walk.IsWalk edge a b rs)
    (valid : ∀ r ∈ rs, read (edge r).2 = step (read (edge r).1) r) :
    read b = rs.foldl step (read a) ∧ ∀ i : Fin rs.length, read (edge rs[i.val]).1 = (rs.take i.val).foldl step (read a) := by
  induction rs generalizing a with
  | nil => change a = b at walk; exact ⟨congrArg read walk.symm,fun i => Fin.elim0 i⟩
  | cons r rs ih =>
    obtain ⟨before,later⟩ := walk
    subst a
    obtain ⟨terminal,positions⟩ := ih later (fun x m => valid x (List.mem_cons_of_mem _ m))
    rw [valid r List.mem_cons_self] at terminal positions
    refine ⟨terminal,?_⟩
    rintro ⟨i,h⟩
    cases i with
    | zero => rfl
    | succ i => exact positions ⟨i,Nat.lt_of_succ_lt_succ h⟩

/-- Both the terminal cursor and every incoming cursor equal their chronological
semantic prefixes. This preserves all repeated occurrences and all empty writes. -/
theorem dispatch_walk_counts {start stop : StreamCursor F} {path : List (Dispatch F)}
    (walk : Walk.IsWalk (fun d : Dispatch F => (d.previous,d.next d.flags)) start stop path)
    (valid : ∀ d ∈ path, d.Valid ∧ d.request.Valid) :
    StreamCounts.ofCursor stop = dispatchCounts path (StreamCounts.ofCursor start) ∧
      ∀ i : Fin path.length, StreamCounts.ofCursor path[i.val].previous = dispatchCounts (path.take i.val) (StreamCounts.ofCursor start) := by
  apply fold_walk (fun d : Dispatch F => (d.previous,d.next d.flags)) StreamCounts.ofCursor
    (fun s d => s.record d.route d.request.header.length.toNat) walk
  intro d md
  obtain ⟨v,c⟩ := valid d md
  rw [v.guest_length]
  exact v.stream_counts c

end SP1Clean.WriteEffects
