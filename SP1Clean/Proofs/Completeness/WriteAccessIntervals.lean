import SP1Clean.Proofs.Completeness.MemoryReadbackIntervals

/-! # Coverage of incoming CPU cuts by genuine predecessor records

A mutating Memory push lands strictly after its row's incoming clock. An access at exactly
that clock is value-preserving. Real CPU starts are at least eight ticks apart, so clipping a
predecessor interval to the incoming clock drops no eligible CPU cut before its push.
-/

namespace SP1Clean.TraceGen.MemoryLocationHistory

open Semantics Soundness.TimedGrounding

variable {p : ℕ} [Fact p.Prime]

/-- The closed interval emitted by a Memory pull carries the pulled word even at the
accessing row's exact incoming clock. Later aliased predecessors may have an empty interval. -/
theorem heldAt_incoming (history : MemoryLocationHistory) (chain : history.IsRecordChain)
    (strict : ∀ a ∈ history.accesses, a.previous < a.current)
    {rowTime time : ℕ} {touch : Touch p} (shape : TouchOK rowTime touch.1 touch.2)
    (member : MemoryHistoryAccess.ofTouch touch ∈ history.accesses)
    (first : MemoryMsg.timeNat touch.1.1 ≤ time) (last : time ≤ rowTime) :
    MemoryHistoryAccess.heldAt history.first.pulled time history.accesses = touch.1.1.value.toBitVec64 := by
  have future := shape.push_lo
  by_cases inside : time < MemoryMsg.timeNat touch.2
  · exact history.heldAt_interval chain strict member ⟨first, inside⟩
  have equal : time = MemoryMsg.timeNat touch.2 := by omega
  rcases shape.push_kind with ⟨same, _⟩ | effect
  · apply history.heldAt_readback chain strict member (congrArg Word.toBitVec64 same) ⟨first, equal.le⟩
  · have positive : 0 < writeOffset (MemoryMsg.locOf touch.2) := by
      cases MemoryMsg.locOf touch.2 <;> simp only [writeOffset_reg, writeOffset_ram] <;> decide
    omega

/-- Any genuine incoming cut in the original half-open predecessor interval is contained in
its clipped receipt. The same physical word therefore funds every such CPU cut. -/
theorem incoming_covers_cut (history : MemoryLocationHistory) (chain : history.IsRecordChain)
    (strict : ∀ a ∈ history.accesses, a.previous < a.current)
    (timeline : Timeline) (row cut : ℕ) {touch : Touch p} (shape : TouchOK (timeline.start row) touch.1 touch.2)
    (member : MemoryHistoryAccess.ofTouch touch ∈ history.accesses)
    (within : MemoryMsg.timeNat touch.1.1 ≤ timeline.start cut ∧ timeline.start cut < MemoryMsg.timeNat touch.2) :
    timeline.start cut ≤ timeline.start row ∧
      MemoryHistoryAccess.heldAt history.first.pulled (timeline.start cut) history.accesses = touch.1.1.value.toBitVec64 := by
  have before : cut ≤ row := by
    by_contra! later
    have next := timeline.start_le_of_le (show row + 1 ≤ cut by omega)
    have gap := timeline.gap row
    have latest := shape.push_hi
    omega
  have order := timeline.start_le_of_le before
  exact ⟨order, history.heldAt_incoming chain strict shape member within.1 order⟩

/-- Pick the first genuine access strictly after the requested clock. A missing selection uses
the finalized suffix, including when the clock equals the last push. -/
def nextAccess? (history : MemoryLocationHistory) (time : ℕ) : Option MemoryHistoryAccess :=
  history.accesses.find? fun a => time < a.current

private theorem selected_previous {time : ℕ} (first : MemoryHistoryAccess) (rest : List MemoryHistoryAccess)
    {selected : MemoryHistoryAccess} (links : List.IsChain MemoryHistoryAccess.Continues (first :: rest))
    (entered : first.previous ≤ time)
    (found : (first :: rest).find? (fun a => time < a.current) = some selected) : selected.previous ≤ time := by
  induction rest generalizing first with
  | nil =>
    by_cases later : time < first.current
    · have same : first = selected := by simpa [List.find?, later] using found
      exact same ▸ entered
    · simp [List.find?, later] at found
  | cons second rest ih =>
    by_cases later : time < first.current
    · have eq : first = selected := by simpa [List.find?, later] using found
      exact eq ▸ entered
    · have next := (List.isChain_cons.mp links).1 second (by simp)
      apply ih second (List.isChain_cons.mp links).2
      · rw [next.2.1]
        omega
      · simpa [List.find?_cons, later] using found

/-- The deterministic query selector is total on each genuine location history. Its selected
predecessor or terminal suffix always carries the exact held word. -/
theorem nextAccess?_covers (history : MemoryLocationHistory) (chain : history.IsRecordChain)
    (strict : ∀ a ∈ history.accesses, a.previous < a.current) (time : ℕ) :
    match history.nextAccess? time with
    | some a => a ∈ history.accesses ∧ a.previous ≤ time ∧ time < a.current ∧
        MemoryHistoryAccess.heldAt history.first.pulled time history.accesses = a.pulled
    | none => history.last.current ≤ time ∧
        MemoryHistoryAccess.heldAt history.first.pulled time history.accesses = history.last.pushed := by
  cases found : history.nextAccess? time with
  | none =>
    have bound : history.last.current ≤ time := by
      have absent := List.find?_eq_none.mp found history.last (List.getLast_mem history.nonempty)
      simpa using absent
    exact ⟨bound, history.heldAt_final chain strict bound⟩
  | some a =>
    have member := List.mem_of_find?_eq_some found
    have eligible := List.find?_some (p := fun x : MemoryHistoryAccess => decide (time < x.current)) found
    have after : time < a.current := of_decide_eq_true eligible
    have before : a.previous ≤ time := by
      have links := chain.adjacent
      have start := chain.genesis
      unfold nextAccess? at found
      cases eq : history.accesses with
      | nil => exact False.elim (history.nonempty eq)
      | cons first rest =>
        rw [eq] at links found
        have zero : first.previous = 0 := by simpa [MemoryLocationHistory.first, eq] using start
        exact selected_previous first rest links (zero ▸ Nat.zero_le _) found
    exact ⟨member, before, after, history.heldAt_interval chain strict member ⟨before, after⟩⟩

end SP1Clean.TraceGen.MemoryLocationHistory
