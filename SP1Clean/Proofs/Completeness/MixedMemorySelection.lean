import SP1Clean.Proofs.Completeness.MixedMemoryValues
import SP1Clean.Proofs.Completeness.WriteAccessIntervals

/-! # Selecting an original Memory receipt at a semantic CPU cut

At a touched location the next later transfer displaces the exact word held at the requested
cut. Its own event starts no earlier than the cut, so clipping the receipt to the actual row
clock preserves coverage. When the sequence is exhausted, the final Memory boundary owns it.
-/

namespace SP1Clean.TraceGen.MixedMemoryHistory

open Semantics Machine FormalModel.Shard Soundness.Target MemoryHistoryAccess

/-- An occupied location at an authentic CPU cut has either a later compiled predecessor or a
nonempty finalizer interval. Both choices use the value of the genuine Sail state at that cut. -/
theorem select_at_cut {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    {cut : ℕ} {current : ExecutionState} {frontier : AccessFrontier}
    (atCut : mixedAccessPrefix (policy SP1Prime image) image.program source.realize events cut = some (current, frontier))
    (loc : MemLoc) (used : loc ∈ touchedMemoryLocations (stream image source events rows)) :
    let tape := stream image source events rows
    (∃ i : Fin rows.length, ∃ before r,
      executionTrajectory (policy SP1Prime image) image.program source.realize events i.val = some before ∧
      r ∈ batch image source events rows i ∧ r.loc = loc ∧ r.previous ≤ current.clock ∧ current.clock ≤ before.clock ∧
      before.clock < 2 ^ 48 ∧ locContent current.sail loc = some r.pulled) ∨
    (∃ h ∈ memoryLocationHistories tape, h.loc = loc ∧ h.last.current ≤ current.clock ∧
      locContent current.sail loc = some h.last.pushed) := by
  intro tape
  let history : MemoryLocationHistory := ⟨loc, memoryHistoryAt tape loc, memoryHistoryAt_ne_nil_of_mem used⟩
  have listed : history ∈ memoryLocationHistories tape :=
    List.mem_map.mpr ⟨⟨loc, used⟩, List.mem_attach _ _, rfl⟩
  obtain ⟨_, _, transfers, advances⟩ := records run routed
  have chain := memoryRecordChains_of_chronology transfers.chronology history listed
  have strict : ∀ r ∈ history.accesses, r.previous < r.current := fun _ mem => advances _ (List.mem_filter.mp mem).1
  obtain ⟨first, inTape, located⟩ := mem_touchedMemoryLocations.mp used
  have canonicalLoc := located ▸ canonical run routed first inTape
  have genesis := transfers.first_word loc used
  have seed : history.first.pulled = source.sail.memorySnapshot.read loc :=
    Option.some.inj (genesis.trans (run.1.1.memory.locContent loc canonicalLoc))
  have observed := heldAt_cut run routed atCut loc canonicalLoc
  rw [← seed] at observed
  change locContent current.sail loc = some (heldAt history.first.pulled current.clock history.accesses) at observed
  have selected := history.nextAccess?_covers chain strict current.clock
  cases found : history.nextAccess? current.clock with
  | none =>
    rw [found] at selected
    exact Or.inr ⟨history, listed, rfl, selected.1, observed.trans (congrArg some selected.2)⟩
  | some r =>
    rw [found] at selected
    obtain ⟨occurs, prior, later, word⟩ := selected
    have member : r ∈ tape := (List.mem_filter.mp occurs).1
    obtain ⟨idx, _, atRow⟩ := List.mem_flatMap.mp member
    obtain ⟨before, next, earlier, following, _, window⟩ := batch_values run routed idx
    obtain ⟨state, f, path, seen, _⟩ := admissibleExecution_mixedAccessPrefix run cut
    cases Option.some.inj (atCut.symm.trans seen)
    have ends := (window r atRow).2
    have ordered : cut ≤ idx.val := by
      by_contra! afterwards
      have tooLate := cut_clock_mono (show idx.val + 1 ≤ cut by omega) following path
      omega
    obtain ⟨generated, made, size⟩ := admissibleExecution_routeMixedRows run
    have length : rows.length = events.length := Option.some.inj (routed.symm.trans made) ▸ size
    have here := List.getElem?_eq_getElem (idx.isLt.trans_eq length)
    have terminal := run.1.2.clock_at here earlier
    have bound : target.clock < 2 ^ 48 := run.2.2.2.2.2.1
    change before.clock + _ ≤ target.clock at terminal
    exact Or.inl ⟨idx, before, r, earlier, atRow, chain.located r occurs, prior, cut_clock_mono ordered path earlier,
      by omega, observed.trans (congrArg some word)⟩

end SP1Clean.TraceGen.MixedMemoryHistory
