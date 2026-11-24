import SP1Clean.Proofs.Completeness.MixedMemoryRecords

/-! # Sail values posted by the generated mixed Memory history

Ordinary instructions and ECALLs publish their canonical register schedules. Each padded
HINT_READ word also updates its aligned RAM cell at the host transfer's actual record clock.
-/

namespace SP1Clean.TraceGen.MixedMemoryHistory

open Semantics Machine FormalModel.Shard Soundness.Target
open MemoryHistoryAccess

/-- At each genuine event position, its original physical transfers produce the complete outgoing
Sail register/RAM image and lie strictly after the incoming CPU clock and before the next cut. -/
theorem batch_values {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (index : Fin rows.length) :
    ∃ before next, executionTrajectory (policy SP1Prime image) image.program source.realize events index.val = some before ∧
      executionTrajectory (policy SP1Prime image) image.program source.realize events (index.val + 1) = some next ∧
      post (locContent before.sail) (batch image source events rows index) = locContent next.sail ∧
      ∀ a ∈ batch image source events rows index, before.clock < a.current ∧ a.current ≤ next.clock := by
  obtain ⟨before, incoming, atCut, prefixAt, _⟩ := admissibleExecution_mixedAccessPrefix run index.val
  obtain ⟨next, outgoing, atNext, prefixNext, _⟩ := admissibleExecution_mixedAccessPrefix run (index.val + 1)
  obtain ⟨valid, _, window⟩ := batch_records run routed index prefixAt prefixNext
  exact ⟨before, next, atCut, atNext, valid.post_eq, window⟩

private theorem cut_clock_mono {p : HostPolicy} {program : GuestProgram} {source early late : ExecutionState}
    {events : List ExecutionEvent} {i j : ℕ} (ordered : i ≤ j)
    (before : executionTrajectory p program source events i = some early)
    (after : executionTrajectory p program source events j = some late) : early.clock ≤ late.clock := by
  have split := List.take_append_drop i (events.take j)
  rw [List.take_take, Nat.min_eq_left ordered] at split
  rw [replayEvents?_clock (events := events.take i) before, replayEvents?_clock (events := events.take j) after]
  conv_rhs => rw [← split, List.map_append, List.sum_append]
  omega

/-- The held word of the complete original mixed transfer stream is the actual Sail value at every
CPU cut and every canonical register or RAM location. The initial value comes from the realized
incoming boundary. Both touched and untouched locations use this same query. -/
theorem heldAt_cut {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    {cut : ℕ} {current : ExecutionState} {frontier : AccessFrontier}
    (atCut : mixedAccessPrefix (policy SP1Prime image) image.program source.realize events cut = some (current, frontier))
    (loc : MemLoc) (canonicalLoc : loc.CanonicalAddress) :
    locContent current.sail loc = some (heldAt (source.sail.memorySnapshot.read loc) current.clock
      (memoryHistoryAt (stream image source events rows) loc)) := by
  obtain ⟨actual, f, path, found, _⟩ := admissibleExecution_mixedAccessPrefix run cut
  cases Option.some.inj (atCut.symm.trans found)
  let indices := List.finRange rows.length
  let emit := batch image source events rows
  have split : stream image source events rows = (indices.take cut).flatMap emit ++ (indices.drop cut).flatMap emit := by
    rw [← List.flatMap_append, List.take_append_drop]
    rfl
  have earlier : ∀ a ∈ (indices.take cut).flatMap emit, a.current ≤ current.clock := by
    intro a mem
    obtain ⟨idx, member, occurs⟩ := List.mem_flatMap.mp mem
    obtain ⟨j, bound, eq⟩ := List.mem_take_iff_getElem.mp member
    have coordinate : idx.val = j := by rw [← eq]; simp [indices]
    obtain ⟨before, next, _, after, _, window⟩ := batch_values run routed idx
    exact (window a occurs).2.trans (cut_clock_mono (by omega) after path)
  have later : ∀ a ∈ (indices.drop cut).flatMap emit, current.clock < a.current := by
    intro a mem
    obtain ⟨idx, member, occurs⟩ := List.mem_flatMap.mp mem
    obtain ⟨j, _, eq⟩ := List.mem_drop_iff_getElem.mp member
    have coordinate : idx.val = cut + j := by rw [← eq]; simp [indices]
    obtain ⟨before, next, prior, _, _, window⟩ := batch_values run routed idx
    exact (cut_clock_mono (by omega) path prior).trans_lt (window a occurs).1
  rw [split, heldAt_post earlier later (values := locContent source.realize.sail) loc _ (run.1.1.memory.locContent loc canonicalLoc)]
  exact congrFun (prefix_records run routed atCut).1.post_eq.symm loc

end SP1Clean.TraceGen.MixedMemoryHistory
