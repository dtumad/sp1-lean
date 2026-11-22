import SP1Clean.Proofs.Completeness.ExecutionObservation
import SP1Clean.Proofs.Completeness.ReleaseInstructionRows

/-! # Chronological instruction buckets of a mixed execution

Each bucket member comes from its actual ordinary tape position. The chronological router and
the per-position compiler use the same displaced Memory timestamps, including across host calls.
-/

namespace SP1Clean.TraceGen
open Semantics Machine FormalModel.Shard Soundness.Target

private theorem ordinary_cut (events : List ExecutionEvent) {rank : ℕ}
    (bound : rank < events.countP ExecutionEvent.isOrdinary) :
    ∃ cut, events[cut]? = some .ordinary ∧ (events.take cut).countP ExecutionEvent.isOrdinary = rank := by
  induction events generalizing rank with
  | nil => simp at bound
  | cons event rest ih =>
    cases event with
    | syscall call =>
      obtain ⟨cut, atCut, count⟩ := ih (by simpa [List.countP_cons] using bound)
      exact ⟨cut + 1, atCut, by simpa [List.countP_cons] using count⟩
    | ordinary =>
      cases rank with
      | zero => exact ⟨0, rfl, rfl⟩
      | succ k =>
        obtain ⟨cut, atCut, count⟩ := ih (rank := k) (by simpa [List.countP_cons] using bound)
        exact ⟨cut + 1, atCut, by simp [List.countP_cons, count]⟩

/-- The row produced at an ordinary cut is exactly the corresponding chronological bucket input. -/
theorem compiled_mem_at_rank {host : HostPolicy} {program : GuestProgram} {source : ExecutionState}
    {events : List ExecutionEvent} {rows : List RoutedEvent} {cut : ℕ}
    {current next : ExecutionState} {frontier : AccessFrontier} {view : SP1TransitionView}
    {row : CompiledInstructionEvent}
    (route : routeObservations? host program AccessFrontier.initial source events = some rows)
    (ordinary : events[cut]? = some .ordinary)
    (before : mixedAccessPrefix host program source events cut = some (current, frontier))
    (projected : projectSP1Transition? program ⟨current.sail, ⟨.ordinary, next.sail⟩⟩ = some view)
    (made : compileInstructionEvent? view frontier current.clock = some row)
    (after : mixedAccessPrefix host program source events (cut + 1) = some (next, row.nextFrontier)) :
    rows[(events.take cut).countP ExecutionEvent.isOrdinary]? = some row.routed := by
  obtain ⟨s, t, v, r, f, incoming, _, ran, seen, built, rank⟩ := routeObservations?_at route ordinary
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (incoming.symm.trans before))
  rw [mixedAccessPrefix_succ _ _ _ _ ordinary, before] at after
  simp only [Option.bind_some, mixedAccessStep, ran, seen, built, Option.bind_eq_bind, Option.pure_def] at after
  obtain rfl := (Prod.mk.inj (Option.some.inj after)).1
  obtain rfl := Option.some.inj (seen.symm.trans projected)
  obtain rfl := Option.some.inj (built.symm.trans made)
  exact rank

/-- Stable partition of the actual chronological compiler stream supplies a valid input
for every occurrence in all 25 buckets. Each independently demand-padded bucket fits Clean's
row index. Both conclusions follow from the release execution at arbitrary semantic limits. -/
theorem releaseAdmissibleExecution_instructionBuckets {limits : ResourceLimits} {p : ℕ}
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : ReleaseAdmissibleExecution limits p image source target events) :
    ∃ rows, routeObservations? (policy p image) image.program AccessFrontier.initial source.realize events = some rows ∧
      rows.length = events.countP ExecutionEvent.isOrdinary ∧
      ∀ id, Air.Flat.WitnessGeneration.demandHeight (EventBuckets.ofChronological rows id).length ≤ UInt64.size ∧
        ∀ event ∈ EventBuckets.ofChronological rows id, id.Valid event := by
  obtain ⟨rows, route, size, _⟩ := admissibleExecution_routeObservations execution.1
  refine ⟨rows, route, size, fun id => ⟨?_, ?_⟩⟩
  · have length := (EventBuckets.length_le rows id).trans
      (size.le.trans (List.countP_le_length (p := ExecutionEvent.isOrdinary)))
    have duration := execution.1.1.clock
    have work := event_count_le_ticks events
    have last : target.clock < 2 ^ 48 := execution.1.2.2.2.2.2.1
    have height := (Air.Flat.WitnessGeneration.demandHeight_bounds (EventBuckets.ofChronological rows id).length).2
    change _ ≤ 2 ^ 64
    omega
  · intro event member
    obtain ⟨row, occurs, same, payload⟩ := EventBuckets.exists_chronological_of_mem member
    obtain ⟨rank, placed⟩ := List.mem_iff_getElem?.mp occurs
    have bound := (List.getElem?_eq_some_iff.mp placed).1
    obtain ⟨cut, active, rankEq⟩ := ordinary_cut events (size ▸ bound)
    obtain ⟨_, _, _, _, compiled, before, projected, made, after, _, _, valid⟩ :=
      releaseAdmissibleExecution_compile_from_prefix execution active
    have chosen := compiled_mem_at_rank route active before projected made after
    rw [rankEq, placed] at chosen
    obtain rfl := Option.some.inj chosen
    cases same
    exact payload ▸ valid

end SP1Clean.TraceGen
