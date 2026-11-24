import SP1Clean.Proofs.Completeness.WriteWitnessPosition

/-! # Chronological construction of every physical WRITE dispatcher

The installed dispatcher consumes the dispatcher-only projection of the shared CPU traversal.
Every successful full allocation witness supplies exactly the same ordered rows, at arbitrary
node, block and immutable-word query multiplicities.
-/

namespace SP1Clean.WriteEffects

open Semantics Machine FormalModel.Shard TraceGen WriteAllocation
private abbrev F := ZMod SP1Prime

/-- Dispatcher rows for the actual table, obtained by replaying each CPU event once.
The projection consumes the observed packet and current store directly. -/
noncomputable def dispatchInputs (image : ProgramImage) (source : ExecutionSnapshot) (events : List ExecutionEvent) : List (Dispatch F) :=
  (dispatchTape? image source.host source.clock source.realize (HintQueue.ofList source.host.io.hints) events).getD []

/-- The table's dispatch inputs are the projection of the same real WRITE positions as the
full packet and queue collector, for every choice of immutable read multiplicities. -/
theorem dispatchInputs_positions {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers) :
    let entries := events.zipIdx.filterMap fun (e,i) => Witness.position image source events readers e i
    dispatchTape? image source.host source.clock source.realize (HintQueue.ofList source.host.io.hints) events =
      some (entries.map Witness.Entry.dispatch) ∧ dispatchInputs image source events = entries.map Witness.Entry.dispatch := by
  obtain ⟨built,_⟩ := Witness.native_collect run readers
  have delivered := Witness.dispatch_projection image source.host readers source.clock source.realize (HintQueue.ofList source.host.io.hints) events
  rw [← Witness.native?, built, Option.map_some] at delivered
  exact ⟨delivered, by rw [dispatchInputs,delivered]; rfl⟩

/-- The shared CPU traversal succeeds on every admissible mixed execution, in actual dispatch order. -/
theorem native_dispatch_replay {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) :
    dispatchTape? image source.host source.clock source.realize (HintQueue.ofList source.host.io.hints) events =
      some (dispatchInputs image source events) := by
  obtain ⟨built, inputs⟩ := dispatchInputs_positions run ⟨fun _ => 0,fun _ => 0,fun _ => 0⟩
  exact built.trans (congrArg some inputs.symm)

/-- All and only actual WRITEs supply valid inputs, including zero-byte and ignored writes. -/
theorem dispatchInputs_valid {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) :
    (dispatchInputs image source events).length = events.countP WriteObservations.isWriteCall ∧
    ∀ r ∈ dispatchInputs image source events, r.Valid := by
  let readers : Readers := ⟨fun _ => 0,fun _ => 0,fun _ => 0⟩
  rw [(dispatchInputs_positions run readers).2]
  constructor
  · rw [List.length_map,List.length_filterMap_eq_countP]
    calc
      _ = events.zipIdx.countP (WriteObservations.isWriteCall ∘ Prod.fst) := by
        apply List.countP_congr
        intro ⟨event,cut⟩ used
        rw [(Witness.native_position_active run readers (List.mk_mem_zipIdx_iff_getElem?.mp used)).1]
        rfl
      _ = _ := by rw [← List.countP_map, List.zipIdx_map_fst]
  · intro dispatch used
    obtain ⟨entry, member, rfl⟩ := List.mem_map.mp used
    obtain ⟨⟨event,cut⟩, original, found⟩ := List.mem_filterMap.mp member
    exact (Witness.native_position_active run readers (List.mk_mem_zipIdx_iff_getElem?.mp original)).2 entry found

end SP1Clean.WriteEffects
