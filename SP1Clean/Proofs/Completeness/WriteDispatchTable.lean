import SP1Clean.Proofs.Completeness.WriteDispatchRows
import SP1Clean.Proofs.Completeness.WritePlacementCapacity
import ToClean.Air.GuardedDemandTable

/-! # The physical WRITE dispatcher for an admissible mixed shard

Every WRITE, including an empty one, contributes its dispatch row at its actual CPU position.
Clean pads the resulting ordered rows at the installed component's demand height. Recovering
the event pre-state uses the same noncomputable Sail trajectory as the mixed instruction compiler.
-/

namespace SP1Clean.WriteEffects
open Circuit Air.Flat Semantics Machine FormalModel.Shard TraceGen

private abbrev F := ZMod SP1Prime

/-- Recover a dispatch input at the given execution position. Ordinary events and the seven
other syscalls contribute no dispatcher input. -/
noncomputable def dispatchAt? (image : ProgramImage) (source : ExecutionSnapshot) (events : List ExecutionEvent) :
    ExecutionEvent × Nat → Option (Dispatch F)
  | (.ordinary, _) => none
  | (.syscall call, cut) => do
    if call.rawCode ≠ SyscallKind.write.code then none else
    let policy := FormalModel.Shard.policy SP1Prime image
    let current ← executionTrajectory policy image.program source.realize events cut
    let (length, _) ← WriteObservations.read? current.sail call
    let (store, _) ← HintQueue.storeAfter? policy image.program source.realize (events.take cut) (HintQueue.ofList source.host.io.hints)
    return dispatchRow call.arg1 call.arg2 length current.clock ((events.take cut).foldl advanceWriteClock source.clock)
      (WriteStreams.fromEndpoints source.host current.host) current.host store

/-- Dispatchers appear in source order, indexed by the entire event tape. -/
noncomputable def dispatchInputs (image : ProgramImage) (source : ExecutionSnapshot) (events : List ExecutionEvent) : List (Dispatch F) :=
  events.zipIdx.filterMap (dispatchAt? image source events)

private theorem dispatchAt_valid {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events)
    {event : ExecutionEvent} {cut : Nat} (present : events[cut]? = some event) :
    let input := dispatchAt? image source events (event,cut)
    input.isSome = WriteObservations.isWriteCall event ∧ ∀ r ∈ input, r.Valid := by
  cases event with
  | ordinary => simp [dispatchAt?, WriteObservations.isWriteCall]
  | syscall call =>
    by_cases write : call.rawCode = SyscallKind.write.code
    · obtain ⟨current, _, len, buf, cursor, reached, _, read, store, valid, _⟩ := native_dispatch_at run present write
      simpa [dispatchAt?, WriteObservations.isWriteCall, write, reached, read, store] using valid
    · simp [dispatchAt?, WriteObservations.isWriteCall, write]

/-- All and only actual WRITEs supply valid inputs, in particular zero-byte and ignored writes. -/
theorem dispatchInputs_valid {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) :
    (dispatchInputs image source events).length = events.countP WriteObservations.isWriteCall ∧
    ∀ r ∈ dispatchInputs image source events, r.Valid := by
  constructor
  · rw [dispatchInputs, List.length_filterMap_eq_countP]
    calc
      _ = events.zipIdx.countP (WriteObservations.isWriteCall ∘ Prod.fst) := by
        apply List.countP_congr
        intro ⟨event, cut⟩ h
        rw [(dispatchAt_valid run (List.mk_mem_zipIdx_iff_getElem?.mp h)).1]
        rfl
      _ = _ := by rw [← List.countP_map, List.zipIdx_map_fst]
  · intro row member
    obtain ⟨⟨event, cut⟩, h, built⟩ := List.mem_filterMap.mp member
    exact (dispatchAt_valid run (List.mk_mem_zipIdx_iff_getElem?.mp h)).2 row built

/-- Clean's physical dispatcher table, including its canonical zero-weight padding. -/
def dispatchTable (inputs : List (Dispatch F)) (data : ProverData F)
    (fit : WitnessGeneration.demandHeight inputs.length ≤ UInt64.size) : Table F :=
  Table.ofInputs dispatchComponent (WitnessGeneration.guardedRows inputs) data
    ((WitnessGeneration.guardedRows_length inputs).le.trans fit) (fun _ => trivial)

/-- Construct the installed dispatcher at the tight height already paid for by the shard's
WRITE count. All local constraints and channel guarantees hold for the generated physical rows. -/
theorem native_dispatch_table {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (data : ProverData F) :
    ∃ fit : WitnessGeneration.demandHeight (dispatchInputs image source events).length ≤ UInt64.size,
      let t := dispatchTable (dispatchInputs image source events) data fit
      t.component = dispatchComponent ∧ t.Constraints ∧ t.Guarantees ∧
      t.table.length = WitnessGeneration.demandHeight (events.countP WriteObservations.isWriteCall) ∧ t.table.length ≤ 2^16 := by
  obtain ⟨packets, _, count, height, _⟩ := admissible_placement_heights run (.refl _)
  obtain ⟨length, valid⟩ := dispatchInputs_valid run
  rw [count, ← length] at height
  let inputs := dispatchInputs image source events
  let rows := WitnessGeneration.guardedRows (F := F) inputs
  have size : rows.length = WitnessGeneration.demandHeight inputs.length := WitnessGeneration.guardedRows_length inputs
  have allowed : rows.length ≤ UInt64.size := size.le.trans (height.trans (by decide))
  obtain ⟨checked, guarantees⟩ := Table.ofInputs_valid (dispatchComponent (p := SP1Prime)) rows data allowed (fun _ => trivial)
    (WitnessGeneration.guardedRows_all Dispatch.Valid valid)
  have realized := Table.ofInputs_length (dispatchComponent (p := SP1Prime)) rows data allowed (fun _ => trivial)
  exact ⟨height.trans (by decide), rfl, checked, guarantees, (realized.trans size).trans (congrArg _ length), (realized.trans size).le.trans height⟩

end SP1Clean.WriteEffects
