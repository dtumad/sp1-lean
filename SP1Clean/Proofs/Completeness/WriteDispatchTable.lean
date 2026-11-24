import SP1Clean.Proofs.Completeness.WriteDispatchReplay
import SP1Clean.Proofs.Completeness.WritePlacementCapacity
import ToClean.Air.GuardedDemandTable

/-! # The physical WRITE dispatcher for an admissible mixed shard

Every WRITE, including an empty one, contributes its dispatch row at its actual CPU position.
Clean pads the shared chronological collector’s dispatch projection at the installed component’s demand height.
-/

namespace SP1Clean.WriteEffects
open Circuit Air.Flat Semantics Machine FormalModel.Shard TraceGen

private abbrev F := ZMod SP1Prime

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
