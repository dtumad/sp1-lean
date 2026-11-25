import SP1Clean.Math.SP1Field
import SP1Clean.Native.Chips.HaltPaddingChip
import SP1Clean.FormalModel.Contracts.ShardHeader
import SP1Clean.Semantics.Host.HostReplay
import SP1Clean.Soundness.BumpDecode
import ToClean.Air.GuardedDemandTable

/-! # Physical legacy Exit padding for arbitrary mixed local segments

The original syscall table owns a real HALT. The legacy padding component supplies a zero
receipt exactly when the segment has no new terminal event, including a parked empty segment.
-/

namespace SP1Clean.TraceGen.MixedHaltPadding
open Circuit Air.Flat Semantics Machine Channels Soundness
private abbrev F := ZMod SP1Prime

/-- The original scheduler input for a checkpoint. A real terminal segment has no legacy row. -/
def inputs (source target : ExecutionSnapshot) : List (HaltChip.Inputs F) :=
  match SP1StateBoundary.haltCode source target with
  | none => [HaltChip.paddingInputs]
  | some _ => []

/-- Compile the original HALT padding component from the complete endpoints. -/
def table (source target : ExecutionSnapshot) (data : ProverData F) : Table F :=
  Table.ofInputs HaltPaddingChip.component (inputs source target) data (by unfold inputs; split <;> decide) (fun _ => trivial)

/-- The legacy physical table has its designated inactive row or zero rows, according to the
actual source-to-target exit transition. Every generated row is locally checked. -/
theorem checked (source target : ExecutionSnapshot) (data : ProverData F) :
    let t := table source target data
    t.Constraints ∧ t.Guarantees ∧ t.length = (if (SP1StateBoundary.haltCode source target).isNone then 1 else 0) := by
  intro t
  have valid : t.Constraints ∧ t.Guarantees := by
    apply Table.ofInputs_valid
    intro i inside
    change HaltChip.Spec i ∧ i.is_real = 0
    unfold inputs at inside
    split at inside
    · cases List.mem_singleton.mp inside
      exact ⟨HaltChip.spec_paddingInputs,rfl⟩
    · contradiction
  refine ⟨valid.1,valid.2,?_⟩
  trans (inputs source target).length
  · exact Table.ofInputs_length HaltPaddingChip.component (inputs source target) data _ _
  unfold inputs
  cases SP1StateBoundary.haltCode source target <;> rfl

/-- The original legacy decoder recovers the literal disabled input at any evaluation data. -/
theorem all_inputs (source target : ExecutionSnapshot) (data evaluation : ProverData F) :
    (table source target data).table.map (haltRow evaluation) = inputs source target :=
  Table.build_inputs HaltPaddingChip.component (inputs source target) _ (.empty _) (by unfold inputs; split <;> decide) (by trivial)
    (HaltPaddingChip.component.inputData_consistent _ data) evaluation

private def output (r : HaltChip.Inputs F) : List (Interaction F) :=
  [exitChannel.pushedIfValue r.is_real (HaltChip.exitMessage r),exitChannel.pushedIfValue (1-r.is_real) ⟨0⟩]

private theorem emitted (env : Environment F) : HaltPaddingChip.component.operations.interactionValuesWith exitChannel.toRaw env =
    output (HaltPaddingChip.component.rowInput env) := by
  rw [Operations.interactionValuesWith,HaltPaddingChip.interactions,Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval env) (((HaltChip.main (varFromOffset HaltChip.Inputs 0 : Var HaltChip.Inputs F)).operations (size HaltChip.Inputs)).interactionsWith exitChannel.toRaw) = _
  rw [HaltChip.interactionsWith_exit_eq]
  simp only [output,List.map_cons,List.map_nil,Channel.eval_pushedIf]
  change _ = [exitChannel.pushedIfValue (valueFromOffset HaltChip.Inputs 0 env).is_real (HaltChip.exitMessage (valueFromOffset HaltChip.Inputs 0 env)),exitChannel.pushedIfValue (1-(valueFromOffset HaltChip.Inputs 0 env).is_real) ⟨0⟩]
  rw [← eval_varFromOffset_valueFromOffset HaltChip.Inputs]
  simp only [HaltChip.exitMessage,HaltChip.exitMsg,HaltChip.exitPaddingMsg,circuit_norm]

/-- All actual physical Exit occurrences on the original table, including its disabled push.
A real HALT with code zero takes the empty branch just like any other real HALT. -/
theorem ledger (source target : ExecutionSnapshot) (data : ProverData F) :
    (table source target data).interactionsWith exitChannel.toRaw =
      if (SP1StateBoundary.haltCode source target).isNone then
        [exitChannel.pushedIfValue 0 ⟨0⟩,exitChannel.pushedIfValue 1 ⟨0⟩] else [] := by
  trans (inputs source target).flatMap output
  · exact Table.ofInputs_ledger HaltPaddingChip.component (inputs source target) data _ _ _ output emitted
  unfold inputs
  cases SP1StateBoundary.haltCode source target
  · simp [output,HaltChip.paddingInputs,HaltChip.exitMessage]
  · rfl

/-- On the full execution tape the physical padding and the genuine HALT complement one
another, producing precisely the public header's exit code. -/
theorem receipt {policy : HostPolicy} {program : Target.GuestProgram} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (path : ExecutionPath policy program source.realize events target.realize) :
    (inputs source target).map (fun _ => (0 : BitVec 32)) ++ events.filterMap (hostExitAfter none) =
      [(SP1StateBoundary.haltCode source target).getD 0] := by
  have actual : events.filterMap (hostExitAfter none) = (SP1StateBoundary.haltCode source target).toList := by
    rw [path.exit_receipts]
    unfold SP1StateBoundary.haltCode
    change (if source.host.exitCode = none then target.host.exitCode.toList else []) = _
    split <;> rfl
  rw [actual]
  unfold inputs
  cases SP1StateBoundary.haltCode source target <;> rfl

end SP1Clean.TraceGen.MixedHaltPadding
