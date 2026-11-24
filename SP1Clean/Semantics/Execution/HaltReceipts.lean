module

public import SP1Clean.Semantics.Execution.ExecutionPath

/-! # New terminal receipts on an arbitrary local execution segment -/

@[expose] public section
namespace SP1Clean
open Machine Semantics

/-- A canonical HALT event supplies its actual unsigned exit value, including zero. -/
def Machine.ExecutionEvent.haltReceipt? : ExecutionEvent → Option (BitVec 32)
  | .ordinary => none
  | .syscall call => if call.rawCode = 0 then some (call.arg1.setWidth 32) else none

/-- The whole label tape has exactly the new exit receipt of this segment. A segment
starting after a previous HALT contributes no new receipt. -/
theorem Semantics.ExecutionPath.haltReceipts {policy : HostPolicy} {program : Soundness.Target.GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent} (path : ExecutionPath policy program source events target) :
    events.filterMap ExecutionEvent.haltReceipt? = (if source.host.exitCode = none then target.host.exitCode else none).toList := by
  induction path with
  | nil state => cases state.host.exitCode <;> simp
  | @cons s m t event events step tail ih =>
    have receipt : event.haltReceipt? = m.host.exitCode := by cases event <;> exact step.exit.symm
    rw [step.running,ite_eq_left rfl,List.filterMap_cons,receipt]
    cases status : m.host.exitCode with
    | none => simpa [status] using ih
    | some code =>
      obtain ⟨rfl,rfl⟩ := tail.of_halted (by rw [status]; simp)
      simp [status]

end SP1Clean
