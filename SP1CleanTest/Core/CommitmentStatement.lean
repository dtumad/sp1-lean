import SP1Clean.Model.Core.CommitmentStatement
import SP1Clean.Model.Core.HostExecution
import SP1Clean.Model.SP1Field

/-! # Declaration consistency is distinct from execution and coverage

These cases exercise the immutable statement meaning, including repeated declarations,
partial coverage, flags and conflicting writes that the operational host still executes.
-/

namespace SP1CleanTest.Core.CommitmentStatement

open SP1Clean.Model.Core SP1Clean.Machine

private def statement : CommitmentStatement :=
  ⟨Vector.replicate 8 7, Vector.replicate 8 9, true, true⟩

private def declaration (deferred : Bool) (slot value : ℕ) : ExecutionEvent :=
  .syscall ⟨1, 65536, 65540, (if deferred then SyscallKind.commitDeferred else .commit).code,
    BitVec.ofNat 64 slot, BitVec.ofNat 64 value,
    (if deferred then SyscallKind.commitDeferred else .commit).code⟩

example : statement.Matches [] := by decide
example : statement.Matches [declaration false 0 7, declaration false 0 7] := by decide
example : statement.Matches [declaration true 7 9] := by decide
example : ¬ statement.Matches [declaration false 0 7, declaration false 0 9] := by decide
example : ¬ statement.Matches [declaration false 8 7] := by decide
example : ¬ statement.Matches [declaration true 7 7] := by decide
example : ¬ ({ statement with commit := false }).Matches [declaration false 0 7] := by decide
example : ({ statement with committed := statement.committed.set 7 99 }).Matches
    [declaration false 0 7] := by decide

private def policy : HostPolicy := ⟨{ readOnly := fun _ => false }, SP1Clean.SP1Prime⟩
private def context : HostReadContext := ⟨fun _ => none, fun _ => none⟩

/-- An overwritten recording slot remains a successful operational update. -/
example : (HostState.executeKind { committed := Vector.replicate 8 7 }
    policy context .commit 0 9).map (·.state.committed[0]) = some 9 := by decide

end SP1CleanTest.Core.CommitmentStatement
