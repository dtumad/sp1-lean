module

public import SP1Clean.Model.SP1Field
public import SP1Clean.Native.Operations.CommitmentBoundary
public import SP1Clean.Native.Operations.CommitmentStatement
public import ToClean.Air.TableBuild

/-! # Canonical commitment fields and fixed-provider rows

These checks exercise the u32/public-byte distinction, deferred-field boundaries and the
complete sixteen-row provider. Agreement does not imply that any slot was actually declared.
-/

@[expose] public section

namespace SP1CleanTest.Core.CommitmentBoundary

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core

private def statement : CommitmentStatement :=
  ⟨Vector.replicate 8 0x89abcdef,
    Vector.replicate 8 (BitVec.ofNat 32 (SP1Prime - 1)), true, false⟩

example : statement.WellFormed SP1Prime := by decide
example : ¬ ({ statement with deferred := Vector.replicate 8 (BitVec.ofNat 32 SP1Prime) }).WellFormed SP1Prime := by decide
example : (SP1Clean.CommitmentBoundary.committed (p := SP1Prime) statement).toList.take 4 =
    [239, 205, 171, 137] := by decide
example : SP1Clean.CommitmentBoundary.deferred (p := SP1Prime) statement =
    Vector.replicate 8 (-1 : ZMod SP1Prime) := by native_decide
example : (CommitmentDeclaration.rows (p := SP1Prime) statement).length = 16 := by decide
example : (CommitmentDeclaration.encode (p := SP1Prime) statement true 7).flag = 0 := by decide
example : (CommitmentDeclaration.encode (p := SP1Prime) statement false 7).flag = 1 := by decide
example : (CommitmentDeclaration.source (p := SP1Prime) statement).fixedColumns.isSome := by decide

end SP1CleanTest.Core.CommitmentBoundary
