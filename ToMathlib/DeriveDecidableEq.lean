module

public meta import Mathlib.Lean.Meta.Basic
public meta import Lean.Elab.Deriving.DecEq
public meta import Lean.Elab.Deriving.Util
meta import all Lean.Elab.Deriving.DecEq

/-! # Named structural equality instances

Standalone `deriving instance DecidableEq` does not accept an instance name. For imported
types whose names contain underscores, its generated names violate the definition-name linter.
This additive entry point reuses Lean's derivation with a caller-chosen name. Replace it with
the standard command when upstream supports naming standalone derived instances.
-/

public meta section

namespace Lean.Elab.Deriving

/-- Derive structural equality for one nonrecursive, nonnested inductive, using an explicit
instance name. Constructor comparisons and proofs use Lean's standard derivation, including
its linear construction for large variants. -/
def deriveDecidableEqNamed (typeName instanceName : Name) : Command.CommandElabM Unit := do
  let commands ← Command.liftTermElabM do
    let context ← mkContext ``DecidableEq "decEq" typeName
    unless context.typeInfos.size == 1 && !context.usePartial && !context.typeInfos[0]!.isRec do
      throwError "named equality derivation requires one nonrecursive, nonnested inductive"
    let context := { context with instName := instanceName, auxFunNames := #[instanceName ++ `decEq] }
    return #[ (← DecEq.mkAuxFunctions context).raw ] ++
      (← mkInstanceCmds context `DecidableEq #[typeName] (useAnonCtor := false)).map (·.raw)
  withEnableInfoTree false do
    commands.forM Command.elabCommand

end Lean.Elab.Deriving
