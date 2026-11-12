import Lean
import SP1Clean

/-! # Proof closure of the headline results

Reports which repository declarations the headline soundness theorem and the capstone targets
depend on. Declaration types, definition bodies and theorem proofs are all followed; the compiled
contract audit (`capstoneContract.lean`) records only the statement surface and stops at proofs.
External declarations are boundary nodes and are not traversed.

This is a report for retiring code that no headline result uses. It is neither a gate nor a proof.
A module outside the closure may still guard a distinct claim through a test, or be planned
material for an open obligation; deleting it is a reviewed decision.

Run through `scripts/proof_closure.py`, which supplies `PROOF_CLOSURE_OUT` and optional
`PROOF_CLOSURE_ROOTS` (comma-separated declaration names).
-/

namespace ProofClosureAudit

open Lean

/-- The headline soundness theorem, the capstone targets and the machine they interpret. -/
def defaultRoots : Array Name := #[
  ``SP1Clean.Soundness.Shard.sail_trace,
  ``SP1Clean.Soundness.Shard.statement_iff,
  ``SP1Clean.Soundness.Shard.statement_iff_of_realizes,
  ``SP1Clean.Soundness.Shard.realizes,
  ``SP1Clean.FormalModel.Shard.AdmissibleExecution,
  ``SP1Clean.FormalModel.Shard.sp1Machine,
  ``Air.Flat.Realizes]

/-- The owning module is used rather than the namespace, which is decoupled from paths. -/
def moduleOf (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some index => env.header.moduleNames[index.toNat]!
  | none => env.mainModule

/-- Repository modules are traversed; pinned upstream declarations are boundary nodes. -/
def localModule (name : Name) : Bool :=
  ["SP1Clean", "ToClean", "ToMathlib"].any
    (fun rootName => name.toString.startsWith (rootName ++ "."))

/-- Iterative traversal of types, values (including theorem proofs) and constructors. -/
def closure (env : Environment) (roots : List Name) : Except String NameSet := do
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | throw s!"missing declaration: {name}"
    if localModule (moduleOf env name) then
      pending := info.type.getUsedConstants.toList ++ pending
      if let some value := info.value? (allowOpaque := true) then
        pending := value.getUsedConstants.toList ++ pending
      if let .inductInfo declaration := info then
        pending := declaration.ctors ++ pending
  return seen

def report (env : Environment) (roots : Array Name) : Except String Json := do
  let seen ← closure env roots.toList
  let reachable := seen.toList.filterMap fun name =>
    let owner := moduleOf env name
    if localModule owner then
      some (Json.mkObj [("name", toJson name.toString), ("module", toJson owner.toString)])
    else none
  let modules := env.header.moduleNames.filter localModule
  return Json.mkObj [
    ("version", toJson (1 : Nat)),
    ("roots", toJson (roots.map Name.toString)),
    ("modules", toJson (modules.map Name.toString)),
    ("reachable", Json.arr reachable.toArray)]

run_cmd do
  let env ← Lean.getEnv
  let some destination ← IO.getEnv "PROOF_CLOSURE_OUT"
    | throwError "PROOF_CLOSURE_OUT is required; use scripts/proof_closure.py"
  let roots := match ← IO.getEnv "PROOF_CLOSURE_ROOTS" with
    | some text => (text.splitOn ",").filter (· ≠ "") |>.map String.toName |>.toArray
    | none => defaultRoots
  match report env roots with
  | .error message => throwError message
  | .ok result => IO.FS.writeFile destination (result.compress ++ "\n")

end ProofClosureAudit
