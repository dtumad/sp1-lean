import SP1CleanTest.Alignment.Support.InstalledAssemblyExport
import SP1CleanTest.Core.ComponentExport

/-! # Shared native reference encoding for installed export fixtures

This serializes the existing witness and checker results; Clean still owns generation,
constraints, interactions and Rust emission. Retain empty tables and zero occurrences.
-/

namespace SP1CleanTest.Alignment.InstalledAssemblyReference

open Lean

open SP1CleanTest.Core.ComponentExport (interactionReference physicalReference)

/-- Run the native scheduler and authenticated checker before recording the expected result. -/
def installedCase (context : SP1Clean.Export.InstalledAssembly.Context)
    (prepared : SP1CleanTest.Alignment.InstalledAssemblyExport.Prepared)
    (name : String) (publicInput : SP1Clean.SP1PublicIO (ZMod SP1Clean.SP1Prime))
    (privateInput : fields prepared.data.size
      (ZMod SP1Clean.SP1Prime)) (expected : Bool) : IO Json := do
  -- The built-in exporter checks that this verifier depends only on public inputs.
  -- Retain its occurrences even when witness generation rejects the instance.
  let verifier := (SP1Clean.Export.InstalledAssembly.assembly context).verifierOperations
    |>.interactionValues (Environment.fromInput publicInput (ProverData.empty (ZMod SP1Clean.SP1Prime)))
  let fields := [("name", toJson name), ("accepted", toJson expected),
    ("verifier", toJson (verifier.map interactionReference)),
    ("publicInput", toJson ((toElements publicInput).toArray.map (·.val))),
    ("privateInput", toJson (privateInput.toArray.map (·.val)))]
  match SP1CleanTest.Alignment.InstalledAssemblyExport.generate context prepared publicInput privateInput with
  | .error message =>
    if expected then throw (IO.userError s!"installed assembly {name}: {message}")
    pure (Json.mkObj (fields ++ [("error", toJson message)]))
  | .ok witness =>
    unless (SP1Clean.Export.InstalledAssembly.description context).checkWitness
        (witness.withEnsemble (SP1Clean.Export.InstalledAssembly.assembly context) rfl) == expected do
      throw (IO.userError s!"unexpected installed assembly acceptance: {name}")
    pure (Json.mkObj (fields ++ [("witness", physicalReference witness)]))

/-- Physical table positions and fixed-column dimensions. -/
def installedInventory (context : SP1Clean.Export.InstalledAssembly.Context) : Json :=
  toJson ((SP1Clean.Export.InstalledAssembly.assembly context).tables.map fun component =>
    Json.mkObj [("name", toJson component.circuit.name), ("width", toJson component.width),
      ("fixedColumns", toJson (component.generation.cells.1.toList.zipIdx.filterMap
        (fun (cell, index) => if cell.isFixed then some index else none))),
      ("fixedHeight", toJson (match component.generation with
        | .preallocated mode => mode.height.toNat
        | .demand _ => 0))])


end SP1CleanTest.Alignment.InstalledAssemblyReference
