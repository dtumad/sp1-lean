module

public import SP1CleanTest.Alignment.Support.InstalledAssemblyExport

/-! # Shared native reference encoding for installed export fixtures

This serializes the existing witness and checker results; Clean still owns generation,
constraints, interactions and Rust emission. Retain empty tables and zero occurrences.
-/

@[expose] public section

namespace SP1CleanTest.Alignment.InstalledAssemblyReference

open Lean

/-- Literal channel, payload and multiplicity, including zero occurrences. -/
def interactionReference (interaction : Interaction (ZMod SP1Clean.SP1Prime)) : Json :=
  Json.mkObj [
    ("channel", toJson interaction.channel.name),
    ("message", toJson (interaction.msg.map (·.val))),
    ("multiplicity", toJson interaction.mult.val),
    ("assumeGuarantees", toJson interaction.assumeGuarantees)]

/-- Every table and physical interaction, in its original order. -/
def physicalReference {PublicIO : TypeMap} [ProvableType PublicIO]
    {ensemble : Air.Flat.Ensemble (ZMod SP1Clean.SP1Prime) PublicIO}
    (witness : Air.Flat.EnsembleWitness ensemble) : Json :=
  Json.mkObj [
    ("tables", toJson (witness.tables.map fun table =>
      table.table.map fun row => row.map (·.val))),
    ("interactions", toJson (witness.interactions.map interactionReference))]


/-- Run the native scheduler and authenticated checker before recording the expected result. -/
def installedCase (context : SP1CleanTest.Alignment.InstalledAssembly.Context)
    (consumers : List SP1CleanTest.Alignment.InstalledAssembly.Seed)
    (name : String) (publicInput : SP1Clean.SP1PublicIO (ZMod SP1Clean.SP1Prime))
    (privateInput : fields (SP1CleanTest.Alignment.InstalledAssemblyExport.privateInput context consumers).size
      (ZMod SP1Clean.SP1Prime)) (expected : Bool) : IO Json := do
  -- The built-in exporter checks that this verifier depends only on public inputs.
  -- Retain its occurrences even when witness generation rejects the instance.
  let verifier := (SP1CleanTest.Alignment.InstalledAssemblyExport.installed context).verifierOperations
    |>.interactionValues (Environment.fromInput publicInput (fun _ _ => #[]))
  let fields := [("name", toJson name), ("accepted", toJson expected),
    ("verifier", toJson (verifier.map interactionReference)),
    ("publicInput", toJson ((toElements publicInput).toArray.map (·.val))),
    ("privateInput", toJson (privateInput.toArray.map (·.val)))]
  match SP1CleanTest.Alignment.InstalledAssemblyExport.generate context consumers publicInput privateInput with
  | .error message =>
    if expected then throw (IO.userError s!"installed assembly {name}: {message}")
    pure (Json.mkObj (fields ++ [("error", toJson message)]))
  | .ok witness =>
    unless (SP1CleanTest.Alignment.InstalledAssembly.description context).checkWitness
        SP1Clean.SP1Prime witness == expected do
      throw (IO.userError s!"unexpected installed assembly acceptance: {name}")
    pure (Json.mkObj (fields ++ [("witness", physicalReference witness)]))

/-- Physical table positions and fixed-column dimensions. -/
def installedInventory (context : SP1CleanTest.Alignment.InstalledAssembly.Context) : Json :=
  toJson ((SP1CleanTest.Alignment.InstalledAssemblyExport.installed context).tables.map fun component =>
    Json.mkObj [("name", toJson component.circuit.name), ("width", toJson component.width),
      ("fixedWidth", toJson (component.fixedColumns.map (·.width) |>.getD 0)),
      ("fixedHeight", toJson (component.fixedColumns.map (·.height.toNat) |>.getD 0))])


end SP1CleanTest.Alignment.InstalledAssemblyReference
