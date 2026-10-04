import SP1CleanTest.Core.EnsembleExport

/-! # Clean's built-in whole-ensemble Rust export fixture

Generated sources and Lean reference rows stay under the ignored build tree. The comparison
script selects a fresh directory through ENSEMBLE_EXPORT_OUT and checks the completion marker.
-/

open Lean SP1CleanTest.Core.EnsembleExport

private def exportEnsembleFixture : IO Unit := do
  let out := System.FilePath.mk
    ((← IO.getEnv "ENSEMBLE_EXPORT_OUT").getD ".lake/build/ensemble-export")
  IO.FS.createDirAll out
  let exported ← match rust with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  IO.FS.writeFile (out / "fixed_membership.rs") exported
  let cases ← ([7, 9, 8] : List Nat).mapM fun (value : Nat) => do
    let result ← match generate (Nat.cast value) with
      | .error message => pure <| Json.mkObj [
          ("publicInput", toJson value), ("accepted", toJson false), ("error", toJson message)]
      | .ok witness => do
          let accepted := description.checkWitness SP1Clean.SP1Prime witness
          unless accepted do throw (IO.userError "generated witness failed raw acceptance")
          pure <| Json.mkObj [
            ("publicInput", toJson value), ("accepted", toJson accepted),
            ("tables", toJson (witness.tables.map fun table =>
              table.table.map fun row => row.map (·.val))),
            ("interactionCount", toJson witness.interactions.length)]
    pure result
  IO.FS.writeFile (out / "fixed_membership.reference.json") ((toJson cases).compress ++ "\n")
  IO.println "EXPORTED ensemble Rust and Lean reference cases"

#eval exportEnsembleFixture
