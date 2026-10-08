import SP1CleanTest.Core.EnsembleExport
import SP1CleanTest.Core.InstructionExport

/-! # Clean's built-in whole-ensemble Rust export fixture

Generated sources and Lean reference rows stay under the ignored .lake/ensemble-export tree.
The comparison script regenerates twice, checks the completion marker and compiles the output.
-/

open Lean SP1CleanTest.Core.EnsembleExport

private def exportEnsembleFixture : IO Unit := do
  let out := System.FilePath.mk
    ((← IO.getEnv "ENSEMBLE_EXPORT_OUT").getD ".lake/ensemble-export/manual")
  IO.FS.createDirAll out
  let exported ← match rust with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  IO.FS.writeFile (out / "fixed_membership.rs") exported
  for (name, result) in [
      ("add_instruction.rs", SP1CleanTest.Core.InstructionExport.addRust),
      ("load_byte_instruction.rs", SP1CleanTest.Core.InstructionExport.loadByteRust),
      ("div_rem_instruction.rs", SP1CleanTest.Core.InstructionExport.divRemRust),
      ("mul_instruction.rs", SP1CleanTest.Core.InstructionExport.mulRust),
      ("bitwise_instruction.rs", SP1CleanTest.Core.InstructionExport.bitwiseRust)] do
    let instruction ← match result with
      | .ok value => pure value
      | .error message => throw (IO.userError message)
    IO.FS.writeFile (out / name) instruction
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
