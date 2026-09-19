import SP1CleanTest.Core.EnsembleExport

/-! # Whole-ensemble export regression fixture

Sole writer of `export/ensemble/`. The optional `ENSEMBLE_EXPORT_OUT` selects a scratch directory
for the byte-identity check. Requires built test oleans; invoked by `check_ensemble_export.sh`.
-/

private def exportEnsembleFixture : IO Unit := do
  let out := System.FilePath.mk ((← IO.getEnv "ENSEMBLE_EXPORT_OUT").getD "export/ensemble")
  IO.FS.createDirAll out
  let exported ← match SP1CleanTest.Core.EnsembleExport.instanceJson with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  IO.FS.writeFile (out / "lookup.instance.json") (exported.compress ++ "\n")
  let trace (value : ℕ) := Lean.Json.mkObj [
    ("version", Lean.toJson (1 : ℕ)),
    ("publicInput", Lean.toJson [value]),
    ("tables", Lean.toJson [[[value]]])]
  IO.FS.writeFile (out / "lookup.valid.json") ((trace 7).compress ++ "\n")
  IO.FS.writeFile (out / "lookup.forged.json") ((trace 8).compress ++ "\n")

#eval exportEnsembleFixture
