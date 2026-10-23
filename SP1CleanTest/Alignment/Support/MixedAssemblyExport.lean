import SP1CleanTest.Alignment.Support.InstalledAssemblyReference
import SP1CleanTest.Alignment.Support.OrdinaryAssemblyFixture
import SP1CleanTest.Alignment.Support.HintProgramFixture
import SP1CleanTest.Alignment.Support.EnterAssemblyFixture

/-! # Finite mixed-program export instances

Ordinary local cuts, repeated queue observations and constrained ENTER replay use the same
installed inventory and native reference format. Rust independently executes their programs.
-/

namespace SP1CleanTest.Alignment.MixedAssemblyExport

open Lean Circuit SP1Clean InstalledAssembly InstalledAssemblyReference

/-- Independently located finite cuts and host programs, with complete boundary observations. -/
def instances : List (String × Except String (Context × List Seed × SP1PublicIO Fp)) :=
  [("installed_ordinary", OrdinaryAssembly.prepare),
   ("installed_ordinary_prefix", OrdinaryAssembly.prepare 0 2),
   ("installed_ordinary_suffix", OrdinaryAssembly.prepare 2 7),
   ("installed_ordinary_empty", OrdinaryAssembly.prepare 9 0),
   ("installed_hints_empty", HintProgram.prepare 0),
   ("installed_hints_tail", HintProgram.prepare 9),
   ("installed_hints_aligned", HintProgram.prepare 16),
   ("installed_enter", EnterAssembly.prepare)]

/-- Native rows and the full physical ledger; endpoint and terminal mutations must reject. -/
def reference (context : Context) (consumers : List Seed) (header : SP1PublicIO Fp) : IO Json := do
  let input := InstalledAssemblyExport.privateInput context consumers
  let base : fields input.size Fp := ⟨input, rfl⟩
  let some terminal := (InstalledAssemblyExport.hintTables context consumers)[88]?
    | throw (IO.userError "missing bank terminal")
  let changed := Vector.ofFn fun index : Fin input.size =>
    input[index] + if index.val == terminal.offset then 1 else 0
  let cases ← [
      ("honest", header, base, true),
      ("wrong-final-clock", { header with final_clk_0_16 := header.final_clk_0_16 + 1 }, base, false),
      ("changed-terminal-clock", header, changed, false)].mapM
      fun (name, publicInput, privateInput, expected) =>
        installedCase context consumers name publicInput privateInput expected
  return Json.mkObj [("cases", toJson cases), ("inventory", installedInventory context)]

/-- Emit only through Clean's built-in backend and record the checked Lean witness. -/
def write (out : System.FilePath) : IO Unit := do
  for (name, prepared) in instances do
    let (context, consumers, header) ← match prepared with
      | .ok value => pure value
      | .error error => throw (IO.userError s!"{name}: {error}")
    match InstalledAssemblyExport.exportRust context consumers with
    | .ok rust => IO.FS.writeFile (out / s!"{name}.rs") rust
    | .error error => throw (IO.userError s!"{name}: {error}")
    let value ← reference context consumers header
    IO.FS.writeFile (out / s!"{name}.reference.json") value.compress

end SP1CleanTest.Alignment.MixedAssemblyExport
