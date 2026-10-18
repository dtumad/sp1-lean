import SP1CleanTest.Core.EnsembleExport
import SP1CleanTest.Core.SyscallCodeExport
import SP1CleanTest.Core.InstructionExport
import SP1CleanTest.Core.ByteProviderExport
import SP1CleanTest.Core.RangeProviderExport
import SP1CleanTest.Core.SystemExport
import SP1CleanTest.Core.SyscallExport
import SP1CleanTest.Core.HostControlExport
import SP1CleanTest.Core.SnapshotRegisterExport
import SP1CleanTest.Core.StaticProviderExport
import SP1CleanTest.Core.RamExport
import SP1CleanTest.Core.ProgramExport
import SP1CleanTest.Core.HintSourceExport
import SP1CleanTest.Core.WritePermissionExport
import SP1CleanTest.Alignment.Support.InstalledAssemblyExport

/-! # Clean's built-in whole-ensemble Rust export fixture

Generated sources and Lean reference rows stay under the ignored .lake/ensemble-export tree.
The comparison script regenerates twice, checks the completion marker and compiles the output.
-/

open Lean SP1CleanTest.Core.EnsembleExport

private def physicalReference {PublicIO : TypeMap} [ProvableType PublicIO]
    {ensemble : Air.Flat.Ensemble (ZMod SP1Clean.SP1Prime) PublicIO}
    (witness : Air.Flat.EnsembleWitness ensemble) : Json :=
  Json.mkObj [
    ("tables", toJson (witness.tables.map fun table =>
      table.table.map fun row => row.map (·.val))),
    ("interactions", toJson (witness.interactions.map fun interaction => Json.mkObj [
      ("channel", toJson interaction.channel.name),
      ("message", toJson (interaction.msg.map (·.val))),
      ("multiplicity", toJson interaction.mult.val),
      ("assumeGuarantees", toJson interaction.assumeGuarantees)]))]

private def expressionDegree : Expression (ZMod SP1Clean.SP1Prime) → ℕ
  | .var _ => 1
  | .const _ => 0
  | .add left right => max (expressionDegree left) (expressionDegree right)
  | .mul left right => expressionDegree left + expressionDegree right

private def installedCase (consumers : List SP1Clean.Audit.BranchEnsemble.Seed)
    (name : String) (publicInput : SP1Clean.SP1PublicIO (ZMod SP1Clean.SP1Prime))
    (privateInput : fields (SP1CleanTest.Alignment.InstalledAssemblyExport.privateInput consumers).size
      (ZMod SP1Clean.SP1Prime)) (expected : Bool) : IO Json := do
  let fields := [("name", toJson name), ("accepted", toJson expected),
    ("publicInput", toJson ((toElements publicInput).toArray.map (·.val))),
    ("privateInput", toJson (privateInput.toArray.map (·.val)))]
  match SP1CleanTest.Alignment.InstalledAssemblyExport.generate consumers publicInput privateInput with
  | .error message =>
    if expected then throw (IO.userError s!"installed assembly {name}: {message}")
    pure (Json.mkObj (fields ++ [("error", toJson message)]))
  | .ok witness =>
    unless (SP1Clean.Audit.BranchEnsemble.description SP1Clean.Audit.BranchEnsemble.target).checkWitness
        SP1Clean.SP1Prime witness == expected do
      throw (IO.userError s!"unexpected installed assembly acceptance: {name}")
    pure (Json.mkObj (fields ++ [("witness", physicalReference witness)]))

private def installedInventory : Json :=
  toJson (SP1CleanTest.Alignment.InstalledAssemblyExport.installed.tables.map fun component =>
    Json.mkObj [("name", toJson component.circuit.name), ("width", toJson component.width),
      ("fixedWidth", toJson (component.fixedColumns.map (·.width) |>.getD 0)),
      ("fixedHeight", toJson (component.fixedColumns.map (·.height.toNat) |>.getD 0))])

private def installedReference : IO Json := do
  let consumers := SP1Clean.Audit.BranchEnsemble.consumerSeeds
  let input := SP1CleanTest.Alignment.InstalledAssemblyExport.privateInput consumers
  let base : fields input.size (ZMod SP1Clean.SP1Prime) := ⟨input, rfl⟩
  let some branchHint := (SP1CleanTest.Alignment.InstalledAssemblyExport.hintTables consumers)[18]?
    | throw (IO.userError "installed assembly has no branch input")
  let changed := Vector.ofFn fun index : Fin input.size =>
    input[index] + if index.val == branchHint.offset then 1 else 0
  let header := SP1Clean.Audit.BranchEnsemble.header
  let cases ← [
      ("active-branch", header, base, true),
      ("wrong-final-pc", { header with final_pc0 := header.final_pc0 + 4 }, base, false),
      ("changed-branch-input", header, changed, false)].mapM
      fun (name, publicInput, privateInput, expected) =>
        installedCase consumers name publicInput privateInput expected
  return Json.mkObj [("cases", toJson cases), ("inventory", installedInventory),
    ("compilerBranchRow", toJson (SP1Clean.Audit.BranchCompilerRoundTrip.row.map (·.val)))]

private def installedEmptyReference : IO Json := do
  let consumers := SP1CleanTest.Alignment.InstalledAssemblyExport.emptyConsumers
  let input := SP1CleanTest.Alignment.InstalledAssemblyExport.privateInput consumers
  let base : fields input.size (ZMod SP1Clean.SP1Prime) := ⟨input, rfl⟩
  let some terminal := (SP1CleanTest.Alignment.InstalledAssemblyExport.hintTables consumers).find?
      (fun hint => hint.key == (SP1Clean.HostCommitBoundary.terminal (p := SP1Clean.SP1Prime) false).name)
    | throw (IO.userError "installed assembly has no commitment terminal")
  let changed := Vector.ofFn fun index : Fin input.size =>
    input[index] + if index.val == terminal.offset then 1 else 0
  let header := SP1CleanTest.Alignment.InstalledAssemblyExport.emptyHeader
  let cases ← [
      ("empty-local", header, base, true),
      ("wrong-initial-clock", { header with init_clk_0_16 := header.init_clk_0_16 + 1 }, base, false),
      ("wrong-final-clock", { header with final_clk_0_16 := header.final_clk_0_16 + 1 }, base, false),
      ("wrong-final-pc", { header with final_pc0 := header.final_pc0 + 4 }, base, false),
      ("nonzero-exit", { header with exit_code := 1 }, base, false),
      ("changed-bank-terminal", header, changed, false)].mapM
      fun (name, publicInput, privateInput, expected) =>
        installedCase consumers name publicInput privateInput expected
  return Json.mkObj [("cases", toJson cases), ("inventory", installedInventory)]

private def programReference (image : SP1Clean.Model.Core.ProgramImage) {n : ℕ}
    (requests : SP1CleanTest.Core.ProgramExport.Requests n (ZMod SP1Clean.SP1Prime)) : IO Json := do
  match SP1CleanTest.Core.ProgramExport.generate image requests with
  | .error message => throw (IO.userError message)
  | .ok witness =>
    unless (SP1CleanTest.Core.ProgramExport.description image n).checkWitness SP1Clean.SP1Prime witness do
      throw (IO.userError "fixed Program witness failed raw acceptance")
    return Json.mkObj [("publicInput", toJson ((toElements requests).toList.map (·.val))),
      ("witness", physicalReference witness)]

private def componentMetrics (component : Air.Flat.Component (ZMod SP1Clean.SP1Prime)) : Json :=
  let constraints := component.rowOperations.constraints
  Json.mkObj [("name", toJson component.circuit.name), ("width", toJson component.width),
    ("constraints", toJson constraints.length),
    ("degreeBound", toJson ((constraints.map expressionDegree).foldl max 0))]

private def permissionReference (rom : SP1Clean.Model.Core.ProgramImage) (empty : Bool) : IO Json := do
  let cases ← SP1CleanTest.Core.WritePermissionExport.cases.mapM fun (name, requests, expected) => do
    let expected := if empty then requests.toList.all (fun address =>
      address.toList.all (fun limb => limb.val < 65536)) else expected
    let fields := [("name", toJson name), ("publicInput", toJson ((toElements requests).toList.map (·.val))),
      ("accepted", toJson expected)]
    match SP1CleanTest.Core.WritePermissionExport.generate rom requests with
    | .error message =>
      if expected then throw (IO.userError s!"permission {name}: {message}")
      pure (Json.mkObj (fields ++ [("error", toJson message)]))
    | .ok witness =>
      unless (SP1CleanTest.Core.WritePermissionExport.description rom).checkWitness SP1Clean.SP1Prime witness == expected do
        throw (IO.userError s!"unexpected permission acceptance: {name}")
      pure (Json.mkObj (fields ++ [("witness", physicalReference witness)]))
  return toJson cases

private def hintCases {Row : TypeMap} [ProvableType Row]
    (samples : List (Row (ZMod SP1Clean.SP1Prime))) :
    List (String × List (Row (ZMod SP1Clean.SP1Prime)) × Bool) :=
  let zero := fromElements (Vector.replicate (size Row) 0)
  let first := samples.headD zero
  samples.zipIdx.map (fun (record, index) => (s!"record-{index}", [record, record], true)) ++
    [("mixed", [first, samples.getLastD zero], true)] ++
    (List.finRange (size Row)).map (fun (index : Fin (size Row)) =>
      let changed := fromElements ((toElements first).set index.val ((toElements first)[index] + 1))
      (s!"forged-{index.val}", [first, changed], false)) ++ [("padding", [zero, zero], false)]

private def hintReference {Row : TypeMap} [ProvableType Row]
    (source : SP1CleanTest.Core.HintSourceExport.Source Row)
    (cases : List (String × List (Row (ZMod SP1Clean.SP1Prime)) × Bool)) : IO Json := do
  let results ← cases.mapM fun (name, requests, expected) => do
    let fields := [("name", toJson name),
      ("publicInput", toJson (requests.flatMap fun row => (toElements row).toList.map (·.val))),
      ("accepted", toJson expected)]
    match SP1CleanTest.Core.HintSourceExport.generate source requests with
    | .error message =>
      if expected then throw (IO.userError s!"hint {name}: {message}")
      pure (Json.mkObj (fields ++ [("error", toJson message)]))
    | .ok witness =>
      unless (SP1CleanTest.Core.HintSourceExport.description source requests.length).checkWitness
          SP1Clean.SP1Prime witness == expected do
        throw (IO.userError s!"unexpected hint acceptance: {name}")
      pure (Json.mkObj (fields ++ [("witness", physicalReference witness)]))
  return toJson results

private def hintReferences : IO Json := do
  let hints := SP1CleanTest.Core.HintSourceExport.hints
  let nodes := SP1Clean.Model.Core.HintQueue.sourceRows (p := SP1Clean.SP1Prime) hints
  let words := SP1Clean.Model.Core.HintQueue.sourceWordRows (p := SP1Clean.SP1Prime) hints
  let nodeCases := hintCases nodes
  let wordCases := hintCases words
  return Json.mkObj [
    ("nodes", ← hintReference (SP1CleanTest.Core.HintSourceExport.nodes hints) nodeCases),
    ("words", ← hintReference (SP1CleanTest.Core.HintSourceExport.words hints) wordCases),
    ("nodes_empty", ← hintReference (SP1CleanTest.Core.HintSourceExport.nodes [])
      (nodeCases.map fun (name, rows, _) => (name, rows, false))),
    ("words_empty", ← hintReference (SP1CleanTest.Core.HintSourceExport.words [])
      (wordCases.map fun (name, rows, _) => (name, rows, false))),
    ("nodes_unused", ← hintReference (SP1CleanTest.Core.HintSourceExport.nodes hints) [("unused", [], true)]),
    ("words_unused", ← hintReference (SP1CleanTest.Core.HintSourceExport.words hints) [("unused", [], true)])]

private def exportEnsembleFixture : IO Unit := do
  let out := System.FilePath.mk
    ((← IO.getEnv "ENSEMBLE_EXPORT_OUT").getD ".lake/ensemble-export/manual")
  IO.FS.createDirAll out
  let opcodes := SP1Clean.Soundness.Opcode.all.map fun opcode => Json.mkObj [
    ("constructor", toJson (reprStr opcode)), ("discriminant", toJson opcode.toNat)]
  IO.FS.writeFile (out / "opcodes.reference.json") ((toJson opcodes).compress ++ "\n")
  for (name, consumers) in [
      ("installed_assembly", SP1Clean.Audit.BranchEnsemble.consumerSeeds),
      ("installed_empty", SP1CleanTest.Alignment.InstalledAssemblyExport.emptyConsumers)] do
    let installed ← match SP1CleanTest.Alignment.InstalledAssemblyExport.exportRust consumers with
      | .ok value => pure value
      | .error message => throw (IO.userError message)
    IO.FS.writeFile (out / (name ++ ".rs")) installed
  IO.FS.writeFile (out / "installed_assembly.reference.json") ((← installedReference).compress ++ "\n")
  IO.FS.writeFile (out / "installed_empty.reference.json") ((← installedEmptyReference).compress ++ "\n")
  let exported ← match rust with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  IO.FS.writeFile (out / "fixed_membership.rs") exported
  IO.FS.writeFile (out / "syscall_code_guard.reference.json")
    ((Json.mkObj [("cases", SP1CleanTest.Core.SyscallCodeExport.reference),
      ("metrics", componentMetrics SP1CleanTest.Core.SyscallCodeExport.component)]).compress ++ "\n")
  for (name, result) in SP1CleanTest.Core.InstructionExport.rustExports ++
      SP1CleanTest.Core.ByteProviderExport.rustExports ++
      SP1CleanTest.Core.RangeProviderExport.rustExports ++
      SP1CleanTest.Core.SystemExport.rustExports ++
      SP1CleanTest.Core.SyscallExport.rustExports ++
      SP1CleanTest.Core.HostControlExport.rustExports ++
      SP1CleanTest.Core.SyscallCodeExport.rustExports ++
      SP1CleanTest.Core.ProgramExport.rustExports ++
      SP1CleanTest.Core.WritePermissionExport.rustExports ++
      SP1CleanTest.Core.HintSourceExport.rustExports ++
      SP1CleanTest.Core.SnapshotRegisterExport.rustExports ++
      SP1CleanTest.Core.SnapshotRegisterExport.Target.rustExports ++
      SP1CleanTest.Core.StaticProviderExport.rustExports ++
      SP1CleanTest.Core.RamExport.rustExports do
    let source ← match result with
      | .ok value => pure value
      | .error message => throw (IO.userError message)
    IO.FS.writeFile (out / name) source
  IO.FS.writeFile (out / "host_control.reference.json")
    (SP1CleanTest.Core.HostControlExport.reference.compress ++ "\n")
  let hints ← match SP1CleanTest.Core.HostControlExport.hintReference with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  IO.FS.writeFile (out / "host_hints.reference.json") (hints.compress ++ "\n")
  let programActive ← programReference SP1CleanTest.Core.ProgramExport.image
    SP1CleanTest.Core.ProgramExport.requests
  let programUnused ← programReference SP1CleanTest.Core.ProgramExport.image #v[]
  let programEmpty ← programReference SP1CleanTest.Core.ProgramExport.emptyImage #v[]
  let programSparse ← programReference SP1CleanTest.Core.ProgramExport.sparseImage
    SP1CleanTest.Core.ProgramExport.sparseRequests
  IO.FS.writeFile (out / "program_fixed.reference.json")
    ((Json.mkObj [("active", programActive), ("unused", programUnused), ("empty", programEmpty),
      ("sparse", programSparse)]).compress ++ "\n")
  IO.FS.writeFile (out / "hint_sources.reference.json") ((← hintReferences).compress ++ "\n")
  let permissions ← permissionReference SP1CleanTest.Core.WritePermissionExport.image false
  let emptyPermissions ← permissionReference SP1CleanTest.Core.WritePermissionExport.emptyImage true
  IO.FS.writeFile (out / "write_permission.reference.json")
    ((Json.mkObj [("rom", permissions), ("empty", emptyPermissions)]).compress ++ "\n")
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
  let registerCases ← SP1CleanTest.Core.SnapshotRegisterExport.cases.mapM
      fun (name, requests, expected) => do
    let fields := [("name", toJson name),
      ("publicInput", toJson ((toElements requests).toArray.map (·.val))),
      ("accepted", toJson expected)]
    match SP1CleanTest.Core.SnapshotRegisterExport.generate requests with
    | .error message =>
      if expected then throw (IO.userError s!"{name}: {message}")
      pure <| Json.mkObj (fields ++ [("error", toJson message)])
    | .ok witness =>
      unless expected && SP1CleanTest.Core.SnapshotRegisterExport.description.checkWitness
          SP1Clean.SP1Prime witness do
        throw (IO.userError s!"unexpected source-register acceptance: {name}")
      pure <| Json.mkObj (fields ++ [("witness", physicalReference witness)])
  let empty ← match SP1CleanTest.Core.SnapshotRegisterExport.generateEmpty with
    | .error message => throw (IO.userError message)
    | .ok witness =>
      unless SP1CleanTest.Core.SnapshotRegisterExport.emptyDescription.checkWitness
          SP1Clean.SP1Prime witness do
        throw (IO.userError "unused fixed provider failed raw acceptance")
      pure (physicalReference witness)
  IO.FS.writeFile (out / "snapshot_registers.reference.json")
    ((Json.mkObj [("cases", toJson registerCases), ("empty", empty)]).compress ++ "\n")
  let targetCases ← SP1CleanTest.Core.SnapshotRegisterExport.Target.cases.mapM
      fun (name, requests, expected) => do
    let fields := [("name", toJson name),
      ("publicInput", toJson ((toElements requests).toArray.map (·.val))),
      ("accepted", toJson expected)]
    match SP1CleanTest.Core.SnapshotRegisterExport.Target.generate requests with
    | .error message =>
      if expected then throw (IO.userError s!"{name}: {message}")
      pure <| Json.mkObj (fields ++ [("error", toJson message)])
    | .ok witness =>
      unless SP1CleanTest.Core.SnapshotRegisterExport.Target.description.checkWitness
          SP1Clean.SP1Prime witness == expected do
        throw (IO.userError s!"unexpected target-register acceptance: {name}")
      pure <| Json.mkObj (fields ++ [("witness", physicalReference witness)])
  let targetEmpty ← match SP1CleanTest.Core.SnapshotRegisterExport.Target.generateEmpty with
    | .error message => throw (IO.userError message)
    | .ok witness =>
      unless SP1CleanTest.Core.SnapshotRegisterExport.Target.emptyDescription.checkWitness
          SP1Clean.SP1Prime witness do
        throw (IO.userError "unused target provider failed raw acceptance")
      pure (physicalReference witness)
  IO.FS.writeFile (out / "target_registers.reference.json")
    ((Json.mkObj [("cases", toJson targetCases), ("empty", targetEmpty)]).compress ++ "\n")
  let staticFixtures ← SP1CleanTest.Core.StaticProviderExport.fixtures.mapM fun fixture => do
    let name := fixture.name
    let rows := fixture.rows
    let cases ← SP1CleanTest.Core.StaticProviderExport.requests.mapM fun request => do
      let expected := rows.contains request[0] && rows.contains request[1]
      let fields := [("publicInput", toJson ((toElements request).toArray.map (·.val))),
        ("accepted", toJson expected)]
      match SP1CleanTest.Core.StaticProviderExport.generate fixture request with
      | .error message =>
        if expected then throw (IO.userError s!"{name}: {message}")
        pure <| Json.mkObj (fields ++ [("error", toJson message)])
      | .ok witness =>
        unless expected && (SP1CleanTest.Core.StaticProviderExport.description fixture).checkWitness
            SP1Clean.SP1Prime witness do
          throw (IO.userError s!"unexpected padded membership acceptance: {name}")
        pure <| Json.mkObj (fields ++ [("witness", physicalReference witness)])
    let unused ← match SP1CleanTest.Core.StaticProviderExport.generateEmpty fixture with
      | .error message => throw (IO.userError s!"{name}: {message}")
      | .ok witness =>
        unless (SP1CleanTest.Core.StaticProviderExport.emptyDescription fixture).checkWitness
            SP1Clean.SP1Prime witness do
          throw (IO.userError s!"unused padded provider failed: {name}")
        pure (physicalReference witness)
    pure <| Json.mkObj [("name", toJson name), ("cases", toJson cases), ("unused", unused)]
  IO.FS.writeFile (out / "static_membership.reference.json") ((toJson staticFixtures).compress ++ "\n")
  let ramFixtures ← ["sp1.native.initial_memory", "sp1.native.target_memory"].mapM fun name => do
    let cases ← SP1CleanTest.Core.RamExport.cases.mapM fun (label, requests, expected) => do
      let fields := [("name", toJson label),
        ("publicInput", toJson ((toElements requests).toArray.map (·.val))),
        ("accepted", toJson expected)]
      match SP1CleanTest.Core.RamExport.generate name requests with
      | .error message =>
        if expected then throw (IO.userError s!"{label}: {message}")
        pure <| Json.mkObj (fields ++ [("error", toJson message)])
      | .ok witness =>
        unless expected && (SP1CleanTest.Core.RamExport.description name).checkWitness
            SP1Clean.SP1Prime witness do
          throw (IO.userError s!"unexpected RAM membership acceptance: {label}")
        pure <| Json.mkObj (fields ++ [("witness", physicalReference witness)])
    pure (name, toJson cases)
  IO.FS.writeFile (out / "ram_membership.reference.json") ((Json.mkObj ramFixtures).compress ++ "\n")
  let ramRows := SP1CleanTest.Core.RamExport.rowCases.map fun (name, component, inputs) =>
    (name, toJson (inputs.map fun cells =>
      let input := fromElements (Vector.ofFn fun index => cells[index.val]?.getD 0)
      let row := component.buildRow input (fun _ _ => #[]) (ProverHint.empty _)
      let env := Environment.fromArray row (fun _ _ => #[])
      Json.mkObj [("input", toJson (cells.map (·.val))), ("row", toJson (row.map (·.val))),
        ("interactions", toJson (component.rowOperations.interactionValues env |>.map fun entry =>
          Json.mkObj [("channel", toJson entry.channel.name),
            ("message", toJson (entry.msg.map (·.val))),
            ("multiplicity", toJson entry.mult.val), ("assumeGuarantees", toJson entry.assumeGuarantees)]))]))
  IO.FS.writeFile (out / "ram_rows.reference.json") ((Json.mkObj ramRows).compress ++ "\n")
  IO.println "EXPORTED ensemble Rust and Lean reference cases"

#eval exportEnsembleFixture
