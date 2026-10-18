import SP1CleanTest.Core.ComponentExport
import SP1Clean.Proofs.Chips.HostCommitChip.Populate
import SP1Clean.Proofs.Chips.HostHaltChip.Formal
import SP1Clean.Proofs.Chips.HostEnterChip.Formal
import SP1Clean.Native.Operations.HostCommitBoundary
import ToClean.Air.TableBuild

/-! # Built-in exports of native control and commitment handlers

These are the installed production components, with their complete declared channels. Rust
compares active effects against released execution and retains the separate per-call receipt
and shard-public contracts. Component rows have no inactive flag; zero rows are not padding.
-/

namespace SP1CleanTest.Core.HostControlExport

open Circuit Air.Flat SP1Clean ComponentExport

private def description {Input : TypeMap} [ProvableType Input]
    (circuit : GeneralFormalCircuit Fp Input unit) : Ensemble Fp unit :=
  { ensemble { circuit, Assumptions := circuit.Assumptions } with channels := circuit.channels }

private def exportCircuit {Input : TypeMap} [ProvableType Input]
    (circuit : GeneralFormalCircuit Fp Input unit) : Except String String :=
  Backends.Plonky3.Print.ensembleToRust (fixture (description circuit) Input)
    (config { circuit, Assumptions := circuit.Assumptions })

private def commitName (deferred : Bool) (slot : Fin 8) : String :=
  s!"host_{if deferred then "deferred" else "commit"}_{slot.val}"

/-- HALT, ENTER, sixteen routed bank updates and the two bank terminals. -/
def rustExports : List (String × Except String String) :=
  [("host_halt.rs", exportCircuit HostHaltChip.circuit),
   ("host_enter.rs", exportCircuit HostEnterChip.circuit)] ++
  [false, true].flatMap (fun deferred =>
    (List.finRange 8).map fun slot =>
      (s!"{commitName deferred slot}.rs", exportCircuit (HostCommitChip.circuit deferred slot))) ++
  [("host_commit_terminal.rs", exportCircuit (HostCommitBoundary.terminal false)),
   ("host_deferred_terminal.rs", exportCircuit (HostCommitBoundary.terminal true))]

private def word (value : ℕ) : Word Fp := Soundness.Target.bitVecToWord (BitVec.ofNat 64 value)

private def call (code arg1 arg2 result : ℕ) : HostCallChip.Message Fp :=
  ⟨0, 265, word code, word arg1, word arg2, word result, 0⟩

private def previous : HostCommitChip.State Fp :=
  ⟨0, 1, Vector.ofFn fun i : Fin 8 => word (100 + i.val)⟩

private def rowReference {Input : TypeMap} [ProvableType Input]
    (name : String) (circuit : GeneralFormalCircuit Fp Input unit) (input : Input Fp) : Lean.Json :=
  let component : Component Fp := { circuit, Assumptions := circuit.Assumptions }
  let data : ProverData Fp := fun _ _ => #[]
  let row := component.buildRow input data (ProverHint.empty Fp)
  let interactions := component.rowOperations.interactionValues (Environment.fromArray row data)
  Lean.Json.mkObj [("name", Lean.toJson name),
    ("input", Lean.toJson ((toElements input).toArray.map (·.val))),
    ("row", Lean.toJson (row.map (·.val))),
    ("ledger", Lean.toJson (interactions.map fun interaction =>
      Lean.Json.arr #[Lean.toJson interaction.channel.name, Lean.toJson interaction.mult.val,
        Lean.toJson (interaction.msg.toList.map (·.val))]))]

/-- Lean constructor references authenticate the Rust field adapter and every physical occurrence. -/
def reference : Lean.Json := Lean.toJson (
  [rowReference "host_halt" HostHaltChip.circuit
      (HostHaltChip.populate (call 0 (SP1Prime - 1) (2 ^ 64 - 1) 0)),
   rowReference "host_enter" HostEnterChip.circuit (call 3 (2 ^ 64 - 1) 0 0)] ++
  [false, true].flatMap (fun deferred => (List.finRange 8).map fun slot =>
    let code := if deferred then 26 else 16
    rowReference (commitName deferred slot) (HostCommitChip.circuit deferred slot)
      (HostCommitChip.populate deferred (call code slot.val 131075 code) previous)) ++
  [rowReference "host_commit_terminal" (HostCommitBoundary.terminal false) previous,
   rowReference "host_deferred_terminal" (HostCommitBoundary.terminal true) previous])

end SP1CleanTest.Core.HostControlExport
