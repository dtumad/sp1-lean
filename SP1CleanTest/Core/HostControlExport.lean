import SP1CleanTest.Core.ComponentExport
import SP1Clean.Semantics.ReleasePolicy
import SP1Clean.Proofs.Chips.HostCommitChip.Populate
import SP1Clean.Proofs.Chips.HostHaltChip.Formal
import SP1Clean.Proofs.Chips.HostEnterChip.Formal
import SP1Clean.Proofs.Chips.HostHintLengthChip.Populate
import SP1Clean.Proofs.Chips.HostHintReadChip.Populate
import SP1Clean.Native.Operations.HostCommitBoundary
import ToClean.Air.TableBuild

/-! # Built-in exports of native control, commitment and hint handlers

These are the installed production components, with their complete declared channels. Rust
compares active effects against released execution and retains the separate per-call receipt
and shard-public contracts. Commitment rows have Boolean activity for padding; terminals
and the other control handlers remain actual events.
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

/-- HALT, ENTER, sixteen bank updates, two terminals and three hint handlers. -/
def rustExports : List (String × Except String String) :=
  [("host_halt.rs", exportCircuit HostHaltChip.circuit),
   ("host_enter.rs", exportCircuit HostEnterChip.circuit)] ++
  [false, true].flatMap (fun deferred =>
    (List.finRange 8).map fun slot =>
      (s!"{commitName deferred slot}.rs", exportCircuit (HostCommitChip.circuit deferred slot))) ++
  [("host_commit_terminal.rs", exportCircuit (HostCommitBoundary.terminal false)),
   ("host_deferred_terminal.rs", exportCircuit (HostCommitBoundary.terminal true)),
   ("host_hint_length_empty.rs", exportCircuit (HostHintLengthChip.circuit true)),
   ("host_hint_length.rs", exportCircuit (HostHintLengthChip.circuit false)),
   ("host_hint_read.rs", exportCircuit HostHintReadChip.circuit)]

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
def reference : Lean.Json := Lean.Json.mkObj [("rows", Lean.toJson (
  [rowReference "host_halt" HostHaltChip.circuit
      (HostHaltChip.populate (call 0 (SP1Prime - 1) (2 ^ 64 - 1) 0)),
   rowReference "host_enter" HostEnterChip.circuit (call 3 (2 ^ 64 - 1) 0 0)] ++
  [false, true].flatMap (fun deferred => (List.finRange 8).map fun slot =>
    let code := if deferred then 26 else 16
    rowReference (commitName deferred slot) (HostCommitChip.circuit deferred slot)
      (HostCommitChip.populate deferred (call code slot.val 131075 code) previous, 1)) ++
  [rowReference "host_commit_terminal" (HostCommitBoundary.terminal false) previous,
   rowReference "host_deferred_terminal" (HostCommitBoundary.terminal true) previous])),
  ("releaseExitPolicy", Lean.toJson ([0, 1, 2, 3, 65536, SP1Prime - 1, 2 ^ 32 - 1].map
    fun code : ℕ => Lean.Json.mkObj [("code", Lean.toJson code),
      ("accepted", Lean.toJson (Semantics.ReleasePolicy.acceptsExit (BitVec.ofNat 32 code)))]))]

private def hintExecution (hints : List Model.Core.Bytes) (kind : Model.Core.SyscallKind)
    (arg1 arg2 : ℕ) : Except String Model.Core.HostExecution :=
  let host : Model.Core.HostState := { io := { hints } }
  let context : Model.Core.HostReadContext := {
    register := fun index =>
      if index = 5 then some kind.code
      else if index = 10 then some (BitVec.ofNat 64 arg1)
      else if index = 11 then some (BitVec.ofNat 64 arg2)
      else none
    byte := fun _ => none }
  match host.run ⟨{ readOnly := fun _ => false }, SP1Prime⟩ context with
  | some executed => .ok executed
  | none => .error "native hint reference execution failed"

/-- Constructor rows from native execution include empty queues, empty hints and limb carries. -/
def hintReference : Except String Lean.Json := do
  let empty ← hintExecution [] .hintLength (2 ^ 64 - 1) 17
  let initial := rowReference "host_hint_length_empty" (HostHintLengthChip.circuit true)
    (HostHintLengthChip.populate #[] 0 1 265 empty)
  let cases ← [0, 1, 7, 8, 9, 16, 17, 65535, 65536].mapM fun length => do
    let bytes : Model.Core.Bytes := (List.range length).map fun index => BitVec.ofNat 8 (19 * index + 3)
    let hints := [bytes, [BitVec.ofNat 8 99]]
    let store := Model.Core.HintQueue.ofList hints
    let address := if length % 2 = 0 then 131072 else 131064
    let observe ← hintExecution hints .hintLength (2 ^ 64 - 1) 17
    let read ← hintExecution hints .hintRead address length
    pure [rowReference "host_hint_length" (HostHintLengthChip.circuit false)
        (HostHintLengthChip.populate store.1 store.2 1 265 observe),
      rowReference "host_hint_read" HostHintReadChip.circuit
        (HostHintReadChip.populate store.1 store.2 1 265 read)]
  return Lean.toJson (initial :: cases.flatten)

end SP1CleanTest.Core.HostControlExport
