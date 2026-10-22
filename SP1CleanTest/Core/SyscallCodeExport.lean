import SP1Clean.Native.Operations.SyscallCodeGuard
import SP1CleanTest.Core.ComponentExport
import ToClean.Air.TableBuild

/-! # Built-in Rust export of the native syscall guard

Clean generates the six shared products in both languages. The Rust comparison independently
selects the eight supported calls from SP1's pinned enum, exhausts the low 16-bit code space and
checks upper-limb aliases, padding and witness tampering. This checks the native profile, not the
separate host effects or SP1's more permissive truncation of the syscall register.
-/

namespace SP1CleanTest.Core.SyscallCodeExport

open Circuit Air.Flat SP1Clean ComponentExport

/-- Wrap the production assertion without changing its implementation or semantic contract. -/
def circuit : GeneralFormalCircuit Fp SyscallCodeGuard.Inputs unit where
  name := "sp1.native.syscall_code.guard"
  main input := do assertion SyscallCodeGuard.circuit input
  Spec input _ _ := SyscallCodeGuard.Spec input
  ProverAssumptions input _ _ := SyscallCodeGuard.Spec input
  soundness := by
    circuit_proof_start [SyscallCodeGuard.circuit]
    exact h_holds
  completeness := by
    circuit_proof_start [SyscallCodeGuard.circuit]
    exact h_assumptions

def component : Component Fp := { circuit, Assumptions := circuit.Assumptions }

def rustExports : List (String × Except String String) :=
  [("syscall_code_guard.rs", exportRust circuit)]

/-- Cross-language row references include real calls, rejected values and unrestricted padding. -/
def cases : List (String × SyscallCodeGuard.Inputs Fp × Bool) :=
  (Model.Core.SyscallKind.all.map fun kind =>
    (toString kind.code.toNat, ⟨kind.encode, 1⟩, true)) ++
  [("padding", ⟨#v[65536, 91, 123, 90000], 0⟩, true),
   ("unsupported", ⟨#v[4, 0, 0, 0], 1⟩, false),
   ("upper_alias", ⟨#v[2, 0, 1, 0], 1⟩, false),
   ("nonboolean", ⟨#v[2, 0, 0, 0], 2⟩, false)]

/-- Reference rows use the production component and Clean's ordinary witness interpreter. -/
def reference : Lean.Json :=
  Lean.toJson (cases.map fun (name, input, expected) =>
    let row := component.buildRow input (fun _ _ => #[]) (ProverHint.empty Fp)
    Lean.Json.mkObj [("name", Lean.toJson name),
      ("input", Lean.toJson ((toElements input).toArray.map (fun (value : Fp) => value.val))),
      ("row", Lean.toJson (row.map (fun (value : Fp) => value.val))), ("accepted", Lean.toJson expected)])

/-- Both the arithmetic AIR and witness program lower through the pinned upstream exporter. -/
theorem export_succeeds : (exportRust circuit).isOk = true := by native_decide

end SP1CleanTest.Core.SyscallCodeExport
