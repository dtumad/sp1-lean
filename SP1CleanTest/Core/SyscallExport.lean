import SP1CleanTest.Core.ComponentExport
import SP1Clean.Proofs.Chips.HostCallChip.Formal

/-! # Built-in export of the syscall instruction and installed host handoff

The base row is compared with released SP1's supervisor-mode AIR in Rust. Public values use
native Exit/PublicValues messages; the comparison checks their bindings separately from the
shared buses. The core guard and host handoff add the native eight-call profile and WRITE's x12
read. Exporting these components does not establish the separate host handlers' effects.
-/

namespace SP1CleanTest.Core.SyscallExport

open Air.Flat SP1Clean ComponentExport

private def exportCircuit {Input : TypeMap} [ProvableType Input]
    (circuit : GeneralFormalCircuit Fp Input unit) : Except String String :=
  exportRust circuit

/-- The original instruction, its full-code profile, and the installed instruction-to-host row. -/
def rustExports : List (String × Except String String) := [
  ("syscall_instruction.rs", exportCircuit SyscallInstrsChip.circuit),
  ("core_syscall.rs", exportCircuit CoreSyscallChip.circuit),
  ("host_call.rs", exportCircuit HostCallChip.circuit)]

end SP1CleanTest.Core.SyscallExport
