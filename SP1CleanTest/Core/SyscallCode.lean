import SP1Clean.Proofs.Chips.CoreSyscallChip.Formal
import SP1Clean.Model.SP1Field
import Clean.Circuit.WitnessExport

/-! # Native syscall guard regressions

Check the production guard's generated witnesses and arithmetic constraints. The whole-chip
suffix test also checks that the guard reads the prior x5 word, including every upper limb.
These local checks make no claim about host effects or whole-ensemble balance.
-/

namespace SP1CleanTest.Core.SyscallCode

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core

private abbrev Fp := ZMod SP1Prime

private def accepts (input : SyscallCodeGuard.Inputs Fp) : Bool :=
  let program := SyscallCodeGuard.main (varFromOffset SyscallCodeGuard.Inputs 0)
  let env := (program.proverEnvironment (ProverHint.empty Fp) (toElements input).toList).toEnvironment
  (program.operations (size SyscallCodeGuard.Inputs)).toFlat.all fun operation =>
    match operation with
    | .assert expression => env expression == 0
    | .lookup _ => false
    | .witness .. | .interact .. => true

/-- Every supported full code is accepted; selection is independent of witness-supplied tables. -/
theorem supportedCodes :
    SyscallKind.all.all (fun kind => accepts ⟨kind.encode, 1⟩) = true := by native_decide

/-- Unsupported low codes, dispatched-to-core codes, upper-limb aliases, and nonboolean gates fail. -/
theorem rejectedCodes :
    ([1, 4, 5, 0x01010005, 0x100000002, 0x100000003, 0x1000000f1, 0x100000000000002] :
      List (BitVec 64)).all (fun code => !accepts ⟨Soundness.Target.bitVecToWord code, 1⟩) = true ∧
    accepts ⟨#v[2, 0, 0, 0], 2⟩ = false ∧
    accepts ⟨#v[2, 65536, 0, 0], 1⟩ = false := by native_decide

/-- Padding imposes no code bound, but still checks that its gate is boolean. -/
theorem padding : accepts ⟨#v[65536, 91, 123, 90000], 0⟩ = true := by native_decide

private def chipGuardAccepts (code : Word Fp) : Bool :=
  let input : SyscallInstrsChip.Inputs Fp :=
    { (fromElements (Vector.replicate (size SyscallInstrsChip.Inputs) 0)) with
      op_a_memory := ⟨code, ⟨0, 0⟩⟩, is_real := 1 }
  let vars := varFromOffset SyscallInstrsChip.Inputs 0
  let program := CoreSyscallChip.circuit.main vars
  let env := (program.proverEnvironment (ProverHint.empty Fp) (toElements input).toList).toEnvironment
  let ops := program.operations (size SyscallInstrsChip.Inputs)
  let original := (SyscallInstrsChip.circuit.main vars).operations (size SyscallInstrsChip.Inputs)
  let guard := ops.constraints.drop original.constraints.length
  ops.lookups.isEmpty && guard.length == 11 && guard.all (fun expression => env expression == 0)

/-- The composed guard reads all four limbs of the prior x5 value. Synthetic rows test this
suffix only, independently of the original instruction constraints. -/
theorem chipProfileWiring :
    SyscallKind.all.all (fun kind => chipGuardAccepts kind.encode) = true ∧
    chipGuardAccepts #v[3, 0, 1, 0] = false ∧
    chipGuardAccepts #v[4, 0, 0, 0] = false := by native_decide

/-- info: exportable ✓ (6 witness cells) -/
#guard_msgs in
#assert_exportable (SyscallCodeGuard.circuit (p := SP1Prime))

/-- info: exportable ✓ (6 witness cells) -/
#guard_msgs in
#assert_exportable (CoreSyscallChip.circuit (p := SP1Prime))

end SP1CleanTest.Core.SyscallCode
