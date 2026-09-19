import SP1Clean.Native.Operations.InitialMemoryRead
import SP1CleanTest.Core.InitialMemoryLookup

/-! # Whole-word initial-memory AIR regressions

The checked words cross sparse-image gaps and a 16-bit address-limb boundary. Invalid byte-row
routing is tested against the actual flattened addition constraints, even though each byte row
individually authenticates a real initial-memory byte.
-/

namespace SP1CleanTest.Core.InitialMemoryRead

open Circuit SP1Clean.Model.Core SP1Clean.InitialMemoryRead

private abbrev Fp := ZMod SP1Clean.SP1Prime

private def memory : ByteMemory := ⟨[(7, 42), (0, 13), (65535, 255), (65536, 17)]⟩

/-- info: exportable ✓ (512 witness cells) -/
#guard_msgs in
#assert_exportable (circuit (p := SP1Clean.SP1Prime) memory)

private def evaluate (input : Inputs Fp) : Bool × BitVec 64 :=
  let program := main memory (varFromOffset Inputs 0)
  let env := (program.proverEnvironment (ProverHint.empty Fp) (toElements input).toList).toEnvironment
  (InitialMemoryLookup.localConstraints memory (2 ^ 48) env (program.operations (size Inputs)).toFlat,
    SP1Clean.Word.toBitVec64 (ProvableType.eval env (program.output (size Inputs))))

/-- The circuit-generated words pass the AIR checks and equal the independently defined memory read. -/
theorem constructedWordRows : [0, 1, 7, 65532, 2 ^ 48 - 8].all (fun address =>
    evaluate (populate memory address) == (true, memory.readWord address)) = true := by
  native_decide

/-- Reusing a valid byte at the wrong position fails the circuit's address-link constraints. -/
theorem rejectsWrongOffset :
    (evaluate ⟨(populate (p := SP1Clean.SP1Prime) memory 0).bytes.set 1
      (populate memory 0).bytes[0]⟩).1 = false := by
  native_decide

example : [2 ^ 48 - 8, 2 ^ 48 - 7, 2 ^ 48].map (fun address =>
    (populate? (p := SP1Clean.SP1Prime) memory address).isSome) = [true, false, false] := by
  native_decide

end SP1CleanTest.Core.InitialMemoryRead
