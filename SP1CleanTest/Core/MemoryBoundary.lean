import SP1Clean.Proofs.Chips.OrderedInitialProvider
import SP1CleanTest.Core.InitialMemoryLookup

/-! # Initial-record and ordered-key AIR regressions

These checks execute the actual witness programs, evaluate every assertion and initial-image
lookup, and validate every nonzero Byte interaction against the byte-op semantics. Memory and
ordering interactions are retained for the separate whole-ensemble balance argument.
-/

namespace SP1CleanTest.Core.MemoryBoundary

open Circuit SP1Clean SP1Clean.Model.Core SP1Clean.Soundness.Target

private abbrev Fp := ZMod SP1Prime

private def image : ProgramImage :=
  ⟨[(65536, 0x00000013)], 65536, [(65543, 171), (131071, 255)]⟩

private instance byteDecidable (op : ByteOpcode) (a b c : Fp) : Decidable (op.constrain a b c) := by
  cases op <;> unfold ByteOpcode.constrain <;> infer_instance

private def byteValid (values : List Fp) : Bool :=
  match values with
  | [opcode, a, b, c] =>
    [ByteOpcode.AND, .OR, .XOR, .U8Range, .LTU, .MSB, .Range].any fun op =>
      opcode == (op.idx : Fp) && decide (op.constrain a b c)
  | _ => false

private def evaluate {Input : TypeMap} [ProvableType Input]
    (program : Var Input Fp → Circuit Fp (Var Channels.MemoryMsg Fp))
    (input : Input Fp) : Bool × List Fp :=
  let circuit := program (varFromOffset Input 0)
  let env := (circuit.proverEnvironment (ProverHint.empty Fp) (toElements input).toList).toEnvironment
  let operations := (circuit.operations (size Input)).toFlat
  let bytes := (FlatOperation.interactions operations).all fun interaction =>
    interaction.channel.name != "SP1Byte" || env interaction.mult == 0 ||
      byteValid (interaction.msg.map env).toList
  (InitialMemoryLookup.localConstraints image.initialMemory (2 ^ 48) env operations && bytes,
    (toElements (ProvableType.eval env (circuit.output (size Input)))).toList)

private def word (address : ℕ) : Word Fp := bitVecToWord (BitVec.ofNat 64 address)

private def ramInput (previous address current : ℕ) :
    OrderedInitialProvider.Inputs InitialRamProvider.Inputs Fp :=
  ⟨InitialMemoryRead.populate image.initialMemory address,
    OrderedBoundary.populate (word previous) (word current)⟩

private def registerInput (previous index current : ℕ) : OrderedInitialProvider.Inputs field Fp :=
  ⟨index, OrderedBoundary.populate (word previous) (word current)⟩

/-- info: exportable ✓ (644 witness cells) -/
#guard_msgs in
#assert_exportable (OrderedInitialProvider.ramCircuit (p := SP1Prime) image)

/-- info: exportable ✓ (133 witness cells) -/
#guard_msgs in
#assert_exportable (OrderedInitialProvider.registerCircuit (p := SP1Prime) image)

/-- Valid ordered RAM rows cross limb boundaries and reach the last aligned guest cell. -/
theorem constructedRamRows : [65536, 131064, 131072, 2 ^ 48 - 8].all (fun address =>
    ((OrderedInitialProvider.populateRam? image 32 address).map fun input =>
      let result := evaluate (OrderedInitialProvider.ramCircuit image).main input
      result.1 && (result.2 ==
        ([(0 : Fp), 0, (word address)[0], (word address)[1], (word address)[2]] ++
          (bitVecToWord (p := SP1Prime) (image.initialMemory.readWord address)).toList))).getD false) = true := by
  native_decide

/-- All 32 register indices emit their exact zero-valued, zero-time boundary messages. -/
theorem constructedRegisterRows : (List.range 32).all (fun index =>
    evaluate (OrderedInitialProvider.registerCircuit image).main (registerInput index index (index + 1)) ==
      (true, [0, 0, (index : Fp), 0, 0, 0, 0, 0, 0])) = true := by
  native_decide

/-- The ordered key cannot be changed independently of the authenticated Memory record. -/
theorem rejectsUnrelatedKeys :
    [(evaluate (OrderedInitialProvider.ramCircuit image).main (ramInput 32 65536 65538)).1,
     (evaluate (OrderedInitialProvider.registerCircuit image).main (registerInput 0 0 2)).1] =
      [false, false] := by native_decide

/-- Equal/reversed links, reserved or misaligned RAM, and out-of-range registers fail the AIR. -/
theorem rejectsInvalidBoundaryRows :
    [(evaluate (OrderedInitialProvider.ramCircuit image).main (ramInput 65537 65536 65537)).1,
     (evaluate (OrderedInitialProvider.ramCircuit image).main (ramInput 65538 65536 65537)).1,
     (evaluate (OrderedInitialProvider.ramCircuit image).main (ramInput 0 32 33)).1,
     (evaluate (OrderedInitialProvider.ramCircuit image).main (ramInput 0 65537 65538)).1,
     (evaluate (OrderedInitialProvider.registerCircuit image).main (registerInput 0 32 33)).1] =
      [false, false, false, false, false] := by native_decide

end SP1CleanTest.Core.MemoryBoundary
