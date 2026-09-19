import SP1Clean.Proofs.Chips.OrderedSnapshotProvider
import SP1Clean.Model.SP1Field
import ToClean.Air.EnsembleExport

/-! # Arbitrary source-snapshot AIR regressions

Execute the real witness programs and check all flattened assertions, concrete fixed lookups,
and nonzero Byte messages. These are provider regressions, not a whole-machine balance claim.
-/

namespace SP1CleanTest.Core.SnapshotBoundary

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core SP1Clean.Soundness.Target

private abbrev Fp := ZMod SP1Prime

private def snapshot : MemorySnapshot :=
  ⟨Vector.ofFn (fun index => BitVec.ofNat 64 (index.val * 0x123456789abcdef)),
    ⟨[(65536, 42), (65543, 171), (131071, 255), (2 ^ 48 - 1, 197)]⟩⟩

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
  let tables := [FiniteLookup.ofStatic (snapshot.registerTable (p := SP1Prime)),
    FiniteLookup.ofStatic (snapshot.memory.fixedTable (p := SP1Prime) (2 ^ 48))]
  let valid := operations.all fun operation =>
    match operation with
    | .assert expression => env expression == 0
    | .lookup lookup => tables.any fun fixed => lookup.table.name == fixed.table.name &&
        fixed.rows.any (fun row => row.toArray == (lookup.entry.map env).toArray)
    | .interact interaction => interaction.channel.name != "SP1Byte" || env interaction.mult == 0 ||
        byteValid (interaction.msg.map env).toList
    | .witness .. => true
  (valid, (toElements (ProvableType.eval env (circuit.output (size Input)))).toList)

private def name : String := "SP1NativeSourceMemoryOrder"

/-- info: exportable ✓ (128 witness cells) -/
#guard_msgs in
#assert_exportable (OrderedSnapshotProvider.registerCircuit (p := SP1Prime) name snapshot)

/-- info: exportable ✓ (644 witness cells) -/
#guard_msgs in
#assert_exportable (OrderedSnapshotProvider.ramCircuit (p := SP1Prime) name snapshot)

/-- Every register, including x0 and multi-limb nonzero values, yields its authenticated record. -/
theorem constructedRegisters : (List.range 32).all (fun index =>
    let payload := SnapshotRegisterProvider.populate snapshot (BitVec.ofNat 5 index)
    let input := OrderedSnapshotProvider.populate payload index index
    evaluate (OrderedSnapshotProvider.registerCircuit name snapshot).main input ==
      (true, [0, 0, (index : Fp), 0, 0] ++ payload.value.toList)) = true := by native_decide

/-- Changed values in any limb, a substituted index, an invalid index, and a forged x0 all fail. -/
theorem rejectsForgedRegisters :
    let payload := SnapshotRegisterProvider.populate (p := SP1Prime) snapshot 5
    let bad := (List.range 4).map (fun limb =>
      let changed := payload.value.set! limb (payload.value[limb]! + 1)
      { payload with value := changed }) ++
      [{ payload with index := 6 }, { payload with index := 32 }, { payload with index := 0 }]
    bad.all (fun input => !(evaluate (SnapshotRegisterProvider.circuit snapshot).main input).1) = true := by
  native_decide

/-- Explicit and default-zero RAM bytes are authenticated, including the last aligned word. -/
theorem constructedRam : [65536, 131064, 131072, 2 ^ 48 - 8].all (fun address =>
    ((OrderedSnapshotProvider.populateRam? snapshot 32 address).map fun input =>
      let result := evaluate (OrderedSnapshotProvider.ramCircuit name snapshot).main input
      let word := bitVecToWord (p := SP1Prime) (BitVec.ofNat 64 address)
      result == (true, [(0 : Fp), 0, word[0], word[1], word[2]] ++
        (bitVecToWord (p := SP1Prime) (snapshot.memory.readWord address)).toList)).getD false) = true := by
  native_decide

/-- A row built from different source memory cannot authenticate under this snapshot's lookup. -/
theorem rejectsForgedRam :
    let forged := { snapshot with memory := snapshot.memory.write 65536 99 }
    ((SnapshotRamProvider.populate? forged 65536).map fun input =>
      (evaluate (SnapshotRamProvider.circuit snapshot).main input).1) = some false := by native_decide

/-- Ordering still binds to the authenticated location; it cannot be a witness-selected key. -/
theorem rejectsUnrelatedKey :
    let input := OrderedSnapshotProvider.populate
      (SnapshotRegisterProvider.populate snapshot 5) 0 6
    (evaluate (OrderedSnapshotProvider.registerCircuit name snapshot).main input).1 = false := by native_decide

/-- Extensional comparison accepts obsolete history and explicit zero entries. -/
theorem equivalentHistories :
    let other := { snapshot with memory :=
      ⟨snapshot.memory.entries ++ [(65536, 99), (77777, 0)]⟩ }
    snapshot.equivalent other = true := by native_decide

/-- Equality includes addresses absent from a shard's provider rows, and every register. -/
theorem rejectsUntouchedMutations :
    [snapshot.equivalent { snapshot with memory := snapshot.memory.write 77777 1 },
     snapshot.equivalent { snapshot with registers := snapshot.registers.set! 31 0 },
     snapshot.equivalent { snapshot with memory := snapshot.memory.write (2 ^ 48 - 1) 0 }] =
      [false, false, false] := by native_decide

end SP1CleanTest.Core.SnapshotBoundary
