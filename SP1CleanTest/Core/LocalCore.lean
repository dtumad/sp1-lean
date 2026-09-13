import SP1Clean.Soundness.LocalCoreBoundaries
import SP1CleanTest.Audit.OneAddNativePremises
import ToClean.Air.EnsembleExport

/-! # Complete local-assembly constraint and ledger regression

The fixture starts at clock 9 with nonzero source registers and executes ADD. Rows are interpreted
at their actual indices in the 59-table local assembly. All assertions, fixed lookups, public
verifier constraints, channel membership, count bounds, and full-message balances are checked.
Byte/Range demands are closed by executing the actual provider circuits, not by assuming their
semantic guarantees. This is executable AIR conformance; the local execution theorem is still open.
-/

namespace SP1CleanTest.Core.LocalCore

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core SP1Clean.Soundness SP1Clean.Soundness.Target

private abbrev Fp := ZMod SP1Prime
private abbrev Row := ℕ × List Fp
private abbrev Ledger := List (String × List Fp × Fp)

private def image : ProgramImage := ⟨[(65536, 0x003100b3)], 65536, []⟩

private def source : ExecutionSnapshot where
  sail := { registers := ((configuredState 65536).regs.insert .x2 100).insert .x3 23
            memory := image.initialMemory }
  host := {}
  clock := 9

private def snapshot : MemorySnapshot := source.sail.memorySnapshot

private def publicInput : SP1PublicIO Fp where
  init_clk_0_16 := 9
  init_clk_16_24 := 0
  init_clk_24_32 := 0
  init_clk_32_48 := 0
  init_pc0 := 0
  init_pc1 := 1
  init_pc2 := 0
  final_clk_0_16 := 17
  final_clk_16_24 := 0
  final_clk_24_32 := 0
  final_clk_32_48 := 0
  final_pc0 := 4
  final_pc1 := 1
  final_pc2 := 0
  exit_code := 0
  is_execution_shard := 1
  committed_value_digest := Vector.replicate 32 0

private def word (value : ℕ) : Word Fp := bitVecToWord (BitVec.ofNat 64 value)

private def sourceRegister (previous index : ℕ) : Row :=
  (0, (toElements (OrderedSnapshotProvider.populate
    (SnapshotRegisterProvider.populate snapshot (BitVec.ofNat 5 index)) previous index)).toList)

private def sourceRam : Row :=
  (1, (toElements (OrderedSnapshotProvider.populate
    (InitialMemoryRead.populate (p := SP1Prime) snapshot.memory 65536) 4 65536)).toList)

private def terminal (table previous : ℕ) : Row :=
  (table, (toElements (OrderedBoundaryEnd.populate (word previous)
    (OrderedMemoryEnsemble.endKey (p := SP1Prime)))).toList)

private def finalRecord (previous address clock value : ℕ) : List Fp :=
  (toElements (OrderedMemoryProvider.populate
    (⟨0, clock, (word address)[0], (word address)[1], (word address)[2], word value⟩ : Channels.MemoryMsg Fp)
    previous address)).toList

private def programRow : Row :=
  (6, ((DecodedProgramProvider.populate? (p := SP1Prime) image (65536, 0x003100b3) 1).map
    (fun input => (toElements input).toList)).getD [])

private def baseRows : List Row :=
  [sourceRegister 0 1, sourceRegister 2 2, sourceRegister 3 3, sourceRam, terminal 2 65537,
    (3, finalRecord 0 1 13 123), (3, finalRecord 2 2 12 100), (3, finalRecord 3 3 11 23),
    (4, finalRecord 4 65536 0 (snapshot.memory.readWord 65536).toNat), terminal 5 65537,
    programRow, (7, Audit.OneAddNativePremises.inputs),
    (57, List.replicate (size HaltChip.Inputs) 0)]

private def withoutRam : List Row :=
  baseRows.filter (fun row => !([1, 2, 4, 5].contains row.1)) ++ [terminal 2 4, terminal 5 4]

private def evaluate (source : ExecutionSnapshot) (component : Component Fp) (inputs : List Fp) : Bool × Ledger :=
  let program := component.circuit.main component.rowInputVar
  let env := (program.proverEnvironment (ProverHint.empty Fp) inputs).toEnvironment
  let operations := (program.operations component.rowOffset).toFlat
  let fixed := [FiniteLookup.ofStatic (source.sail.memorySnapshot.registerTable (p := SP1Prime)),
    FiniteLookup.ofStatic (source.sail.memory.fixedTable (p := SP1Prime) (2 ^ 48)),
    FiniteLookup.ofStatic (image.programTable (p := SP1Prime))]
  let valid := inputs.length == component.rowOffset && operations.all fun operation =>
    match operation with
    | .assert expression => env expression == 0
    | .lookup lookup => fixed.any fun table => lookup.table.name == table.table.name &&
        table.rows.any (fun row => row.toArray == (lookup.entry.map env).toArray)
    | .witness .. | .interact .. => true
  (valid, (FlatOperation.interactions operations).map fun interaction =>
    (interaction.channel.name, (interaction.msg.map env).toList, env interaction.mult))

private def evaluateRow (source : ExecutionSnapshot) (row : Row) : Bool × Ledger :=
  match (Soundness.LocalCore.tables image source)[row.1]? with
  | none => (false, [])
  | some component => evaluate source component row.2

/-- One real provider row for each Byte demand. Provider input shapes are checked at their actual
table indices; unused families are empty. The fixture needs U8Range, LTU, MSB, and fixed Range. -/
private def byteProvider (entry : String × List Fp × Fp) : Option Row :=
  if entry.1 != "SP1Byte" || entry.2.2 == 0 then none else
  match entry.2.1 with
  | [opcode, a, b, c] =>
    if opcode == 3 then some (32, [b, c, -entry.2.2])
    else if opcode == 4 then some (37, [b, c, -entry.2.2])
    else if opcode == 5 then some (33, [b, -entry.2.2])
    else if opcode == 6 && b.val < 17 then some (38 + b.val, [a, -entry.2.2])
    else some (59, [])
  | _ => some (59, [])

private def check (source : ExecutionSnapshot) (pi : SP1PublicIO Fp) (rows : List Row) : Bool :=
  let head := evaluate source ⟨Soundness.LocalCore.verifier image source⟩ (toElements pi).toList
  let initial := head :: rows.map (evaluateRow source)
  let demands := (initial.flatMap Prod.snd).filterMap byteProvider
  let evaluated := initial ++ demands.map (evaluateRow source)
  let ledger := evaluated.flatMap Prod.snd
  evaluated.all Prod.fst && decide (ledger.length < SP1Prime) &&
    ledger.all fun (name, message, _) =>
      ((Soundness.LocalCore.ensemble (p := SP1Prime) image source).channels.map RawChannel.name).contains name &&
        ((ledger.filter (fun entry => entry.1 == name && entry.2.1 == message)).map
          (fun entry => entry.2.2)).sum == 0

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (Soundness.LocalCore.verifier (p := SP1Prime) image source)

/-- The full local fixture has an active instruction, nonzero incoming registers, and no boot clock. -/
theorem activeLocalShard : check source publicInput baseRows = true := by native_decide

/-- State endpoints are bound to the physical instruction ledger, not chosen independently. -/
theorem rejectsWrongEndpoints :
    [check source { publicInput with init_clk_0_16 := 1 } baseRows,
     check source { publicInput with final_clk_0_16 := 18 } baseRows,
     check source { publicInput with final_pc0 := 8 } baseRows] = [false, false, false] := by native_decide

/-- Changing fixed incoming values or removing a register invalidates this physical witness. -/
theorem rejectsWrongSource :
    [check { source with sail.registers := source.sail.registers.insert .x2 101 } publicInput baseRows,
     check { source with sail.registers := source.sail.registers.erase .x2 } publicInput baseRows,
     check { source with sail.memory := source.sail.memory.write 65536 0 } publicInput baseRows] =
      [false, false, false] := by native_decide

/-- The source's actual PC and clock cannot differ from the public incoming token. -/
theorem rejectsUnboundSource :
    [check { source with clock := 10 } publicInput baseRows,
     check { source with sail.registers := source.sail.registers.insert .PC 65540 } publicInput baseRows,
     check { source with clock := 2 ^ 48 + 9 } publicInput baseRows,
     check { source with sail.registers := source.sail.registers.insert .PC (2 ^ 48 + 65536) }
       publicInput baseRows] = [false, false, false, false] := by native_decide

/-- Platform configuration is checked even when the affected register is untouched by the row. -/
theorem rejectsInvalidPlatform :
    [check { source with sail.registers := source.sail.registers.insert .misa 0 } publicInput baseRows,
     check { source with sail.registers := source.sail.registers.insert .mstatus 8 } publicInput baseRows,
     check { source with sail.registers := source.sail.registers.erase .pma_regions } publicInput baseRows] =
      [false, false, false] := by native_decide

/-- ROM agreement is enforced even when no source/final RAM row reads the changed code byte. -/
theorem checksUntouchedRom :
    check source publicInput withoutRam = true ∧
      check { source with sail.memory := source.sail.memory.write 65536 0 } publicInput withoutRam = false := by
  native_decide

/-- Missing or duplicate source records fail the actual Memory/order balances. -/
theorem rejectsBrokenInventory :
    [check source publicInput (baseRows.drop 1),
     check source publicInput (sourceRegister 0 1 :: baseRows),
     check source publicInput (baseRows.filter (fun row => row.1 != 2)),
     check source publicInput (baseRows.filter (fun row => row.1 != 4))] =
      [false, false, false, false] := by native_decide

/-- A forged final value cannot be hidden by keeping the same canonical address and clock. -/
theorem rejectsWrongFinalValue :
    check source publicInput (baseRows.set 5 (3, finalRecord 0 1 13 124)) = false := by native_decide

end SP1CleanTest.Core.LocalCore
