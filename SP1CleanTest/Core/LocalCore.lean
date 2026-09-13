import SP1Clean.Soundness.LocalCoreGrounding
import SP1Clean.Model.Core.HostSnapshot
import SP1CleanTest.Audit.OneAddNativePremises
import ToClean.Air.EnsembleExport

/-! # Complete local-assembly constraint and ledger regression

The fixture starts at clock 9 with nonzero source registers and executes ADD. Rows are interpreted
at their actual indices in the 59-table local assembly. All assertions, fixed lookups, public
verifier constraints, channel membership, count bounds, and full-message balances are checked.
Byte/Range demands are closed by executing the actual provider circuits. An active HINT_LEN fixture
checks the wide syscall edge and all three Memory pairs, and records the unclosed host-result
binding with a concrete forged-return example. Same-register accesses and a real State clock carry
exercise the grounding interfaces; stopped-source rows are rejected while identities remain valid.
This is AIR conformance, not an execution theorem.
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

private def finalRecord (previous address clock value : ℕ) (epoch : ℕ := 0) : List Fp :=
  (toElements (OrderedMemoryProvider.populate
    (⟨epoch, clock, (word address)[0], (word address)[1], (word address)[2], word value⟩ : Channels.MemoryMsg Fp)
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

private def evaluate (image : ProgramImage) (source : ExecutionSnapshot) (component : Component Fp) (inputs : List Fp) : Bool × Ledger :=
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

private def evaluateRow (image : ProgramImage) (source : ExecutionSnapshot) (row : Row) : Bool × Ledger :=
  match (Soundness.LocalCore.tables image source)[row.1]? with
  | none => (false, [])
  | some component => evaluate image source component row.2

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

private def check (image : ProgramImage) (source : ExecutionSnapshot) (pi : SP1PublicIO Fp) (rows : List Row) : Bool :=
  let head := evaluate image source ⟨Soundness.LocalCore.verifier image source⟩ (toElements pi).toList
  let initial := head :: rows.map (evaluateRow image source)
  let demands := (initial.flatMap Prod.snd).filterMap byteProvider
  let evaluated := initial ++ demands.map (evaluateRow image source)
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
theorem activeLocalShard : check image source publicInput baseRows = true := by native_decide

/-- State endpoints are bound to the physical instruction ledger, not chosen independently. -/
theorem rejectsWrongEndpoints :
    [check image source { publicInput with init_clk_0_16 := 1 } baseRows,
     check image source { publicInput with final_clk_0_16 := 18 } baseRows,
     check image source { publicInput with final_pc0 := 8 } baseRows] = [false, false, false] := by native_decide

/-- Changing fixed incoming values or removing a register invalidates this physical witness. -/
theorem rejectsWrongSource :
    [check image { source with sail.registers := source.sail.registers.insert .x2 101 } publicInput baseRows,
     check image { source with sail.registers := source.sail.registers.erase .x2 } publicInput baseRows,
     check image { source with sail.memory := source.sail.memory.write 65536 0 } publicInput baseRows] =
      [false, false, false] := by native_decide

/-- The source's actual PC and clock cannot differ from the public incoming token. -/
theorem rejectsUnboundSource :
    [check image { source with clock := 10 } publicInput baseRows,
     check image { source with sail.registers := source.sail.registers.insert .PC 65540 } publicInput baseRows,
     check image { source with clock := 2 ^ 48 + 9 } publicInput baseRows,
     check image { source with sail.registers := source.sail.registers.insert .PC (2 ^ 48 + 65536) }
       publicInput baseRows] = [false, false, false, false] := by native_decide

/-- Platform configuration is checked even when the affected register is untouched by the row. -/
theorem rejectsInvalidPlatform :
    [check image { source with sail.registers := source.sail.registers.insert .misa 0 } publicInput baseRows,
     check image { source with sail.registers := source.sail.registers.insert .mstatus 8 } publicInput baseRows,
     check image { source with sail.registers := source.sail.registers.erase .pma_regions } publicInput baseRows] =
      [false, false, false] := by native_decide

/-- ROM agreement is enforced even when no source/final RAM row reads the changed code byte. -/
theorem checksUntouchedRom :
    check image source publicInput withoutRam = true ∧
      check image { source with sail.memory := source.sail.memory.write 65536 0 } publicInput withoutRam = false := by
  native_decide

/-- Missing or duplicate source records fail the actual Memory/order balances. -/
theorem rejectsBrokenInventory :
    [check image source publicInput (baseRows.drop 1),
     check image source publicInput (sourceRegister 0 1 :: baseRows),
     check image source publicInput (baseRows.filter (fun row => row.1 != 2)),
     check image source publicInput (baseRows.filter (fun row => row.1 != 4))] =
      [false, false, false, false] := by native_decide

/-- A forged final value cannot be hidden by keeping the same canonical address and clock. -/
theorem rejectsWrongFinalValue :
    check image source publicInput (baseRows.set 5 (3, finalRecord 0 1 13 124)) = false := by native_decide

/-- Fetch authentication rejects a missing ROM producer and an altered fixed lookup key. -/
theorem rejectsUnauthenticatedFetch :
    [check image source publicInput (baseRows.filter (fun row => row.1 != 6)),
     check image source publicInput (baseRows.set 10 (6, programRow.2.set 0 4))] =
      [false, false] := by native_decide

private def twoImage : ProgramImage := ⟨[(65536, 0x003100b3), (65540, 0x003100b3)], 65536, []⟩

private def twoSource : ExecutionSnapshot := { source with sail.memory := twoImage.initialMemory }

private def secondAdd : Row := (7, TraceGenTests.rTypeEventInputs
  { Audit.OneAddNativePremises.event with
    clk := 17, pc := 65540, tsA := 21, prevTsA := 13, prevA := 123,
    tsB := 20, prevTsB := 12, tsC := 19, prevTsC := 11 })

private def paddingAdd : Row := (7, List.replicate (size AddChip.Inputs) 0)

private def twoPublic : SP1PublicIO Fp :=
  { publicInput with final_clk_0_16 := 25, final_pc0 := 8 }

private def twoRows : List Row :=
  [sourceRegister 0 1, sourceRegister 2 2, sourceRegister 3 3, terminal 2 4,
    (3, finalRecord 0 1 21 123), (3, finalRecord 2 2 20 100), (3, finalRecord 3 3 19 23), terminal 5 4,
    programRow, (6, ((DecodedProgramProvider.populate? (p := SP1Prime) twoImage (65540, 0x003100b3) 1).map
      (fun input => (toElements input).toList)).getD []),
    secondAdd, paddingAdd, (7, Audit.OneAddNativePremises.inputs),
    (57, List.replicate (size HaltChip.Inputs) 0)]

/-- The physical ADD rows are reversed, with padding between them; the ledger still closes
for the two-step local segment. Duplicating an active occurrence invalidates it. -/
theorem acceptsReorderedPaddedSegment :
    check twoImage twoSource twoPublic twoRows = true ∧
      check twoImage twoSource twoPublic (secondAdd :: twoRows) = false := by native_decide

private def identityPublic : SP1PublicIO Fp :=
  { publicInput with final_clk_0_16 := 9, final_pc0 := 0 }

private def identityRows : List Row :=
  [terminal 2 0, terminal 5 0, paddingAdd, (57, List.replicate (size HaltChip.Inputs) 0)]

/-- A zero-step segment has equal State endpoints and empty touched inventories. The same
identity is accepted for a stopped host; this does not permit a semantic step after HALT. -/
theorem acceptsEmptySegments :
    check image source identityPublic identityRows = true ∧
      check image { source with host.exitCode := some 0 } identityPublic identityRows = true := by native_decide

private def aliasImage : ProgramImage := ⟨[(65536, 0x001080b3)], 65536, []⟩

private def aliasSource : ExecutionSnapshot :=
  { source with
    sail.registers := source.sail.registers.insert .x1 100
    sail.memory := aliasImage.initialMemory }

private def aliasEvent : TraceGenTests.AluEventRec :=
  { Audit.OneAddNativePremises.event with
    a := 200, c := 100, opB := 1, opC := 1, prevA := 100, prevTsA := 12, prevTsB := 11 }

private def aliasRows : List Row :=
  [(0, (toElements (OrderedSnapshotProvider.populate
    (SnapshotRegisterProvider.populate aliasSource.sail.memorySnapshot 1#5) 0 1)).toList), terminal 2 2,
    (3, finalRecord 0 1 13 200), terminal 5 2,
    (6, ((DecodedProgramProvider.populate? (p := SP1Prime) aliasImage (65536, 0x001080b3) 1).map
      (fun input => (toElements input).toList)).getD []),
    (7, TraceGenTests.rTypeEventInputs aliasEvent), (57, List.replicate (size HaltChip.Inputs) 0)]

/-- ADD x1,x1,x1 uses one source/final location and three consecutive touches within the row.
Skipping either intermediate prior record breaks the complete physical Memory ledger. -/
theorem acceptsSameRegisterTouches :
    check aliasImage aliasSource publicInput aliasRows = true ∧
      check aliasImage aliasSource publicInput
        (aliasRows.set 5 (7, TraceGenTests.rTypeEventInputs { aliasEvent with prevTsA := 0 })) = false ∧
      check aliasImage aliasSource publicInput
        (aliasRows.set 5 (7, TraceGenTests.rTypeEventInputs { aliasEvent with prevTsB := 0 })) = false := by
  native_decide

private def clockEvent (clock : ℕ) : TraceGenTests.AluEventRec :=
  { Audit.OneAddNativePremises.event with clk := clock, tsA := clock + 4, tsB := clock + 3, tsC := clock + 2 }

private def clockPublic (clock : ℕ) : SP1PublicIO Fp :=
  { publicInput with
    init_clk_0_16 := (clock % 65536 : ℕ)
    init_clk_16_24 := (clock / 65536 % 256 : ℕ)
    final_clk_0_16 := ((clock + 8) % 65536 : ℕ)
    final_clk_16_24 := ((clock + 8) / 65536 % 256 : ℕ)
    final_clk_24_32 := ((clock + 8) / 2 ^ 24 : ℕ) }

private def clockRows (clock : ℕ) : List Row :=
  [sourceRegister 0 1, sourceRegister 2 2, sourceRegister 3 3, terminal 2 4,
    (3, finalRecord 0 1 (clock + 4) 123), (3, finalRecord 2 2 (clock + 3) 100),
    (3, finalRecord 3 3 (clock + 2) 23), terminal 5 4, programRow,
    (7, TraceGenTests.rTypeEventInputs (clockEvent clock)), (57, List.replicate (size HaltChip.Inputs) 0)]

private def clockCarry : Row := (56, (toElements ({
    next_clk_32_48 := 0, next_clk_24_32 := 1, next_clk_16_24 := 0, next_clk_0_16 := 1,
    clk_high := 0, clk_low := 2 ^ 24 + 1, next_pc0 := 4, next_pc1 := 1, next_pc2 := 0,
    pc0 := 4, pc1 := 1, pc2 := 0, is_clk := 1, is_real := 1 } : StateBumpChip.Inputs Fp)).toList)

/-- A row crossing the 24-bit epoch needs the actual StateBump link to its canonical public end.
The three Memory touches still precede the carry and preserve their original timestamps. -/
theorem acceptsStateClockCarry :
    let clock := 2 ^ 24 - 7
    check image { source with clock := clock } (clockPublic clock) (clockCarry :: clockRows clock) = true ∧
      check image { source with clock := clock } (clockPublic clock) (clockRows clock) = false := by
  native_decide

/-- Source validation checks clock range, while active CPU rows additionally require SP1's
1-mod-8 clock phase. Shared semantic compiler bounds must account for this profile condition. -/
theorem clockPhaseNeedsProfile :
    checkExecutionSource image { source with clock := 10 } = true ∧
      check image { source with clock := 10 } (clockPublic 10) (clockRows 10) = false := by
  native_decide

/-- The stopped-source clock constraints reject this formerly accepted active ADD. Empty
segments at stopped sources remain valid, as checked by `acceptsEmptySegments`. -/
theorem rejectsActiveRowsAfterHalt :
    check image { source with host.exitCode := some 0 } publicInput baseRows = false := by native_decide

private def syscallImage : ProgramImage := ⟨[(65536, 0x00000073)], 65536, []⟩

private def syscallProgram : GuestProgram := syscallImage.toGuestProgram (by decide)

private def syscallPolicy : HostPolicy :=
  ⟨⟨fun address => decide (65536 ≤ address ∧ address < 65540), 65536, 2 ^ 48⟩, SP1Prime⟩

private def syscallSource : ExecutionSnapshot where
  sail := { registers := (((configuredState 65536).regs.insert .x5 240).insert .x10 7).insert .x11 9
            memory := syscallImage.initialMemory }
  host := { io := ⟨[[1, 2, 3]], []⟩ }
  clock := 9

private def syscallInput (result : ℕ) : SyscallInstrsChip.Inputs Fp :=
  { state := ⟨0, 0, 9, #v[0, 1, 0]⟩
    op_a := 5, op_a_memory := ⟨word 240, ⟨0, 12⟩⟩, op_a_0 := 0
    op_b := 10, op_b_memory := ⟨word 7, ⟨0, 11⟩⟩
    op_c := 11, op_c_memory := ⟨word 9, ⟨0, 10⟩⟩
    next_pc := #v[4, 1, 0], is_halt := 0
    op_a_value := word result, syscall_id_bytes := U16toU8OperationSafe.populate (word 240)
    is_enter_unconstrained := IsZeroOperation.populate (237 : Fp)
    is_hint_len := IsZeroOperation.populate (0 : Fp)
    is_halt_zero := IsZeroOperation.populate (240 : Fp)
    is_commit := IsZeroOperation.populate (224 : Fp)
    is_commit_deferred := IsZeroOperation.populate (214 : Fp)
    digest_index_bits := Vector.replicate 8 0, digest_word := 0
    op_b_cmp := ⟨1⟩, op_c_cmp := ⟨1⟩, is_real := 1 }

private def syscallRows (result : ℕ) : List Row :=
  let sourceRow (previous index : ℕ) : Row :=
    (0, (toElements (OrderedSnapshotProvider.populate
      (SnapshotRegisterProvider.populate syscallSource.sail.memorySnapshot (BitVec.ofNat 5 index))
      previous index)).toList)
  [sourceRow 0 5, sourceRow 6 10, sourceRow 11 11, terminal 2 12,
    (3, finalRecord 0 5 13 result), (3, finalRecord 6 10 12 7), (3, finalRecord 11 11 11 9), terminal 5 12,
    (6, ((DecodedProgramProvider.populate? (p := SP1Prime) syscallImage (65536, 0x00000073) 1).map
      (fun input => (toElements input).toList)).getD []),
    (57, List.replicate (size HaltChip.Inputs) 0), (58, (toElements (syscallInput result)).toList)]

private def syscallPublic : SP1PublicIO Fp := { publicInput with final_clk_0_16 := 273 }

/-- An active ECALL closes the actual 59-table ledger with all three nonzero source registers,
its wide State edge, the changed result, and source/final inventories. No syscall row is erased. -/
theorem activeSyscallLocalShard :
    check syscallImage syscallSource syscallPublic (syscallRows 3) = true := by native_decide

/-- Missing, duplicated, stale, or corrupted syscall read-back records fail complete AIR checks. -/
theorem rejectsBrokenSyscallLedger :
    [check syscallImage syscallSource syscallPublic ((syscallRows 3).drop 1),
     check syscallImage syscallSource syscallPublic ((syscallRows 3).set 4 (3, finalRecord 0 5 13 4)),
     check syscallImage syscallSource syscallPublic ((syscallRows 3).set 5 (3, finalRecord 6 10 11 7)),
     check syscallImage syscallSource syscallPublic ((syscallRows 3).set 6 (3, finalRecord 11 11 11 8)),
     check syscallImage syscallSource syscallPublic ((syscallRows 3) ++ [(58, (toElements (syscallInput 3)).toList)])] =
      [false, false, false, false, false] := by native_decide

private def epochRows (epoch : ℕ) : List Row :=
  let refresh (index value : ℕ) : Row :=
    let input : MemoryBumpChip.Inputs Fp :=
      { access := ⟨word value, ⟨0, 0, 0, ((epoch - 1) % 65536 : ℕ), ((epoch - 1) / 65536 : ℕ)⟩⟩
        addr := index, clk_0_16 := 0, clk_16_24 := 0, clk_24_32 := (epoch % 256 : ℕ)
        clk_32_48 := (epoch / 256 : ℕ), is_real := 1 }
    (55, (toElements input).toList)
  let input := { syscallInput 3 with state.clk_high := (epoch : Fp) }
  ((((syscallRows 3).set 4 (3, finalRecord 0 5 13 3 epoch)).set 5 (3, finalRecord 6 10 12 7 epoch)).set
    6 (3, finalRecord 11 11 11 9 epoch)).set 10 (58, (toElements input).toList) ++
      [refresh 5 240, refresh 10 7, refresh 11 9]

/-- One refresh per touched register reaches the incoming epoch, even at the largest 24-bit
high clock. The continuation does not need rows for all preceding clock epochs. -/
theorem acceptsDistantSourceEpochs : [1, 2 ^ 24 - 1].all (fun epoch =>
    check syscallImage { syscallSource with clock := epoch * 2 ^ 24 + 9 }
      { syscallPublic with
        init_clk_24_32 := (epoch % 256 : ℕ), init_clk_32_48 := (epoch / 256 : ℕ)
        final_clk_24_32 := (epoch % 256 : ℕ), final_clk_32_48 := (epoch / 256 : ℕ) }
      (epochRows epoch)) = true := by native_decide

/-- Recorded integration gap: matching a forged HINT_LEN return on both the instruction and final
record still satisfies this AIR, although finite host execution returns three. Host binding must
close this before any local execution-equivalence theorem is claimed. -/
theorem hintReturnNeedsHostBinding :
    check syscallImage syscallSource syscallPublic (syscallRows 4) = true ∧
      ((syscallSource.hostStep? syscallPolicy syscallProgram).map
        (fun output => output.1.sail.registers.get? LeanRV64D.Defs.Register.x5)) = some (some 3) := by
  native_decide

end SP1CleanTest.Core.LocalCore
