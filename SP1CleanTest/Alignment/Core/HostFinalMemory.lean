import SP1Clean.Soundness.HostFinalMemory
import SP1CleanTest.Alignment.Core.LocalCore

/-! # Complete physical host assembly with outgoing Memory checks

Reuse the existing active ADD fixture, its interpreter, and actual Byte/Range providers. The
host queue is empty and both commitment banks have physical terminals. The target consumers
validate every final record, including unchanged registers and code RAM. All registered channel
occurrences are retained; this fixture checks the assembled AIR, not the unclosed capstone.
-/

namespace SP1CleanTest.Alignment.Core.HostFinalMemory

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core SP1Clean.Soundness

private abbrev Fp := ZMod SP1Prime
private abbrev Row := ℕ × List Fp

private def image := SP1CleanTest.Core.LocalCore.addFixture.1
private def source := SP1CleanTest.Core.LocalCore.addFixture.2.1
private def header := SP1CleanTest.Core.LocalCore.addFixture.2.2.1
private def coreRows := SP1CleanTest.Core.LocalCore.addFixture.2.2.2
private def target : MemorySnapshot :=
  { source.sail.memorySnapshot with registers := source.sail.memorySnapshot.registers.set 1 123 }

private def assembly (target : MemorySnapshot) :=
  Soundness.HostFinalMemory.ensemble (p := SP1Prime) image source target
    (SP1Clean.HostHintQueueBoundary.initial []) source.host HostCallReceivers.available
    (HostHintReadLocal.sourceResources []) []

private def word (value : ℕ) : Word Fp := Target.bitVecToWord (BitVec.ofNat 64 value)
private def record (address clock value : ℕ) : Channels.MemoryMsg Fp :=
  ⟨0, clock, (word address)[0], (word address)[1], (word address)[2], word value⟩

private def registerCheck (index clock value : ℕ) (selected : Fp) : Row :=
  (87, (toElements (⟨record index clock value, selected⟩ : FinalRegisterCheck.Inputs Fp)).toList)

private def ramCheck (clock : ℕ) : Row :=
  (88, (toElements (⟨⟨record 65536 clock (target.memory.readWord 65536).toNat,
    InitialMemoryRead.populate target.memory 65536⟩, 0⟩ : FinalRamCheck.Inputs Fp)).toList)

private def terminals : List Row :=
  [85, 86].map fun index => (index, (toElements (HostCommitBoundary.initial (p := SP1Prime))).toList)

private def rows : List Row :=
  coreRows ++ terminals ++ [registerCheck 1 13 123 1, registerCheck 2 12 100 0,
    registerCheck 3 11 23 0, ramCheck 0]

private def fixed (target : MemorySnapshot) : List (FiniteLookup Fp) :=
  let registers := FiniteLookup.ofStatic (target.registerTable (p := SP1Prime))
  let memory := FiniteLookup.ofStatic (target.memory.fixedTable (p := SP1Prime) (2 ^ 48))
  [{ registers with table := { registers.table with name := "sp1.native.target_registers" } },
    { memory with table := { memory.table with name := "sp1.native.target_memory" } }]

private def evaluated (target : MemorySnapshot) (row : Row) :=
  match (assembly target).tables[row.1]? with
  | none => (false, [])
  | some component => SP1CleanTest.Core.LocalCore.evaluateComponent image source component row.2 (fixed target)

private def check (target : MemorySnapshot) (input : SP1PublicIO Fp) (rows : List Row) : Bool :=
  let head := SP1CleanTest.Core.LocalCore.evaluateComponent image source
    (assembly target).verifierTable (toElements input).toList (fixed target)
  let initial := head :: rows.map (evaluated target)
  let providers := (initial.flatMap Prod.snd).filterMap SP1CleanTest.Core.LocalCore.provideBytes
  let all := initial ++ providers.map (evaluated target)
  let ledger := all.flatMap Prod.snd
  all.all Prod.fst && decide (ledger.length < SP1Prime) &&
    ledger.all fun (name, message, _) =>
      ((assembly target).channels.map RawChannel.name).contains name &&
        ((ledger.filter fun entry => entry.1 == name && entry.2.1 == message).map (·.2.2)).sum == 0

/-- The active ADD witness includes all target checks and actual lookup providers in one ledger. -/
theorem activeAcceptance : check target header rows = true := by native_decide

/-- No validator, unchanged final record or host terminal can disappear from the accepted witness. -/
theorem mutations :
    [check target header (rows.filter (fun row => row.1 != 88)),
     check target header (rows ++ [ramCheck 0]),
     check target header (rows.map fun row => if row.1 == 88 then ramCheck 1 else row),
     check target header (coreRows ++ terminals ++ [registerCheck 1 13 123 1, ramCheck 0]),
     check { target with registers := target.registers.set 31 1 } header rows,
     check { target with memory := target.memory.write 65544 1 } header rows,
     check target header (rows.filter (fun row => row.1 != 85))] = List.replicate 7 false := by
  native_decide

private def identityHeader : SP1PublicIO Fp :=
  { header with final_clk_0_16 := 9, final_pc0 := 0 }

private def identityRows : List Row :=
  [2, 5].map (fun index => (index, (toElements (OrderedBoundaryEnd.populate (word 0)
    (OrderedMemoryEnsemble.endKey (p := SP1Prime)))).toList)) ++ terminals ++
      [(57, List.replicate (size HaltChip.Inputs) 0)]

/-- An empty continuing segment needs no final inventory and still closes every physical channel. -/
theorem identityAcceptance : check source.sail.memorySnapshot identityHeader identityRows = true := by native_decide

end SP1CleanTest.Alignment.Core.HostFinalMemory
