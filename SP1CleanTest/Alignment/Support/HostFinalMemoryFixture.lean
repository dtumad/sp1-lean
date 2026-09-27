import SP1Clean.Soundness.HostFinalMemory
import SP1CleanTest.Alignment.Support.LocalCoreFixture

/-! # Shared complete-memory fixture

The walkthrough and regression theorems share the physical assembly, rows, and evaluator.
-/

namespace SP1CleanTest.Alignment.Core.HostFinalMemory.Fixture

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core SP1Clean.Soundness

abbrev Fp := ZMod SP1Prime
abbrev Row := ℕ × List Fp

def image := SP1CleanTest.Core.LocalCore.Fixture.image
def source := SP1CleanTest.Core.LocalCore.Fixture.source
def header := SP1CleanTest.Core.LocalCore.Fixture.publicInput
def coreRows := SP1CleanTest.Core.LocalCore.Fixture.baseRows
def target : MemorySnapshot :=
  { source.sail.memorySnapshot with registers := source.sail.memorySnapshot.registers.set 1 123 }

def assembly (target : MemorySnapshot) :=
  Soundness.HostFinalMemory.ensemble (p := SP1Prime) image source target
    (SP1Clean.HostHintQueueBoundary.initial []) source.host HostCallReceivers.available
    (HostHintReadLocal.sourceResources []) []

def word (value : ℕ) : Word Fp := Target.bitVecToWord (BitVec.ofNat 64 value)
def record (address clock value : ℕ) : Channels.MemoryMsg Fp :=
  ⟨0, clock, (word address)[0], (word address)[1], (word address)[2], word value⟩

def registerCheck (index clock value : ℕ) (selected : Fp) : Row :=
  (87, (toElements (⟨record index clock value, selected⟩ : FinalRegisterCheck.Inputs Fp)).toList)

def ramCheck (clock : ℕ) : Row :=
  (88, (toElements (⟨⟨record 65536 clock (target.memory.readWord 65536).toNat,
    InitialMemoryRead.populate target.memory 65536⟩, 0⟩ : FinalRamCheck.Inputs Fp)).toList)

def terminals : List Row :=
  [85, 86].map fun index => (index, (toElements (HostCommitBoundary.initial (p := SP1Prime))).toList)

def rows : List Row :=
  coreRows ++ terminals ++ [registerCheck 1 13 123 1, registerCheck 2 12 100 0,
    registerCheck 3 11 23 0, ramCheck 0]

def fixed (target : MemorySnapshot) : List (FiniteLookup Fp) :=
  let registers := FiniteLookup.ofStatic (target.registerTable (p := SP1Prime))
  let memory := FiniteLookup.ofStatic (target.memory.fixedTable (p := SP1Prime) (2 ^ 48))
  [{ registers with table := { registers.table with name := "sp1.native.target_registers" } },
    { memory with table := { memory.table with name := "sp1.native.target_memory" } }]

def evaluated (target : MemorySnapshot) (row : Row) :=
  match (assembly target).tables[row.1]? with
  | none => (false, [])
  | some component => SP1CleanTest.Core.LocalCore.Fixture.evaluate image source component row.2 (fixed target)

def check (target : MemorySnapshot) (input : SP1PublicIO Fp) (rows : List Row) : Bool :=
  let head := SP1CleanTest.Core.LocalCore.Fixture.evaluate image source
    (assembly target).verifierTable (toElements input).toList (fixed target)
  let initial := head :: rows.map (evaluated target)
  let providers := (initial.flatMap Prod.snd).filterMap SP1CleanTest.Core.LocalCore.Fixture.byteProvider
  let all := initial ++ providers.map (evaluated target)
  let ledger := all.flatMap Prod.snd
  all.all Prod.fst && decide (ledger.length < SP1Prime) &&
    ledger.all fun (name, message, _) =>
      ((assembly target).channels.map RawChannel.name).contains name &&
        ((ledger.filter fun entry => entry.1 == name && entry.2.1 == message).map (·.2.2)).sum == 0

def identityHeader : SP1PublicIO Fp :=
  { header with final_clk_0_16 := 9, final_pc0 := 0 }

def identityRows : List Row :=
  [2, 5].map (fun index => (index, (toElements (OrderedBoundaryEnd.populate (word 0)
    (OrderedMemoryEnsemble.endKey (p := SP1Prime)))).toList)) ++ terminals ++
      [(57, List.replicate (size HaltChip.Inputs) 0)]

/-- Named actual outcomes. These are fixture checks, not proof certificates. -/
def results : List (String × Bool × Bool) :=
  [("active-add", true, check target header rows),
   ("missing-ram-validator", false, check target header (rows.filter (fun row => row.1 != 88))),
   ("duplicate-ram-validator", false, check target header (rows ++ [ramCheck 0])),
   ("wrong-final-record-clock", false,
     check target header (rows.map fun row => if row.1 == 88 then ramCheck 1 else row)),
   ("missing-unchanged-register-validators", false,
     check target header (coreRows ++ terminals ++ [registerCheck 1 13 123 1, ramCheck 0])),
   ("changed-untouched-x31", false, check { target with registers := target.registers.set 31 1 } header rows),
   ("changed-untouched-ram", false, check { target with memory := target.memory.write 65544 1 } header rows),
   ("missing-bank-terminal", false, check target header (rows.filter (fun row => row.1 != 85))),
   ("empty-identity", true, check source.sail.memorySnapshot identityHeader identityRows)]

end SP1CleanTest.Alignment.Core.HostFinalMemory.Fixture
