module

public import SP1Clean.Soundness.HostFinalMemory
public import SP1CleanTest.Alignment.Support.LocalCoreFixture
public import ToClean.Air.TableBuild

/-! # Shared complete-memory fixture

The walkthrough and regression theorems share the physical assembly, rows, and evaluator.
The public verifier runs separately at the data derived from the actual physical tables.
-/

@[expose] public section

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
    (HostHintReadLocal.sourceResources []) [] (Soundness.HostFinalMemory.source_unique_names image source target)

def word (value : ℕ) : Word Fp := Target.bitVecToWord (BitVec.ofNat 64 value)
def record (address clock value : ℕ) : Channels.MemoryMsg Fp :=
  ⟨0, clock, (word address)[0], (word address)[1], (word address)[2], word value⟩

/-- Source resources follow the actual core and receiver inventory. -/
private def resourceStart : ℕ :=
  (Soundness.HostFinalMemory.beforeChecks (p := SP1Prime) image source
    HostCallReceivers.available []).length

/-- Target checks follow the complete source-resource block. -/
private def checkStart : ℕ :=
  (Soundness.HostFinalMemory.beforeChecks (p := SP1Prime) image source
    HostCallReceivers.available (HostHintReadLocal.sourceResources [])).length

def registerCheck (index clock value : ℕ) (selected : Fp) : Row :=
  (checkStart, (toElements (M := FinalRegisterCheck.RowInput) ((⟨record index clock value, selected⟩, 1) : FinalRegisterCheck.RowInput Fp)).toList)

def ramCheck (clock : ℕ) : Row :=
  (checkStart + 1, (toElements (M := FinalRamCheck.RowInput) ((⟨record 65536 clock (target.memory.readWord 65536).toNat, 0⟩, 1) : FinalRamCheck.RowInput Fp)).toList)

def terminals : List Row :=
  [2, 3].map fun offset =>
    (resourceStart + offset, (toElements (HostCommitBoundary.initial (p := SP1Prime))).toList)

def rows : List Row :=
  coreRows ++ terminals ++ [registerCheck 1 13 123 1, registerCheck 2 12 100 0,
    registerCheck 3 11 23 0, ramCheck 0]

/-- Retain every physical table and fixed membership row in the declared assembly order. -/
def builtTables (target : MemorySnapshot) (rows : List Row)
    (bounded : rows.length ≤ UInt64.size) : List (Table Fp) :=
  let components := (assembly target).tables
  let inputs := fun index => (rows.filter (fun row => row.1 == index)).map (·.2)
  let channels := [(source.sail.memorySnapshot.registerTable (p := SP1Prime)).channel.name,
    (FinalRegisterValue.membership (p := SP1Prime) target).channel.name,
    "sp1.native.initial_memory", "sp1.native.target_memory", "SP1Program"]
  let ledger := StaticMembership.demandLedger components inputs channels (fun _ _ => #[]) (ProverHint.empty Fp)
  StaticMembership.buildTables components inputs ledger (fun _ _ => #[]) (ProverHint.empty Fp)
    (fun _ => (List.length_map _).le.trans ((List.length_filter_le _ _).trans bounded))

/-- Only committed physical rows determine the verifier's data environment. -/
def witness (target : MemorySnapshot) (input : SP1PublicIO Fp) (rows : List Row)
    (bounded : rows.length ≤ UInt64.size) :
    EnsembleWitness (assembly target) :=
  EnsembleWitness.ofTables _ (builtTables target rows bounded) input (by
    unfold builtTables
    exact StaticMembership.buildTables_components (F := Fp) ..)

def check (target : MemorySnapshot) (input : SP1PublicIO Fp) (rows : List Row) : Bool :=
  if bounded : rows.length ≤ UInt64.size then
  let installed := assembly target
  let registered := installed.channels.map RawChannel.name
  let consumers := witness target input rows bounded
  let providers := consumers.interactions.filterMap fun interaction =>
    SP1CleanTest.Core.LocalCore.Fixture.byteProvider
      (interaction.channel.name, interaction.msg.toList, interaction.mult)
  let completeRows := rows ++ providers
  if completeBounded : completeRows.length ≤ UInt64.size then
  let built := witness target input completeRows completeBounded
  let ledger := built.interactions.map fun interaction =>
    (interaction.channel.name, interaction.msg.toList, interaction.mult)
  let valid := completeRows.all fun row =>
    match installed.tables[row.1]? with
    | none => false
    | some component => component.fixedColumns.isNone &&
        (SP1CleanTest.Core.LocalCore.Fixture.evaluate image source component row.2).1
  valid && decide (ledger.length < SP1Prime) &&
    ledger.all fun (name, message, _) =>
      registered.contains name &&
        ((ledger.filter fun entry => entry.1 == name && entry.2.1 == message).map (·.2.2)).sum == 0
  else false
  else false

def identityHeader : SP1PublicIO Fp :=
  { header with final_clk_0_16 := 9, final_pc0 := 0 }

def identityRows : List Row :=
  [2, 5].map (fun index => (index, (toElements (OrderedBoundaryEnd.populate (word 0)
    (OrderedMemoryEnsemble.endKey (p := SP1Prime)))).toList)) ++ terminals ++
      [(57, List.replicate (size HaltChip.Inputs) 0)]

/-- Named actual outcomes. These are fixture checks, not proof certificates. -/
def results : List (String × Bool × Bool) :=
  [("active-add", true, check target header rows),
   ("missing-ram-validator", false, check target header (rows.filter (fun row => row.1 != checkStart + 1))),
   ("duplicate-ram-validator", false, check target header (rows ++ [ramCheck 0])),
   ("wrong-final-record-clock", false,
     check target header (rows.map fun row => if row.1 == checkStart + 1 then ramCheck 1 else row)),
   ("missing-unchanged-register-validators", false,
     check target header (coreRows ++ terminals ++ [registerCheck 1 13 123 1, ramCheck 0])),
   ("changed-untouched-x31", false, check { target with registers := target.registers.set 31 1 } header rows),
   ("changed-untouched-ram", false, check { target with memory := target.memory.write 65544 1 } header rows),
   ("missing-bank-terminal", false, check target header (rows.filter (fun row => row.1 != resourceStart + 2))),
   ("empty-identity", true, check source.sail.memorySnapshot identityHeader identityRows)]

end SP1CleanTest.Alignment.Core.HostFinalMemory.Fixture
