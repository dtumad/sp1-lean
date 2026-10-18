import SP1CleanTest.Alignment.Audit.BranchCompilerRoundTrip
import SP1CleanTest.Alignment.Support.InstalledAssembly
import ToClean.Air.EnsembleBuild
import ToClean.Air.FiniteLookup
import ToClean.Air.ChannelRegistry
import SP1CleanTest.Core.StaticMembership

/-! # Compiler-derived branch witness for the complete local host assembly

The only instruction input is extracted from `BranchCompilerRoundTrip.compiled`.
Boundary records and preprocessing rows are derived from its actual physical interactions.
-/

namespace SP1Clean.Audit.BranchEnsemble

open SP1CleanTest.Alignment.InstalledAssembly
open Circuit Air.Flat SP1Clean.Model.Core SP1Clean.Soundness SP1Clean.TraceGen SP1Clean.Semantics

/-- The native SP1 field. -/
abbrev Fp := ZMod SP1Prime
/-- The previously checked semantic branch/compiler fixture. -/
abbrev image := BranchCompilerRoundTrip.image
/-- Canonical finite source snapshot for the same official Sail state. -/
def source : ExecutionSnapshot where
  sail := { registers := (Target.configuredState 65536).regs, memory := image.initialMemory }
  host := {}
  clock := 1
/-- Branches preserve the complete register and RAM snapshot. -/
def target : MemorySnapshot := source.sail.memorySnapshot
/-- The branch fixture's instance data for the shared complete installed assembly. -/
def context (target : MemorySnapshot) : Context where
  image := image
  source := source
  target := target
  finalHints := SP1Clean.HostHintQueueBoundary.initial []
  finalHost := source.host
/-- Public ordinary-step endpoints, not a HALT endpoint claim. -/
def header : SP1PublicIO Fp where
  init_clk_0_16 := 1
  init_clk_16_24 := 0
  init_clk_24_32 := 0
  init_clk_32_48 := 0
  init_pc0 := 0
  init_pc1 := 1
  init_pc2 := 0
  final_clk_0_16 := 9
  final_clk_16_24 := 0
  final_clk_24_32 := 0
  final_clk_32_48 := 0
  final_pc0 := 4092
  final_pc1 := 1
  final_pc2 := 0
  exit_code := 0
  is_execution_shard := 1
  committed_value_digest := Vector.replicate 32 0
/-- Empty execution preserves the complete source clock and PC. -/
def identityHeader : SP1PublicIO Fp :=
  { header with
    final_clk_0_16 := header.init_clk_0_16,
    final_clk_16_24 := header.init_clk_16_24, final_clk_24_32 := header.init_clk_24_32,
    final_clk_32_48 := header.init_clk_32_48, final_pc0 := header.init_pc0,
    final_pc1 := header.init_pc1, final_pc2 := header.init_pc2 }
/-- Empty generation input; semantic data is derived from the committed physical rows. -/
def data : ProverData Fp := BranchCompilerRoundTrip.data
/-- Evaluate a field word from a natural boundary key. -/
def word (value : ℕ) : Word Fp := Target.bitVecToWord (BitVec.ofNat 64 value)
/-- The sole active instruction uses the actual compiler payload. -/
def branchSeed : Seed :=
  ⟨18, (toElements (BranchCompilerRoundTrip.event.toBranchInputs (p := SP1Prime))).toList⟩
/-- Concrete interaction messages, including zero multiplicities, named for the authenticated export inventory. -/
abbrev Ledger := List (String × List Fp × Fp)
/-- Extract actual row operations without replacing their expression evaluation. -/
def rowLedger (component : Component Fp) (row : Array Fp) : Ledger :=
  let env := Environment.fromArray row data
  component.rowOperations.interactions.map fun interaction =>
    (interaction.channel.name, (interaction.msg.map env).toList, env interaction.mult)
/-- Actual compiler-built branch interactions; all providers are derived from this ledger. -/
def branchLedger : Ledger := rowLedger BranchChip.component BranchCompilerRoundTrip.row
/-- Decode Memory records of the requested polarity from the instruction's actual ledger. -/
def memoryDemand (positive : Bool) : List (Channels.MemoryMsg Fp) :=
  (branchLedger.filter fun entry => entry.1 == "SP1Memory" &&
    entry.2.2 == (if positive then 1 else -1)).map fun entry =>
      fromElements (Vector.ofFn fun index => entry.2.1[index.val]?.getD 0)
/-- Canonical address order supplies ordered boundary links without duplicate authentication. -/
def orderedMemory (positive : Bool) : List (Channels.MemoryMsg Fp) :=
  (memoryDemand positive).mergeSort (fun a b => a.addr0.val ≤ b.addr0.val)
/-- Source authentication records follow the actual initial register pulls. -/
def sourceSeeds : List Seed :=
  ((orderedMemory false).foldl (fun (acc : ℕ × List Seed) record =>
    let address := record.addr0.val
    let input := OrderedSnapshotProvider.populate
      (SnapshotRegisterProvider.populate source.sail.memorySnapshot (BitVec.ofNat 5 address))
      acc.1 address
    (address + 1, acc.2 ++ [Seed.ofCells 0 (toElements input).toList])) (0, [])).2
/-- Complete final records follow the actual latest register pushes. -/
def finalSeeds : List Seed :=
  ((orderedMemory true).foldl (fun (acc : ℕ × List Seed) record =>
    let address := record.addr0.val
    let input := OrderedMemoryProvider.populate record acc.1 address
    (address + 1, acc.2 ++ [Seed.ofCells 3 (toElements input).toList])) (0, [])).2
/-- Every published final receipt is checked against the fixed complete target snapshot. -/
def validatorSeeds : List Seed :=
  (orderedMemory true).map fun record =>
    Seed.ofCells 90 (toElements (⟨record, 0⟩ : FinalRegisterCheck.Inputs Fp)).toList
/-- Terminate the actual finite ordered register inventory. -/
def terminal (table : ℕ) (records : List (Channels.MemoryMsg Fp)) : Seed :=
  let previous := records.foldl (fun _ record => record.addr0.val + 1) 0
  Seed.ofCells table (toElements (OrderedBoundaryEnd.populate (word previous)
    (OrderedMemoryEnsemble.endKey (p := SP1Prime)))).toList
/-- Unchanged host-bank endpoints, physically present even though this step makes no host call. -/
def hostTerminals : List Seed :=
  [88, 89].map fun index =>
    Seed.ofCells index (toElements (HostCommitBoundary.initial (p := SP1Prime))).toList
/-- All non-Byte rows use the compiler and its demanded authentication inventory. -/
def consumerSeeds : List Seed :=
  [branchSeed] ++ sourceSeeds ++ finalSeeds ++ validatorSeeds ++
    [terminal 2 (orderedMemory false), terminal 5 (orderedMemory true)] ++ hostTerminals ++
    [Seed.ofCells 57 (List.replicate (size HaltChip.Inputs) 0)]
/-- Evaluate one seed, failing closed if its component position is absent. -/
def seedLedger? (target : MemorySnapshot) (seed : Seed) : Option Ledger :=
  match (assembly (context target)).tables[seed.table]? with
  | none => none
  | some component => if component.fixedColumns.isSome || seed.cells.length != component.rowOffset then none else
      some (rowLedger component (seed.build component data))
/-- Demand one actual Byte or Range provider row, rejecting unsupported message shapes. -/
def byteSeed? (entry : String × List Fp × Fp) : Option (Option Seed) :=
  if entry.1 != "SP1Byte" || entry.2.2 == 0 then some none else
  match entry.2.1 with
  | [opcode, a, b, c] =>
    if opcode == 3 then some (some (Seed.ofCells 32 [b, c, -entry.2.2]))
    else if opcode == 4 then some (some (Seed.ofCells 37 [b, c, -entry.2.2]))
    else if opcode == 5 then some (some (Seed.ofCells 33 [b, -entry.2.2]))
    else if opcode == 6 && b.val < 17 then some (some (Seed.ofCells (38 + b.val) [a, -entry.2.2]))
    else none
  | _ => none
/-- Extend all physical consumer demand, including the public verifier, with real providers. -/
def seeds? (target : MemorySnapshot) (input : SP1PublicIO Fp) (consumers : List Seed) :
    Option (List Seed) := do
  let ledgers ← consumers.mapM (seedLedger? target)
  let verifier := (assembly (context target)).verifierOperations.interactionValues
    (Environment.fromInput input data) |>.map fun interaction =>
      (interaction.channel.name, interaction.msg.toList, interaction.mult)
  let providers ← (verifier ++ ledgers.flatten).mapM byteSeed?
  let generated := providers.filterMap id
  if generated.all (seedValid (assembly (context target)).tables) then some (consumers ++ generated) else none
/-- Every table remains installed, including all fixed membership rows at their actual counts. -/
def builtTables (target : MemorySnapshot) (seeds : List Seed)
    (bounded : seeds.length ≤ UInt64.size) : List (Table Fp) :=
  let components := (assembly (context target)).tables
  let inputs := fun index => (seeds.filter (fun seed => seed.table == index)).map (·.cells)
  let channels := [(source.sail.memorySnapshot.registerTable (p := SP1Prime)).channel.name,
    (FinalRegisterValue.membership (p := SP1Prime) target).channel.name,
    "sp1.native.initial_memory", "sp1.native.target_memory", "SP1Program", "sp1.native.write_permission",
    "sp1.native.hint_node", "sp1.native.hint_word"]
  let ledger := SP1CleanTest.StaticMembership.demandLedger components inputs channels data (ProverHint.empty Fp)
  SP1CleanTest.StaticMembership.buildTables components inputs ledger data (ProverHint.empty Fp)
    (fun index => by
      dsimp only [inputs]
      rw [List.length_map]
      exact (List.length_filter_le _ _).trans bounded)

/-- All built tables retain the assembly's original component identities and order. -/
theorem builtTables_components (target : MemorySnapshot) (seeds : List Seed)
    (bounded : seeds.length ≤ UInt64.size) :
    (builtTables target seeds bounded).map (·.component) = (assembly (context target)).tables := by
  unfold builtTables
  exact SP1CleanTest.StaticMembership.buildTables_components (F := Fp) ..

/-- Building rows never changes the complete 94-table host inventory. -/
theorem builtTables_length (target : MemorySnapshot) (seeds : List Seed)
    (bounded : seeds.length ≤ UInt64.size) :
    (builtTables target seeds bounded).length = 94 := by
  simp only [builtTables, SP1CleanTest.StaticMembership.buildTables, List.length_ofFn]
  rfl
/-- The exact raw Clean witness on the original, unmodified host assembly. -/
def witness (target : MemorySnapshot) (input : SP1PublicIO Fp) (seeds : List Seed)
    (bounded : seeds.length ≤ UInt64.size) :
    EnsembleWitness (assembly (context target)) :=
  EnsembleWitness.ofTables _ (builtTables target seeds bounded) input (builtTables_components target seeds bounded)

/-- The finite source is exactly the source of the official Sail/compiler regression. -/
theorem source_realizes : source.realize = ⟨BranchCompilerRoundTrip.source, {}, 1⟩ := rfl

/-- Source providers are bound to all registers and every native-address memory byte. -/
theorem source_memory_realizes : source.sail.memorySnapshot.Realizes BranchCompilerRoundTrip.source := by
  exact source.sail.memorySnapshot_realizes (Target.cfgState_init 65536)

/-- The complete target snapshot realizes the same normally retiring official Sail target. -/
theorem target_realizes : target.Realizes BranchCompilerRoundTrip.target := by
  constructor
  · intro index
    have unchanged := BranchCompilerRoundTrip.target_effect.regs
    change ∀ index, BranchCompilerRoundTrip.target.get_reg? index =
      BranchCompilerRoundTrip.source.get_reg? index at unchanged
    exact (unchanged index).trans (source_memory_realizes.1 index)
  · intro address bound
    exact (BranchCompilerRoundTrip.target_effect.mem.1 rfl address).trans
      (source_memory_realizes.2 address bound)

/-- The physical branch seed preserves the exact input and compiler hint of the earlier local row. -/
theorem branchSeed_build : branchSeed.build BranchChip.component data = BranchCompilerRoundTrip.row := by
  have input : branchSeed.input BranchChip.component =
      BranchCompilerRoundTrip.event.toBranchInputs (p := SP1Prime) := by
    unfold Seed.input branchSeed
    conv_rhs => rw [← ProvableType.fromElements_toElements
      (BranchCompilerRoundTrip.event.toBranchInputs (p := SP1Prime))]
    congr 1
    ext index bound
    simp only [Vector.getElem_ofFn, Vector.getElem?_toList]
    have bound' : index < size BranchChip.Inputs := bound
    rw [Vector.getElem?_eq_getElem bound']
    rfl
  unfold Seed.build
  rw [input]
  rfl

end SP1Clean.Audit.BranchEnsemble
