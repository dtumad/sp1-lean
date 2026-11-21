import SP1Clean.Export.InstalledAssembly
import SP1Clean.Proofs.Completeness.OrdinaryObservationHistory
import ToClean.Air.ChannelRegistry
import ToClean.Air.TableBuild
import SP1CleanTest.Core.StaticMembership

/-! # Finite comparison inputs for the installed SP1 assembly

These helpers supply component inputs for the released-SP1 comparison fixtures.
-/

namespace SP1CleanTest.Alignment.InstalledAssembly

open Circuit Air.Flat SP1Clean SP1Clean.Semantics SP1Clean.Soundness SP1Clean.Export.InstalledAssembly

/-- Finish an ordinary fixture step with the Sail bookkeeping observed by the shard verifier.
The fixture supplies the instruction's computed register writes and successor PC. -/
def retiredSnapshot (source : SailSnapshot) (registers : SailRegisterFile.Map) (nextPC : BitVec 64) :
    SailSnapshot :=
  let enabled := retirementEnabled source.skeleton
  let counter := (source.registers.get? .minstret).getD 0
  let updated := registers.insert .PC nextPC |>.insert .nextPC nextPC
    |>.insert .minstret (counter + if enabled then 1 else 0)
    |>.insert .minstret_increment enabled
    |>.insert .mip (TryStepReduction.refreshedMip source.skeleton)
    |>.insert .written_event_index none
  { source with registers := updated }

/-- One consumer input at its actual physical table position. -/
structure Seed where
  /-- Position in the complete installed physical inventory. -/
  table : ℕ
  /-- Exact input cells for the selected component. -/
  cells : List Fp

/-- Construct a consumer seed from its physical position and input cells. -/
def Seed.ofCells (table : ℕ) (cells : List Fp) : Seed := ⟨table, cells⟩

/-- Decode only after validating the seed's exact input width. -/
def Seed.input (seed : Seed) (component : Component Fp) : component.Input Fp :=
  fromElements (Vector.ofFn fun index => seed.cells[index.val]?.getD 0)

/-- Finite fixture construction uses the same component interface as native witnesses. -/
def Seed.build (seed : Seed) (component : Component Fp) (data : ProverData Fp) : Array Fp :=
  component.buildRow (seed.input component) data (ProverHint.empty Fp)

/-- No seed may name an absent/fixed table or silently truncate an input row. -/
def seedValid (tables : List (Component Fp)) (seed : Seed) : Bool :=
  match tables[seed.table]? with
  | none => false
  | some component => StaticMembership.acceptsSeed component && seed.cells.length == component.rowOffset

/-- Recover the active receipts from the physical instruction rows, then build the ordered
observation inputs and the one terminal selected by the supplied snapshots. -/
def withObservationSeeds (context : Context) (seeds : List Seed) : Except String (List Seed) := do
  let tables := (assembly context).tables
  let observationNames := (Soundness.OrdinaryObservation.tables (p := SP1Prime)).map (·.circuit.name)
  let receiptName := (InstructionReceipt.channel (p := SP1Prime)).name
  let data := ProverData.empty Fp
  let mut receipts : List (Channels.StateMsg Fp) := []
  for seed in seeds do
    let some component := tables[seed.table]? | throw "invalid physical table position"
    unless seedValid tables seed do throw "invalid component input"
    if observationNames.contains component.circuit.name then throw "observation inputs are derived from the physical receipts"
    if component.circuit.channelsWithRequirements.any (·.name == receiptName) then
      let row := seed.build component data
      for interaction in component.operations.interactionValues (Environment.fromArray row data) do
        if interaction.channel.name == receiptName && interaction.direction == .push && interaction.mult != 0 then
          unless interaction.mult == 1 do throw "instruction receipt multiplicity must be one"
          if width : interaction.msg.size = size Channels.StateMsg then
            receipts := fromElements (M := Channels.StateMsg) ⟨interaction.msg, width⟩ :: receipts
          else throw "invalid instruction receipt width"
  let sorted := receipts.mergeSort (fun left right => Semantics.StateMsg.timeNat left ≤ Semantics.StateMsg.timeNat right)
  unless (sorted.map Semantics.StateMsg.timeNat).Nodup do throw "duplicate ordinary receipt clock"
  let (inputs, previous) := SP1Clean.OrdinaryObservation.historyFromReceipts
    (SP1Clean.OrdinaryObservation.startFor context.source.sail) sorted
  let mode := SP1Clean.OrdinaryObservation.Mode.of context.source.sail context.target.sail
  let consumer := tables.findIdx (·.circuit.name == (Soundness.OrdinaryObservation.consumer (p := SP1Prime)).circuit.name)
  let terminal := tables.findIdx (·.circuit.name == SP1Clean.OrdinaryObservation.terminalName mode)
  let active := inputs.map fun input =>
    Seed.ofCells consumer (toElements (SP1Clean.OrdinaryObservation.activeRow input)).toList
  return seeds ++ active ++ [⟨terminal, (toElements (SP1Clean.OrdinaryObservation.terminalInput previous)).toList⟩]

/-- One complete register/RAM message, with canonical address and value limbs. -/
def memoryRecord (address clock : ℕ) (value : BitVec 64) : Channels.MemoryMsg Fp :=
  let key := Address.ofNat (p := SP1Prime) address
  ⟨0, clock, key[0], key[1], key[2], Target.bitVecToWord value⟩

/-- Ordered source/final register records and exact target checks shared by host fixtures. -/
def registerSeeds (context : Context) (registers : List (ℕ × ℕ)) : List Seed :=
  (registers.foldl (fun (acc : ℕ × List Seed) (address, clock) =>
    let index := BitVec.ofNat 5 address
    let record := memoryRecord address clock (context.target.sail.memorySnapshot.read (.reg index))
    let initial := OrderedSnapshotProvider.populate
      (SnapshotRegisterProvider.populate context.source.sail.memorySnapshot index) acc.1 address
    let final := OrderedMemoryProvider.populate record acc.1 address
    let selected : Fp := if Semantics.MemLoc.reg index ∈ context.source.sail.memorySnapshot.changes context.target.sail.memorySnapshot then 1 else 0
    (address + 1, acc.2 ++ [⟨0, (toElements initial).toList⟩, ⟨3, (toElements final).toList⟩,
      ⟨94, (toElements (M := FinalRegisterCheck.RowInput)
        ((⟨record, selected⟩, 1) : FinalRegisterCheck.RowInput Fp)).toList⟩])) (0, [])).2

/-- An empty segment still closes both ordered inventories, both banks and public Exit.
Positions are resolved from actual component names and validated before generation. -/
def emptyConsumers (context : Context) : List Seed :=
  let tables := (assembly context).tables
  let final := OrderedMemoryEnsemble.endKey (p := SP1Prime)
  let ordered := toElements (OrderedBoundaryEnd.populate (Vector.replicate 4 0) final) |>.toList
  let bank (deferred : Bool) := toElements (HostCommitBoundary.start
    (HostCommitEnsemble.sourceValues (p := SP1Prime) deferred context.source.host)) |>.toList
  [(OrderedBoundaryEnd.circuit (p := SP1Prime) SnapshotMemoryEnsemble.channelName final |>.name, ordered),
   (OrderedBoundaryEnd.circuit (p := SP1Prime) OrderedFinalProvider.channelName final |>.name, ordered),
   ((HostCommitBoundary.terminal (p := SP1Prime) false).name, bank false),
   ((HostCommitBoundary.terminal (p := SP1Prime) true).name, bank true),
   ((HaltPaddingChip.circuit (p := SP1Prime)).name, List.replicate (size HaltChip.Inputs) 0)].map
    fun (name, cells) =>
      ⟨tables.findIdx (fun component => component.circuit.name == name), cells⟩

end SP1CleanTest.Alignment.InstalledAssembly
