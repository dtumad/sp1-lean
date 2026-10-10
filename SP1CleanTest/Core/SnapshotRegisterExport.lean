import Clean.Air.Extraction.Rust
import SP1Clean.Proofs.Chips.SnapshotRegisterProvider
import SP1Clean.Model.SP1Field
import ToClean.Air.EnsembleCheck

/-! # Built-in export of source-register authentication

Exercise the production sparse Memory provider and its typed verifier-fixed membership table
together. Clean owns row allocation, multiplicity updates, lowering and Rust rendering. A second
ensemble checks unused fixed rows without introducing a padding row on the sparse Memory bus.
The nonzero local snapshot is independent of SP1's boot-only register initialization.
-/

namespace SP1CleanTest.Core.SnapshotRegisterExport

open Air.Flat Circuit SP1Clean SP1Clean.Model.Core

abbrev Fp := ZMod SP1Prime
abbrev Requests := ProvableVector RegisterSnapshotRow 2

/-- Nonzero values exercise every limb; architectural x0 still reads as zero. -/
def snapshot : MemorySnapshot :=
  ⟨Vector.ofFn (fun index => BitVec.ofNat 64 (index.val * 0x123456789abcdef)), ⟨[]⟩⟩

/-- The production source table, with all 32 rows supplied by the fixed-column IR. -/
def membership : Component Fp := snapshot.registerTable.component

/-- The public boundary requests two complete zero-time Memory records. -/
def verifier : Verifier.Program Fp Requests where
  main input := do
    Verifier.pull Channels.memoryChannel (SnapshotRegisterProvider.message input[0])
    Verifier.pull Channels.memoryChannel (SnapshotRegisterProvider.message input[1])

/-- Sparse Memory rows remain separate from the complete fixed register inventory. -/
def ensemble : Ensemble Fp Requests where
  tables := [{ circuit := SnapshotRegisterProvider.circuit snapshot }, membership]
  unique_names := by
    simp [membership, StaticTable.component, StaticTable.provider,
      SnapshotRegisterProvider.circuit, MemorySnapshot.registerTable, StaticTable.ofRows]
  channels := [Channels.memoryChannel.toRaw, snapshot.registerTable.channel.toRaw]
  verifier := verifier

/-- Only the count column is mutable in the preallocated membership table. -/
def membershipMode : WitnessGeneration.Mode Fp := .preallocated {
  rows := 32
  input := .ofFExprs #v[.const 0]
  input_valid := by rfl
  handlers := [{ interaction := 0, column := 5 }]
}

/-- Allocate one sparse row per Memory occurrence, including repeated messages. -/
def config : WitnessGeneration.Config Fp unit where
  modes := [.demand {
    channel := (Channels.memoryChannel (p := SP1Prime)).name
    direction := .pull
    aggregation := .perOccurrence
    input := ⟨[.message 2, .message 5, .message 6, .message 7, .message 8]⟩
  }, membershipMode]
  padding := [{ input := #[0, 0, 0, 0, 0] },
    { input := #[0, 0, 0, 0, 0, 0], minimumRows := 32 }]
  fuel := 128

/-- Check complete raw constraints and both ledgers, retaining zero-count occurrences. -/
def description : Air.Flat.EnsembleCheck ensemble where
  lookups := []
  lookups_unique := by simp
  lookups_complete := by
    simp [ensemble, membership, Component.lookups_eq, Component.rowOperations,
      StaticTable.component, StaticTable.provider, SnapshotRegisterProvider.circuit,
      SnapshotRegisterProvider.main, circuit_norm]
  channels_unique := by
    simp [ensemble, Channel.toRaw, Channels.memoryChannel, StaticTable.channel,
      MemorySnapshot.registerTable, StaticTable.ofRows]
  channels_complete := by
    simp [ensemble, membership, Component.interactions_eq, Component.rowOperations,
      StaticTable.component, StaticTable.provider, SnapshotRegisterProvider.circuit,
      SnapshotRegisterProvider.main, circuit_norm]
  verifier_channels_complete := by
    simp [ensemble, Ensemble.verifierOperations, verifier,
      Verifier.Program.circuitOperations, circuit_norm]

/-- No sparse consumer is installed when no Memory record is requested. -/
def emptyEnsemble : Ensemble Fp unit where
  tables := [membership]
  unique_names := by simp
  channels := [snapshot.registerTable.channel.toRaw]

def emptyConfig : WitnessGeneration.Config Fp unit where
  modes := [membershipMode]
  padding := [{ input := #[0, 0, 0, 0, 0, 0], minimumRows := 32 }]
  fuel := 1

def emptyDescription : Air.Flat.EnsembleCheck emptyEnsemble where
  lookups := []
  lookups_unique := by simp
  lookups_complete := by
    simp [emptyEnsemble, membership, Component.lookups_eq, Component.rowOperations,
      StaticTable.component, StaticTable.provider, circuit_norm]
  channels_unique := by simp [emptyEnsemble]
  channels_complete := by
    simp [emptyEnsemble, membership, Component.interactions_eq, Component.rowOperations,
      StaticTable.component, StaticTable.provider, circuit_norm]
  verifier_channels_complete := by
    simp [emptyEnsemble, Ensemble.verifierOperations, Verifier.Program.circuitOperations,
      Verifier.Program.empty, circuit_norm]

def generate (requests : Requests Fp) : Except String (EnsembleWitness ensemble) :=
  WitnessGeneration.generate ensemble config requests ()

def generateEmpty : Except String (EnsembleWitness emptyEnsemble) :=
  WitnessGeneration.generate emptyEnsemble emptyConfig () ()

def rustExports : List (String × Except String String) :=
  [("snapshot_registers.rs", Extraction.Rust.ensembleToRust "SnapshotRegisters" ensemble config),
   ("snapshot_registers_empty.rs",
     Extraction.Rust.ensembleToRust "EmptySnapshotRegisters" emptyEnsemble emptyConfig)]

/-- All indices, one repeated demand, and independently forged indices and limbs. -/
def cases : List (String × Requests Fp × Bool) :=
  (List.range 32).map (fun index =>
    (s!"register-{index}",
      #v[snapshot.registerRow (BitVec.ofNat 5 index), snapshot.registerRow 31], true)) ++
  [("repeated", #v[snapshot.registerRow 5, snapshot.registerRow 5], true)] ++
  (List.range 4).map (fun limb =>
    let row := snapshot.registerRow (p := SP1Prime) 5
    (s!"forged-limb-{limb}",
      #v[{ row with value := row.value.set! limb (row.value[limb]! + 1) }, snapshot.registerRow 31],
      false)) ++
  ([6, 32, 0] : List Nat).map (fun index =>
    let row := snapshot.registerRow (p := SP1Prime) 5
    (s!"forged-index-{index}", #v[{ row with index := index }, snapshot.registerRow 31], false))

/-- Independent raw checks validate successful generation and reject every forged request. -/
theorem cases_correct : cases.all (fun (_, requests, expected) =>
    (match generate requests with
    | .ok witness => description.checkWitness SP1Prime witness
    | .error _ => false) == expected) = true := by native_decide

/-- An unused fixed table keeps every row and every zero-count interaction. -/
theorem empty_correct :
    (generateEmpty.map fun witness =>
      emptyDescription.checkWitness SP1Prime witness &&
      witness.tables.length == 1 && witness.interactions.length == 32 &&
      witness.interactions.all (·.mult == 0)) = .ok true := by native_decide

theorem exports_succeed : rustExports.all (fun entry => entry.2.isOk) = true := by native_decide

end SP1CleanTest.Core.SnapshotRegisterExport
