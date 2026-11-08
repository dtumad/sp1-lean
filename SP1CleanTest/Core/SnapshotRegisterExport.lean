import SP1CleanTest.Core.ComponentExport
import SP1Clean.Proofs.Chips.SnapshotRegisterProvider
import SP1Clean.Native.Operations.FinalRegisterValue
import SP1Clean.Model.SP1Field
import ToClean.Air.EnsembleCheck

/-! # Built-in export of source and target register authentication

Exercise the production sparse source Memory provider and target receipt consumer with their
separate verifier-fixed membership tables. Clean owns row allocation, multiplicity updates, lowering and Rust rendering. A second
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
def membership : Component Fp := snapshot.registerTable.component (by
  have padded := (snapshot.registerTable (p := SP1Prime)).height_lt_double
  rw [snapshot.registerTable_length] at padded
  norm_num [UInt64.size] at *
  omega)

/-- The public boundary requests two complete zero-time Memory records. -/
def verifier : Verifier.Program Fp Requests where
  Spec _ _ := True
  soundness := by intros; trivial
  main input := do
    Verifier.pull Channels.memoryChannel (SnapshotRegisterProvider.message input[0])
    Verifier.pull Channels.memoryChannel (SnapshotRegisterProvider.message input[1])

/-- Sparse Memory rows remain separate from the complete fixed register inventory. -/
def ensemble : Ensemble Fp Requests where
  tables := [{
    circuit := SnapshotRegisterProvider.circuit snapshot
    Assumptions := (SnapshotRegisterProvider.circuit snapshot).Assumptions
    generation := .demand {
      channel := Channels.memoryChannel
      trigger := .pull
      input message := pure ⟨.witness (.expr message.addr0),
        message.value.map (fun value => .witness (.expr value))⟩ } }, membership]
  unique_names := by
    simp [membership, StaticTable.component, StaticTable.provider,
      SnapshotRegisterProvider.circuit, MemorySnapshot.registerTable, StaticTable.ofRows]
  channels := [Channels.memoryChannel.toRaw, snapshot.registerTable.channel.toRaw]
  verifier := verifier
  unique_channel_names := by
    simp [Channel.toRaw, Channels.memoryChannel, StaticTable.channel,
      MemorySnapshot.registerTable, StaticTable.ofRows]
  tables_channels := by
    intro component member channel used
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · change channel ∈ [snapshot.registerTable.channel.toRaw, Channels.memoryChannel.toRaw] at used
      simp only [List.mem_cons, List.not_mem_nil, or_false] at used ⊢
      tauto
    · change channel ∈ [snapshot.registerTable.channel.toRaw] at used
      exact List.mem_cons_of_mem _ used
  verifier_channels := by
    intro channel member
    simp [Verifier.Program.channels, Verifier.Program.channelsWithGuarantees,
      Verifier.Program.channelsWithRequirements, Verifier.Program.operations, verifier,
      circuit_norm] at member
    simp [member]

/-- Check complete raw constraints and both ledgers, retaining zero-count occurrences. -/
def description : Air.Flat.EnsembleCheck ensemble where
  lookups := []
  lookups_unique := by simp
  lookups_complete := by
    simp [ensemble, membership, Component.lookups_eq, Component.rowOperations,
      StaticTable.component, StaticTable.provider, SnapshotRegisterProvider.circuit,
      SnapshotRegisterProvider.main, circuit_norm]

/-- No sparse consumer is installed when no Memory record is requested. -/
def emptyEnsemble : Ensemble Fp unit where
  tables := [membership]
  unique_names := by simp
  channels := [snapshot.registerTable.channel.toRaw]
  unique_channel_names := by simp
  tables_channels := by
    intro component member
    obtain rfl := List.mem_singleton.mp member
    change [_] ⊆ [_]
    exact List.Subset.refl _
  verifier_channels := by simp [Verifier.Program.channels, circuit_norm]

def emptyDescription : Air.Flat.EnsembleCheck emptyEnsemble where
  lookups := []
  lookups_unique := by simp
  lookups_complete := by
    simp [emptyEnsemble, membership, Component.lookups_eq, Component.rowOperations,
      StaticTable.component, StaticTable.provider, circuit_norm]

def generate (requests : Requests Fp) : Except String (EnsembleWitness ensemble) :=
  WitnessGeneration.generate ensemble 128 requests () |>.mapError toString

def generateEmpty : Except String (EnsembleWitness emptyEnsemble) :=
  WitnessGeneration.generate emptyEnsemble 1 () () |>.mapError toString

def rustExports : List (String × Except String String) :=
  [("snapshot_registers.rs", Backends.Plonky3.Print.ensembleToRust (ComponentExport.fixture ensemble) 128),
   ("snapshot_registers_empty.rs",
     Backends.Plonky3.Print.ensembleToRust (ComponentExport.fixture emptyEnsemble) 1)]

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
    | .ok witness => description.checkWitness witness
    | .error _ => false) == expected) = true := by native_decide

/-- An unused fixed table keeps every row and every zero-count interaction. -/
theorem empty_correct :
    (generateEmpty.map fun witness =>
      emptyDescription.checkWitness witness &&
      witness.tables.length == 1 && witness.interactions.length == 32 &&
      witness.interactions.all (·.mult == 0)) = .ok true := by native_decide

theorem exports_succeed : rustExports.all (fun entry => entry.2.isOk) = true := by native_decide

namespace Target

abbrev Requests := ProvableVector Channels.MemoryMsg 2

/-- The target has its own fixed channel, independent of source membership. -/
def membership : Component Fp := (FinalRegisterValue.membership snapshot).component
      (FinalRegisterValue.membership_height_lt_uint64 snapshot)

/-- Public final receipts retain both clock limbs and all address/value limbs. -/
def verifier : Verifier.Program Fp Requests where
  Spec _ _ := True
  soundness := by intros; trivial
  main input := do
    Verifier.push (FinalMemoryValue.channel false) input[0]
    Verifier.push (FinalMemoryValue.channel false) input[1]

def ensemble : Ensemble Fp Requests where
  tables := [{
    circuit := FinalRegisterValue.circuit snapshot
    Assumptions := (FinalRegisterValue.circuit snapshot).Assumptions
    generation := .demand {
      channel := FinalMemoryValue.channel false
      trigger := .push
      input message := pure (fromElements (M := Channels.MemoryMsg) ((toElements (M := Channels.MemoryMsg) message).map
        (fun value => .witness (.expr value)))) } }, membership]
  unique_names := by
    simp [membership, StaticTable.component, StaticTable.provider,
      FinalRegisterValue.circuit, FinalRegisterValue.membership]
  channels := [(FinalMemoryValue.channel false).toRaw,
    (FinalRegisterValue.membership snapshot).channel.toRaw]
  verifier := verifier
  unique_channel_names := by
    simp [Channel.toRaw, FinalMemoryValue.channel, StaticTable.channel,
      FinalRegisterValue.membership]
  tables_channels := by
    intro component member channel used
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · change channel ∈ (FinalRegisterValue.circuit snapshot).channels at used
      rw [GeneralFormalCircuit.channels,
        show (FinalRegisterValue.circuit snapshot).channelsWithGuarantees =
          (FinalRegisterValue.elaborated snapshot).channelsWithGuarantees from rfl,
        show (FinalRegisterValue.circuit snapshot).channelsWithRequirements =
          [(FinalMemoryValue.channel false).toRaw] from rfl] at used
      simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at used
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      tauto
    · change channel ∈ [(FinalRegisterValue.membership snapshot).channel.toRaw] at used
      exact List.mem_cons_of_mem _ used
  verifier_channels := by
    intro channel member
    simp [Verifier.Program.channels, Verifier.Program.channelsWithGuarantees,
      Verifier.Program.channelsWithRequirements, Verifier.Program.operations, verifier,
      circuit_norm] at member
    simp [member]

def description : Air.Flat.EnsembleCheck ensemble where
  lookups := []
  lookups_unique := by simp
  lookups_complete := by
    simp [ensemble, membership, Component.lookups_eq, Component.rowOperations,
      StaticTable.component, StaticTable.provider, FinalRegisterValue.circuit,
      FinalRegisterValue.main, circuit_norm]

def emptyEnsemble : Ensemble Fp unit where
  tables := [membership]
  unique_names := by simp
  channels := [(FinalRegisterValue.membership snapshot).channel.toRaw]
  unique_channel_names := by simp
  tables_channels := by
    intro component member
    obtain rfl := List.mem_singleton.mp member
    change [_] ⊆ [_]
    exact List.Subset.refl _
  verifier_channels := by simp [Verifier.Program.channels, circuit_norm]

def emptyDescription : Air.Flat.EnsembleCheck emptyEnsemble where
  lookups := []
  lookups_unique := by simp
  lookups_complete := by
    simp [emptyEnsemble, membership, Component.lookups_eq, Component.rowOperations,
      StaticTable.component, StaticTable.provider, circuit_norm]

def generate (requests : Requests Fp) : Except String (EnsembleWitness ensemble) :=
  WitnessGeneration.generate ensemble 128 requests () |>.mapError toString

def generateEmpty : Except String (EnsembleWitness emptyEnsemble) :=
  WitnessGeneration.generate emptyEnsemble 1 () () |>.mapError toString

def rustExports : List (String × Except String String) :=
  [("target_registers.rs", Backends.Plonky3.Print.ensembleToRust (ComponentExport.fixture ensemble) 128),
   ("target_registers_empty.rs",
     Backends.Plonky3.Print.ensembleToRust (ComponentExport.fixture emptyEnsemble) 1)]

def record (index clock : Nat) : Channels.MemoryMsg Fp :=
  { SnapshotRegisterProvider.message (snapshot.registerRow (BitVec.ofNat 5 index)) with
    clk_high := (clock / 2 ^ 24 : Nat), clk_low := (clock % 2 ^ 24 : Nat) }

/-- Cover every index, repeated full receipts, forged values/indices and malformed addresses. -/
def cases : List (String × Requests Fp × Bool) :=
  let last := record 31 (2 * 2 ^ 24 + 31)
  let row := record 5 (2 ^ 24 + 5)
  (List.range 32).map (fun index =>
    (s!"register-{index}", #v[record index (2 ^ 24 + index), last], true)) ++
  [("repeated", #v[row, row], true)] ++
  (List.range 4).map (fun limb =>
    (s!"forged-limb-{limb}",
      #v[{ row with value := row.value.set! limb (row.value[limb]! + 1) }, last], false)) ++
  ([6, 32, 0] : List Nat).map (fun index =>
    (s!"forged-index-{index}", #v[{ row with addr0 := index }, last], false)) ++
  [("forged-addr1", #v[{ row with addr1 := 1 }, last], false),
   ("forged-addr2", #v[{ row with addr2 := 1 }, last], false)]

/-- Generation alone is not acceptance: the independent raw checker also checks assertions. -/
theorem cases_correct : cases.all (fun (_, requests, expected) =>
    (match generate requests with
    | .ok witness => description.checkWitness witness
    | .error _ => false) == expected) = true := by native_decide

theorem empty_correct :
    (generateEmpty.map fun witness =>
      emptyDescription.checkWitness witness &&
      witness.tables.length == 1 && witness.interactions.length == 32 &&
      witness.interactions.all (·.mult == 0)) = .ok true := by native_decide

theorem exports_succeed : rustExports.all (fun entry => entry.2.isOk) = true := by native_decide

end Target

end SP1CleanTest.Core.SnapshotRegisterExport
