import SP1Clean.Proofs.Completeness.InstalledInstructionTables
import SP1Clean.Proofs.Completeness.MixedInstructionBuckets
import SP1Clean.Proofs.Completeness.OrdinaryBucketCapacity

/-! # Installed ordinary tables from one released mixed execution

Stable routing supplies each typed instruction bucket and its timestamped operands. Clean builds
the protected receipt tables and replaces their generation environments with the data derived
from the full inventory. All local checks and raw channel occurrences survive this replacement.
-/

namespace SP1Clean.TraceGen
open Air.Flat Circuit Semantics Machine FormalModel.Shard Soundness

local notation "Fp" => ZMod SP1Prime
local notation "installed" => ProtectedOrdinaryReceipt.component (p := SP1Prime)

namespace InstalledInstructionTables

/-- Reuse the sealed registry descriptor when elaborating its underlying circuit. -/
local instance (id : InstructionChipId) : ProvableType (supportedChipFor (p := SP1Prime) id).kind.Inputs :=
  (supportedChipFor (p := SP1Prime) id).kind.provableInputs

/-- Use the corresponding output layout for the protected circuit. -/
local instance (id : InstructionChipId) : ProvableType (supportedChipFor (p := SP1Prime) id).kind.Cols :=
  (supportedChipFor (p := SP1Prime) id).kind.provableCols

private def Independent (ch : RawChannel Fp) : Prop :=
  ∀ (mult : Fp) (msg : Vector Fp ch.arity) (before after : ProverData Fp),
    ch.Guarantees mult msg before → ch.Guarantees mult msg after

private theorem channels_independent (id : InstructionChipId) :
    ∀ channel ∈ (installed id).circuit.channels, Independent channel := by
  have original (id : InstructionChipId) {ch : RawChannel Fp}
      (member : ch ∈ (supportedChipFor (p := SP1Prime) id).circuit.channels) : Independent ch := by
    have core := sp1Tables_channels_subset _
      (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨id, InstructionChipId.mem_all id, rfl⟩, rfl⟩) member
    simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false] at core
    rcases core with rfl | rfl | rfl | rfl | rfl <;> exact fun _ _ _ _ h => h
  intro ch used
  have names : (installed id).circuit.channels =
      (ProtectedOrdinaryReceipt.provider (p := SP1Prime) id).channels ++ [InstructionReceipt.channel.toRaw] := by
    change _ ++ (_ ++ [_]) = (_ ++ _) ++ [_]
    exact (List.append_assoc ..).symm
  rw [names] at used
  rcases List.mem_append.mp used with member | recent
  · cases id <;> try exact original _ member
    case' storeByte =>
      have req : (StoreByteChip.circuit (p := SP1Prime)).channelsWithRequirements =
          [Channels.stateChannel.toRaw, Channels.memoryChannel.toRaw] := rfl
      change ch ∈ (ProtectedStore.byte (p := SP1Prime)).channels at member
      simp only [GeneralFormalCircuit.channels, ProtectedStore.byte, circuit_norm, req,
        List.mem_cons, List.not_mem_nil, or_false] at member
    case' storeHalf =>
      have req : (StoreHalfChip.circuit (p := SP1Prime)).channelsWithRequirements =
          [Channels.stateChannel.toRaw, Channels.memoryChannel.toRaw] := rfl
      change ch ∈ (ProtectedStore.half (p := SP1Prime)).channels at member
      simp only [GeneralFormalCircuit.channels, ProtectedStore.half, circuit_norm, req,
        List.mem_cons, List.not_mem_nil, or_false] at member
    case' storeWord =>
      have req : (StoreWordChip.circuit (p := SP1Prime)).channelsWithRequirements =
          [Channels.stateChannel.toRaw, Channels.memoryChannel.toRaw] := rfl
      change ch ∈ (ProtectedStore.word (p := SP1Prime)).channels at member
      simp only [GeneralFormalCircuit.channels, ProtectedStore.word, circuit_norm, req,
        List.mem_cons, List.not_mem_nil, or_false] at member
    case' storeDouble =>
      have req : (StoreDoubleChip.circuit (p := SP1Prime)).channelsWithRequirements =
          [Channels.stateChannel.toRaw, Channels.memoryChannel.toRaw] := rfl
      change ch ∈ (ProtectedStore.double (p := SP1Prime)).channels at member
      simp only [GeneralFormalCircuit.channels, ProtectedStore.double, circuit_norm, req,
        List.mem_cons, List.not_mem_nil, or_false] at member
    all_goals
      have listed : ch = Channels.stateChannel.toRaw ∨ ch = Channels.memoryChannel.toRaw ∨
          ch = Channels.byteChannel.toRaw ∨ ch = Channels.programChannel.toRaw ∨ ch = WritePermissionProvider.channel.toRaw := by
        grind only
      rcases listed with rfl | rfl | rfl | rfl | rfl <;> exact fun _ _ _ _ h => h
  · obtain rfl := List.mem_singleton.mp recent
    exact fun _ _ _ _ h => h

/-- Install a constructed table in Clean's canonical data at its physical inventory position. -/
theorem atSlot (id : InstructionChipId) (events : List id.Event)
    (bounded : WitnessGeneration.demandHeight events.length ≤ UInt64.size)
    (valid : ∀ event ∈ events, id.Valid event) (inventory : List (Table Fp))
    (unique : (inventory.map fun t => t.component.circuit.name).Nodup) (publicInput : Array Fp)
    (i : Fin inventory.length)
    (position : inventory[i.val] = table id events (ProverData.empty _) (ProverHint.empty _) bounded) :
    ∃ actual, (withDerivedData inventory unique publicInput)[i.val]? = some actual ∧
      actual.component = installed id ∧ actual.table = inventory[i.val].table ∧
      actual.data = deriveProverData inventory publicInput ∧ actual.Constraints ∧ actual.Guarantees ∧
      ∀ channel, actual.interactionsWith channel = inventory[i.val].interactionsWith channel := by
  let original := inventory[i.val]
  let data := deriveProverData inventory publicInput
  have consistent : data.tables original.component.circuit.name (size original.component.Input) =
      original.rowPrefixes (size original.component.Input) :=
    deriveTables_eq_of_mem inventory unique (List.getElem_mem i.isLt) _
  let actual : Table Fp := { original with data, data_consistent := consistent }
  have component : original.component = installed id := by rw [show original = _ from position]; rfl
  refine ⟨actual, ?_, component, rfl, rfl, ?_, ?_, Table.interactionsWith_setData original data consistent⟩
  · have inside : i.val < (withDerivedData inventory unique publicInput).length := by simp [withDerivedData]
    rw [List.getElem?_eq_getElem inside]
    simp [withDerivedData, actual, original, data]
  · intro row member
    change (original.component).operations.ConstraintsHold (Environment.fromArray row data)
    rw [component]
    apply constraints_at id events _ _ bounded valid
    change row ∈ inventory[i.val].table at member
    rwa [position] at member
  · have shared : actual.interactions = original.interactions :=
      congrArg List.flatten (List.map_congr_left fun row _ =>
        Operations.interactionValues_congr (ops := original.component.operations)
          (env := actual.environment row) (env' := original.environment row) rfl)
    have issued : original.Guarantees := by rw [show original = _ from position]; exact (table_valid _ _ _ _ _ valid).2
    apply actual.guarantees_iff_forall.mpr
    intro interaction member direction
    have used := shared ▸ member
    have channel := original.channel_mem_channels_of_mem_interactions interaction used
    rw [component] at channel
    exact channels_independent id _ channel _ _ _ _ (original.guarantees_iff_forall.mp issued interaction used direction)

/-- The active input prefix, registered padding and literal ledgers of an installed table,
including their behavior under the complete witness's canonical data. -/
structure Compiled (id : InstructionChipId) (bucket : List id.Event) (physical : Table Fp) : Prop where
  registered : physical.component = installed id
  prefixes : physical.rowPrefixes (size (installed id).Input) = ((inputs id bucket).map toElements).toArray
  height : physical.length = WitnessGeneration.demandHeight bucket.length
  constraints : physical.Constraints
  guarantees : physical.Guarantees
  receipts : physical.interactionsWith InstructionReceipt.channel.toRaw = physical.table.map (fun cells =>
    let row := (supportedChipFor (p := SP1Prime) id).decodeRow physical.data cells
    InstructionReceipt.channel.pushedIfValue row.is_real (statePushMessage row))
  receipt_count : (physical.interactionsWith InstructionReceipt.channel.toRaw).length = physical.length
  weights : (physical.interactionsWith InstructionReceipt.channel.toRaw).map (·.mult) =
    List.replicate bucket.length 1 ++ List.replicate (WitnessGeneration.demandPadding bucket.length) 0
  canonical : ∀ (inventory : List (Table Fp)) (unique : (inventory.map fun t => t.component.circuit.name).Nodup)
    (publicInput : Array Fp) (i : Fin inventory.length), inventory[i.val] = physical →
    ∃ actual, (withDerivedData inventory unique publicInput)[i.val]? = some actual ∧
      actual.component = installed id ∧ actual.table = physical.table ∧
      actual.data = deriveProverData inventory publicInput ∧ actual.Constraints ∧ actual.Guarantees ∧
      ∀ channel, actual.interactionsWith channel = physical.interactionsWith channel

private theorem compiled (id : InstructionChipId) (bucket : List id.Event)
    (bounded : WitnessGeneration.demandHeight bucket.length ≤ UInt64.size) (valid : ∀ e ∈ bucket, id.Valid e) :
    Compiled id bucket (table id bucket (ProverData.empty _) (ProverHint.empty _) bounded) := by
  let built := table id bucket (ProverData.empty _) (ProverHint.empty _) bounded
  obtain ⟨checked, supplied⟩ := table_valid id bucket _ _ bounded valid
  refine ⟨rfl, ?_, table_length .., checked, supplied, table_receipts .., ?_, receipt_weights _ _ _ _ _ valid, ?_⟩
  · exact built.data_consistent.symm.trans ((installed id).inputData_consistent _ (ProverData.empty _))
  · rw [table_receipt_count, table_length]
  · intro inventory unique publicInput i position
    simpa only [← position] using atSlot id bucket bounded valid inventory unique publicInput i position

/-- Canonicalizing the ordered block of all 25 tables requires no layout or data from the caller. -/
def CanonicalBlock (physical : InstructionChipId → Table Fp) (publicInput : Array Fp) : Prop :=
  let inventory := InstructionChipId.all.map physical
  ∃ unique : (inventory.map fun t => t.component.circuit.name).Nodup,
    ∀ id, ∃ actual ∈ withDerivedData inventory unique publicInput,
      actual.component = installed id ∧ actual.table = (physical id).table ∧
      actual.data = deriveProverData inventory publicInput ∧ actual.Constraints ∧ actual.Guarantees ∧
      ∀ ch, actual.interactionsWith ch = (physical id).interactionsWith ch

private theorem canonicalBlock {rows : List RoutedEvent} {physical : InstructionChipId → Table Fp}
    (tables : ∀ id, Compiled id (EventBuckets.ofChronological rows id) (physical id)) (publicInput : Array Fp) :
    CanonicalBlock physical publicInput := by
  let inventory := InstructionChipId.all.map physical
  have names (id : InstructionChipId) : (physical id).component.circuit.name = (installed id).circuit.name :=
    congrArg (fun (c : Component Fp) => c.circuit.name) (tables id).registered
  have unique : (inventory.map fun t => t.component.circuit.name).Nodup := by
    simp only [inventory, List.map_map, Function.comp_def, names]
    decide +kernel
  refine ⟨unique, fun id => ?_⟩
  have present : physical id ∈ inventory := List.mem_map_of_mem (f := physical) (InstructionChipId.mem_all id)
  obtain ⟨i, atIndex⟩ := List.mem_iff_getElem?.mp present
  obtain ⟨inside, equal⟩ := List.getElem?_eq_some_iff.mp atIndex
  obtain ⟨actual, found, same⟩ := (tables id).canonical inventory unique publicInput ⟨i, inside⟩ equal
  exact ⟨actual, List.mem_iff_getElem?.mpr ⟨i, found⟩, same⟩

end InstalledInstructionTables

/-- Every released mixed path constructs the 25 installed ordinary tables from its chronological
router, without external row hints. Each committed input prefix is the exact packed event sequence.
Their separately rounded tables together cost at most twice the tape's ordinary-event count. -/
theorem releaseAdmissibleExecution_instructionTables {limits : ResourceLimits}
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : ReleaseAdmissibleExecution limits SP1Prime image source target events) :
    ∃ (rows : List RoutedEvent) (physical : InstructionChipId → Table Fp),
      routeObservations? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows ∧
      rows.length = events.countP ExecutionEvent.isOrdinary ∧
      (InstructionChipId.all.map (fun id => (physical id).length)).sum ≤ 2 * rows.length ∧
      (∀ id, InstalledInstructionTables.Compiled id (EventBuckets.ofChronological rows id) (physical id)) ∧
      ∀ publicInput, InstalledInstructionTables.CanonicalBlock physical publicInput := by
  obtain ⟨rows, route, count, valid⟩ := releaseAdmissibleExecution_instructionBuckets execution
  let bucket := EventBuckets.ofChronological rows
  let physical (id : InstructionChipId) := InstalledInstructionTables.table id (bucket id)
    (ProverData.empty _) (ProverHint.empty _) (valid id).1
  have tables (id : InstructionChipId) := InstalledInstructionTables.compiled id (bucket id) (valid id).1 (valid id).2
  have heights (id : InstructionChipId) : (physical id).length = EventBuckets.paddedHeight rows id := (tables id).height
  exact ⟨rows, physical, route, count, by simpa only [heights] using EventBuckets.sum_padded_heights rows, tables,
    InstalledInstructionTables.canonicalBlock tables⟩

end SP1Clean.TraceGen
