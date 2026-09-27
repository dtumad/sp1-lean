import SP1Clean.Soundness.HostSailBoundary
import SP1Clean.Soundness.ProtectedOrdinaryReceipt

/-! # Install ordinary receipt producers in the existing mixed assembly

Only the 25 instruction components change. They retain all original row arrays, constraints,
lookups and ledgers, including each store's byte-permission requests. Complete Memory checks,
host resources and the supplied Sail frame remain installed. The resource block can contain
the ordered observation consumer; authentic endpoints and its full Byte closure are subsequent
integration obligations. This producer installation alone is not an end-to-end capstone.
-/

namespace SP1Clean.Soundness.HostOrdinaryReceipts

open Circuit Air.Flat Channels Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- The physical registration retains the original input representation. -/
local instance (id : InstructionChipId) : ProvableType (supportedChipFor (p := p) id).kind.Inputs :=
  (supportedChipFor (p := p) id).kind.provableInputs
/-- The physical registration retains the original output representation. -/
local instance (id : InstructionChipId) : ProvableType (supportedChipFor (p := p) id).kind.Cols :=
  (supportedChipFor (p := p) id).kind.provableCols

/-- The original registration order selects the receipt-bearing protected instruction. -/
def replace (index : ℕ) (original : Component (ZMod p)) : Component (ZMod p) :=
  if within : 7 ≤ index ∧ index < 32 then
    ProtectedOrdinaryReceipt.component
      (InstructionChipId.all[index - 7]'(by rw [InstructionChipId.all_length]; omega))
  else original

/-- Install the producers without moving or removing any physical table. -/
def ensemble (image : ProgramImage) (source target : ExecutionSnapshot)
    (final : HostHintQueue.State (ZMod p))
    (others : List (HostLocalHandoff.Receiver (p := p))) (resources : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p))) : Ensemble (ZMod p) SP1PublicIO :=
  let base := HostSailBoundary.ensemble image source target final others resources channels
  { base with tables := base.tables.mapIdx replace
              channels := base.channels ++ [InstructionReceipt.channel.toRaw] }

variable {image : ProgramImage} {source target : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)}
  {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
  {channels : List (RawChannel (ZMod p))}

/-- Receipt publication adds no tables. -/
theorem tables_length :
    (ensemble (p := p) image source target final others resources channels).tables.length =
      (HostSailBoundary.ensemble image source target final others resources channels).tables.length :=
  by simp only [ensemble, List.length_mapIdx]

private theorem base_length :
    (HostSailBoundary.ensemble (p := p) image source target final others resources channels).tables.length =
      65 + others.length + resources.length := by
  simp only [HostSailBoundary.ensemble, PublicVerifier.install, HostFinalMemory.ensemble,
    ClosedVerifier.install, HostFinalMemory.withReceipts, HostFinalMemory.withRegisters,
    FinalReceiptEnsemble.install, List.length_set, HostFinalMemory.base_tables_length]

private theorem protected_component (index : Fin 25) :
    (ProtectedLocalCore.tables (p := p) image source)[7 + index.val]'(by
      rw [ProtectedLocalCore.tables_length]; omega) =
        ⟨ProtectedOrdinaryReceipt.provider (InstructionChipId.all[index.val]'(by
          rw [InstructionChipId.all_length]; exact index.isLt))⟩ := by
  fin_cases index <;> rfl

/-- Static registration identifies the actual protected instructions below all endpoint wrappers. -/
theorem original_component (index : Fin 25) :
    (HostSailBoundary.ensemble (p := p) image source target final others resources channels).tables[7 + index.val]'(by
      rw [base_length]
      omega) =
      ⟨ProtectedOrdinaryReceipt.provider (InstructionChipId.all[index.val]'(by
        rw [InstructionChipId.all_length]; exact index.isLt))⟩ := by
  change (HostFinalMemory.ensemble image source target.sail.memorySnapshot final target.host
    others resources channels).tables[7 + index.val]'_ = _
  simp only [HostFinalMemory.tables_eq]
  rw [List.getElem_set_ne (by omega : 4 ≠ 7 + index.val),
    List.getElem_set_ne (by omega : 3 ≠ 7 + index.val),
    List.getElem_set_ne (by have := index.isLt; omega : 57 ≠ 7 + index.val)]
  rw [List.getElem_append_left (by rw [HostFinalMemory.prefix_length]; have := index.isLt; omega)]
  simp only [HostFinalMemory.beforeChecks]
  rw [HostLocalCore.core_component image source _ ⟨7 + index.val, by omega⟩,
    if_neg (by have := index.isLt; omega : 58 ≠ 7 + index.val)]
  exact protected_component index

/-- Each instruction retains its original physical position under a typed receipt registration. -/
def slot (index : Fin 25) : TableSlot
    (ensemble (p := p) image source target final others resources channels).tables
    (ProtectedOrdinaryReceipt.component (InstructionChipId.all[index.val]'(by
      rw [InstructionChipId.all_length]; exact index.isLt))) where
  index := ⟨7 + index.val, by rw [tables_length, base_length]; omega⟩
  component_eq := by
    simp only [ensemble, List.getElem_mapIdx, replace,
      show 7 ≤ 7 + index.val ∧ 7 + index.val < 32 by omega, and_self, ↓reduceDIte,
      Nat.add_sub_cancel_left]

/-- Read the literal receipt-bearing instruction table through its typed registration. -/
def instructionTable (index : Fin 25)
    (witness : EnsembleWitness (ensemble image source target final others resources channels)) : Table (ZMod p) :=
  (slot index).table witness

/-- Installed receipts use the sole existing decoder on the actual physical table arrays. -/
theorem instructionTable_receipts (index : Fin 25)
    (witness : EnsembleWitness (ensemble image source target final others resources channels)) :
    (instructionTable index witness).interactionsWith InstructionReceipt.channel.toRaw =
      (instructionTable index witness).table.map (fun physical =>
        let row := (supportedChipFor (p := p) (InstructionChipId.all[index.val]'(by
          rw [InstructionChipId.all_length]; exact index.isLt))).decodeRow witness.data physical
        InstructionReceipt.channel.pushedIfValue row.is_real (statePushMessage row)) := by
  have registered := (slot (image := image) (source := source) (target := target) (final := final)
    (others := others) (resources := resources) (channels := channels) index).table_component witness
  have data := (slot (image := image) (source := source) (target := target) (final := final)
    (others := others) (resources := resources) (channels := channels) index).table_data witness
  change (instructionTable index witness).component = _ at registered
  change (instructionTable index witness).data = _ at data
  simp only [Table.interactionsWith, registered, Table.environment,
    ProtectedOrdinaryReceipt.row_receipt, data]
  exact List.map_eq_flatMap.symm

/-- Physical cost includes every disabled padding occurrence. -/
theorem instructionTable_receipt_count (index : Fin 25)
    (witness : EnsembleWitness (ensemble image source target final others resources channels)) :
    ((instructionTable index witness).interactionsWith InstructionReceipt.channel.toRaw).length =
      (instructionTable index witness).length := by
  rw [instructionTable_receipts, List.length_map]

private theorem component_projection
    (index : Fin (HostSailBoundary.ensemble (p := p) image source target final others resources channels).tables.length) :
    let original := (HostSailBoundary.ensemble image source target final others resources channels).tables[index.val]
    let extended := replace index.val original
    extended.operations.constraints = original.operations.constraints ∧
    extended.operations.lookups = original.operations.lookups ∧
    ∀ channel, channel ≠ InstructionReceipt.channel.toRaw →
      extended.operations.interactionsWith channel = original.operations.interactionsWith channel := by
  dsimp only
  unfold replace
  split
  · rename_i within
    have selected := original_component (image := image) (source := source) (target := target)
      (final := final) (others := others) (resources := resources) (channels := channels)
      ⟨index.val - 7, by omega⟩
    simp only [show 7 + (index.val - 7) = index.val by omega] at selected
    rw [selected]
    exact ⟨ProtectedOrdinaryReceipt.constraints _, ProtectedOrdinaryReceipt.lookups _,
      ProtectedOrdinaryReceipt.interactions _⟩
  · exact ⟨rfl, rfl, fun _ _ => rfl⟩

/-- Forget only the additional receipts, retaining every physical row and public field. -/
def baseWitness (witness : EnsembleWitness (ensemble image source target final others resources channels)) :
    EnsembleWitness (HostSailBoundary.ensemble image source target final others resources channels) :=
  witness.project _ (by rw [tables_length])

/-- Original arrays also construct the producer installation, with no additional witnesses. -/
def construct (witness : EnsembleWitness
    (HostSailBoundary.ensemble image source target final others resources channels)) :
    EnsembleWitness (ensemble image source target final others resources channels) :=
  witness.project _ (by rw [tables_length])

/-- The projected witness retains the shared prover environment. -/
theorem baseWitness_data (witness : EnsembleWitness
    (ensemble image source target final others resources channels)) :
    (baseWitness witness).data = witness.data :=
  witness.project_data (target := HostSailBoundary.ensemble image source target final others resources channels)
    (by rw [tables_length])

/-- The complete public header remains attached to the same physical instruction rows. -/
theorem baseWitness_publicInput (witness : EnsembleWitness
    (ensemble image source target final others resources channels)) :
    (baseWitness witness).publicInput = witness.publicInput := by
  simp only [baseWitness, EnsembleWitness.project, EnsembleWitness.ofTables_publicInput]

/-- Projection preserves the original row arrays at every position. -/
theorem baseWitness_table (witness : EnsembleWitness
    (ensemble image source target final others resources channels))
    (index : Fin (HostSailBoundary.ensemble image source target final others resources channels).tables.length) :
    (baseWitness witness).tables[index.val]'(by rw [← (baseWitness witness).same_length]; exact index.isLt) =
      (witness.tables[index.val]'(by rw [← witness.same_length, tables_length]; exact index.isLt)).withComponent
        ((HostSailBoundary.ensemble image source target final others resources channels).tables[index.val]) :=
  witness.project_getElem (target := HostSailBoundary.ensemble image source target final others resources channels)
    (by rw [tables_length]) index

/-- Projection retains all local checks, including the supplied Memory and Sail target checks. -/
theorem baseWitness_constraints
    (witness : EnsembleWitness (ensemble image source target final others resources channels))
    (checked : witness.Constraints) : (baseWitness witness).Constraints := by
  apply witness.project_constraints
    (target := HostSailBoundary.ensemble image source target final others resources channels)
    (by rw [tables_length]) rfl ?_ ?_ checked
  · intro index
    simpa only [ensemble, List.getElem_mapIdx] using (component_projection index).1.symm
  · intro index
    simpa only [ensemble, List.getElem_mapIdx] using (component_projection index).2.1.symm

/-- Constructing producer rows needs only the original local checks. -/
theorem construct_constraints (witness : EnsembleWitness
    (HostSailBoundary.ensemble image source target final others resources channels))
    (checked : witness.Constraints) : (construct witness).Constraints := by
  apply witness.project_constraints
    (target := ensemble image source target final others resources channels)
    (by rw [tables_length]) rfl ?_ ?_ checked
  · intro index
    have result := (component_projection (image := image) (source := source) (target := target)
      (final := final) (others := others) (resources := resources) (channels := channels)
      ⟨index.val, by simpa only [tables_length] using index.isLt⟩).1
    simpa only [ensemble, List.getElem_mapIdx] using result
  · intro index
    have result := (component_projection (image := image) (source := source) (target := target)
      (final := final) (others := others) (resources := resources) (channels := channels)
      ⟨index.val, by simpa only [tables_length] using index.isLt⟩).2.1
    simpa only [ensemble, List.getElem_mapIdx] using result

/-- Complete ledgers on every original channel are unchanged, including WritePermission. -/
theorem baseWitness_interactions
    (witness : EnsembleWitness (ensemble image source target final others resources channels))
    (channel : RawChannel (ZMod p)) (different : channel ≠ InstructionReceipt.channel.toRaw) :
    (baseWitness witness).interactionsWith channel = witness.interactionsWith channel := by
  apply witness.project_interactions
    (target := HostSailBoundary.ensemble image source target final others resources channels)
    (by rw [tables_length]) rfl channel ?_ ?_
  · intro index
    simpa only [ensemble, List.getElem_mapIdx] using (component_projection index).2.2 channel different |>.symm
  · rw [← tables_length (image := image) (source := source) (target := target) (final := final)
      (others := others) (resources := resources) (channels := channels), witness.same_length,
      List.drop_length, List.flatMap_nil]

/-- Each unchanged-channel balance and its occurrence bound transports independently. -/
theorem baseWitness_balancedChannel
    (witness : EnsembleWitness (ensemble image source target final others resources channels))
    (channel : RawChannel (ZMod p)) (different : channel ≠ InstructionReceipt.channel.toRaw)
    (balanced : witness.BalancedChannel channel) : (baseWitness witness).BalancedChannel channel := by
  change BalancedInteractions ((baseWitness witness).interactionsWith channel)
  rw [baseWitness_interactions witness channel different]
  exact balanced

/-- Full-assembly guarantees pass to the old proof view without assuming its global balance. -/
theorem baseWitness_channelGuarantees
    (witness : EnsembleWitness (ensemble image source target final others resources channels))
    (channel : RawChannel (ZMod p)) (different : channel ≠ InstructionReceipt.channel.toRaw)
    (guarantees : ∀ table ∈ witness.allTables, table.ChannelGuarantees channel) :
    ∀ table ∈ (baseWitness witness).allTables, table.ChannelGuarantees channel :=
  witness.channelGuarantees_of_interactions_subset (baseWitness witness) channel
    (baseWitness_data witness)
    (by rw [baseWitness_interactions witness channel different]; exact List.Subset.refl _) guarantees

/-- Data-only construction preserves all original channel occurrences as well as local checks. -/
theorem construct_interactions (witness : EnsembleWitness
    (HostSailBoundary.ensemble image source target final others resources channels))
    (channel : RawChannel (ZMod p)) (different : channel ≠ InstructionReceipt.channel.toRaw) :
    (construct witness).interactionsWith channel = witness.interactionsWith channel := by
  apply witness.project_interactions
    (target := ensemble image source target final others resources channels)
    (by rw [tables_length]) rfl channel ?_ ?_
  · intro index
    have result := (component_projection (image := image) (source := source) (target := target)
      (final := final) (others := others) (resources := resources) (channels := channels)
      ⟨index.val, by simpa only [tables_length] using index.isLt⟩).2.2 channel different
    simpa only [ensemble, List.getElem_mapIdx] using result
  · rw [tables_length, witness.same_length, List.drop_length, List.flatMap_nil]

end SP1Clean.Soundness.HostOrdinaryReceipts
