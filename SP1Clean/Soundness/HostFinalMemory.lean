import SP1Clean.Soundness.HostHintQueueBoundary
import SP1Clean.Soundness.FinalMemoryChecks

/-! # Complete target Memory checks in the physical host assembly

The existing host assembly keeps every CPU, host, source and final-order table. The two
target consumers are appended to its resource block, the original finalizers publish their
full records, and the canonical change demand runs once in the verifier. All four additions
use the existing circuits. Proof views retain the original arrays and do not claim projected
Byte balance. Grounding and complete endpoint agreement consume the channel facts separately.
-/

namespace SP1Clean.Soundness.HostFinalMemory

open Circuit Air.Flat Channels Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Install the existing target consumers in the host resource block. Their channels are
registered by the same host assembly as every other resource. -/
@[reducible] def base (image : ProgramImage) (source : ExecutionSnapshot) (target : MemorySnapshot)
    (final : HostHintQueue.State (ZMod p)) (bankFinal : HostState)
    (others : List (HostLocalHandoff.Receiver (p := p))) (resources : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p))) : Ensemble (ZMod p) SP1PublicIO :=
  HostHintQueueBoundary.ensemble image source final bankFinal others
    (resources ++ FinalMemoryChecks.checkTables target) channels

/-- The original core and handler positions are unchanged; only two resource tables are added. -/
theorem base_tables_length (image : ProgramImage) (source : ExecutionSnapshot) (target : MemorySnapshot)
    (final : HostHintQueue.State (ZMod p)) (bankFinal : HostState)
    (others : List (HostLocalHandoff.Receiver (p := p))) (resources : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p))) :
    (base image source target final bankFinal others resources channels).tables.length =
      65 + others.length + resources.length := by
  simp only [base, HostHintQueueBoundary.ensemble, HaltPadding.install, ClosedVerifier.install,
    HostHintReadLocal.ensemble, HostLocalHandoff.ensemble, HostLocalCore.ensemble, List.length_set]
  rw [HostLocalCore.tables_length]
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil,
    HostHintReadHandoff.wordResources, FinalMemoryChecks.checkTables]
  omega

/-- Publish complete receipts at the original register-finalizer position. -/
@[reducible] def withRegisters (image : ProgramImage) (source : ExecutionSnapshot) (target : MemorySnapshot)
    (final : HostHintQueue.State (ZMod p)) (bankFinal : HostState)
    (others : List (HostLocalHandoff.Receiver (p := p))) (resources : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p))) :=
  FinalReceiptEnsemble.install (base image source target final bankFinal others resources channels)
    ⟨3, by
      rw [base_tables_length]
      omega⟩ false OrderedFinalProvider.registerCircuit

/-- Publish complete receipts at the original RAM-finalizer position. -/
@[reducible] def withReceipts (image : ProgramImage) (source : ExecutionSnapshot) (target : MemorySnapshot)
    (final : HostHintQueue.State (ZMod p)) (bankFinal : HostState)
    (others : List (HostLocalHandoff.Receiver (p := p))) (resources : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p))) :=
  FinalReceiptEnsemble.install (withRegisters image source target final bankFinal others resources channels)
    ⟨4, by
      simp only [withRegisters, FinalReceiptEnsemble.install, List.length_set, base_tables_length]
      omega⟩ true OrderedFinalProvider.ramCircuit

/-- The source-to-target change inventory is fixed by the supplied complete snapshots. -/
def ensemble (image : ProgramImage) (source : ExecutionSnapshot) (target : MemorySnapshot)
    (final : HostHintQueue.State (ZMod p)) (bankFinal : HostState)
    (others : List (HostLocalHandoff.Receiver (p := p))) (resources : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p))) : Ensemble (ZMod p) SP1PublicIO :=
  (FinalMemoryChangeBoundary.closed source.sail.memorySnapshot target).install
    (withReceipts image source target final bankFinal others resources channels)

variable {image : ProgramImage} {source : ExecutionSnapshot} {target : MemorySnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}
  {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
  {channels : List (RawChannel (ZMod p))}

/-- The original host table block before the two target consumers, prior to the padding wrapper. -/
def beforeChecks (image : ProgramImage) (source : ExecutionSnapshot)
    (others : List (HostLocalHandoff.Receiver (p := p))) (resources : List (Component (ZMod p))) :=
  HostLocalCore.tables image source
    ((HostHintReadHandoff.receiver :: others).map (·.component) ++ (HostHintReadHandoff.wordResources ++ resources))

/-- The prefix contains exactly the original core, receiver registry and resource block. -/
theorem prefix_length (image : ProgramImage) (source : ExecutionSnapshot)
    (others : List (HostLocalHandoff.Receiver (p := p))) (resources : List (Component (ZMod p))) :
    (beforeChecks image source others resources).length = 63 + others.length + resources.length := by
  rw [beforeChecks, HostLocalCore.tables_length]
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil,
    HostHintReadHandoff.wordResources]
  omega

/-- The target consumers are genuine appended resources in the unchanged host table layout. -/
theorem base_tables_eq : (base image source target final bankFinal others resources channels).tables =
    (beforeChecks image source others resources ++ FinalMemoryChecks.checkTables target).set 57 HaltPaddingChip.component := by
  simp only [base, HostHintQueueBoundary.ensemble, HaltPadding.install, ClosedVerifier.install,
    HostHintReadLocal.ensemble, HostLocalHandoff.ensemble, HostLocalCore.ensemble, beforeChecks,
    HostLocalCore.tables, List.append_assoc]

/-- Both wrappers act on the original finalizers; appended targets are retained literally. -/
theorem tables_eq : (ensemble image source target final bankFinal others resources channels).tables =
    (((beforeChecks image source others resources ++ FinalMemoryChecks.checkTables target).set 57 HaltPaddingChip.component).set 3
      ⟨FinalMemoryReceipt.circuit false OrderedFinalProvider.registerCircuit⟩).set 4
      ⟨FinalMemoryReceipt.circuit true OrderedFinalProvider.ramCircuit⟩ := by
  simp only [ensemble, ClosedVerifier.install, withReceipts, withRegisters, FinalReceiptEnsemble.install,
    base_tables_eq]

/-- Typed registration of either target validator survives all three unrelated table replacements. -/
def checkSlot (index : Fin 2) : TableSlot (ensemble image source target final bankFinal others resources channels).tables
    ((FinalMemoryChecks.checkTables (p := p) target)[index.val]'(by
      simpa only [FinalMemoryChecks.checkTables, List.length_cons, List.length_nil] using index.isLt)) := by
  let slot := (TableSlot.ofIndex (FinalMemoryChecks.checkTables (p := p) target)
    ⟨index.val, by simpa only [FinalMemoryChecks.checkTables, List.length_cons, List.length_nil] using index.isLt⟩).appendRight
      (beforeChecks image source others resources)
  have bound : 60 ≤ slot.index.val := by
    dsimp only [slot, TableSlot.appendRight, TableSlot.ofIndex]
    rw [prefix_length]
    omega
  exact (((slot.setOther 57 HaltPaddingChip.component (by omega)).setOther 3
    ⟨FinalMemoryReceipt.circuit false OrderedFinalProvider.registerCircuit⟩ (by change 3 ≠ slot.index.val; omega)).setOther 4
      ⟨FinalMemoryReceipt.circuit true OrderedFinalProvider.ramCircuit⟩ (by change 4 ≠ slot.index.val; omega)).cast tables_eq.symm

private theorem base_boundary_component (index : Fin 6) :
    (base image source target final bankFinal others resources channels).tables[index.val]'(by
      rw [base_tables_length]; omega) =
      (LocalCore.tables (p := p) image source)[index.val]'(by rw [LocalCore.tables_length]; omega) := by
  simp only [base, HostHintQueueBoundary.ensemble, HaltPadding.install, ClosedVerifier.install,
    HostHintReadLocal.ensemble, HostLocalHandoff.ensemble, HostLocalCore.ensemble]
  rw [List.getElem_set_ne (by have := index.isLt; omega : 57 ≠ index.val),
    HostLocalCore.core_component image source _ ⟨index.val, by have := index.isLt; omega⟩,
    if_neg (by have := index.isLt; omega : 58 ≠ index.val)]
  simp only [ProtectedLocalCore.tables]
  rw [List.getElem_append_left (by simp only [List.length_set, LocalCore.tables_length]; have := index.isLt; omega)]
  rw [List.getElem_set_ne (by have := index.isLt; omega : 28 ≠ index.val),
    List.getElem_set_ne (by have := index.isLt; omega : 27 ≠ index.val),
    List.getElem_set_ne (by have := index.isLt; omega : 26 ≠ index.val),
    List.getElem_set_ne (by have := index.isLt; omega : 25 ≠ index.val)]

private theorem base_register_component :
    (base image source target final bankFinal others resources channels).tables[3]'(by rw [base_tables_length]; omega) =
      ⟨OrderedFinalProvider.registerCircuit⟩ :=
  (base_boundary_component (index := ⟨3, by decide⟩)).trans (by rfl)

private theorem base_ram_component :
    (base image source target final bankFinal others resources channels).tables[4]'(by rw [base_tables_length]; omega) =
      ⟨OrderedFinalProvider.ramCircuit⟩ :=
  (base_boundary_component (index := ⟨4, by decide⟩)).trans (by rfl)

private theorem withRegisters_ram_component :
    (withRegisters image source target final bankFinal others resources channels).tables[4]'(by
      simp only [withRegisters, FinalReceiptEnsemble.install, List.length_set, base_tables_length]; omega) =
      ⟨OrderedFinalProvider.ramCircuit⟩ := by
  change ((base image source target final bankFinal others resources channels).tables.set 3
    ⟨FinalMemoryReceipt.circuit false OrderedFinalProvider.registerCircuit⟩)[4]'(by
      rw [List.length_set, base_tables_length]; omega) = _
  rw [List.getElem_set_ne (by decide : 3 ≠ 4)]
  exact base_ram_component

/-- The three original finalizer positions, with the two receipt wrappers installed. -/
def finalSlot (index : Fin 3) : TableSlot
    (ensemble image source target final bankFinal others resources channels).tables
    ((FinalMemoryChecks.ensemble (p := p) source.sail.memorySnapshot target [] []).tables[index.val]'(by
      rw [FinalMemoryChecks.tables_eq]; simp; omega)) := by
  refine ⟨⟨3 + index.val, by
    simp only [ensemble, ClosedVerifier.install, withReceipts, withRegisters,
      FinalReceiptEnsemble.install, List.length_set, base_tables_length]
    omega⟩, ?_⟩
  change (((base image source target final bankFinal others resources channels).tables.set 3
    ⟨FinalMemoryReceipt.circuit false OrderedFinalProvider.registerCircuit⟩).set 4
    ⟨FinalMemoryReceipt.circuit true OrderedFinalProvider.ramCircuit⟩)[3 + index.val]'(by
      rw [List.length_set, List.length_set, base_tables_length]; omega) = _
  fin_cases index <;> dsimp only
  · rw [List.getElem_set_ne (by decide : 4 ≠ 3), List.getElem_set_self]
    rfl
  · rw [List.getElem_set_self]
    rfl
  · rw [List.getElem_set_ne (by decide : 4 ≠ 5), List.getElem_set_ne (by decide : 3 ≠ 5),
      base_boundary_component (index := ⟨5, by decide⟩)]
    rfl

/-- Retain all physical tables while viewing the old verifier without its new change demand. -/
def receiptWitness (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels)) :
    EnsembleWitness (withReceipts image source target final bankFinal others resources channels) :=
  (FinalMemoryChangeBoundary.closed source.sail.memorySnapshot target).project witness

/-- Forget only the RAM receipt, keeping its physical table and original constraints. -/
def registerWitness (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels)) :
    EnsembleWitness (withRegisters image source target final bankFinal others resources channels) :=
  FinalReceiptEnsemble.project (ens := withRegisters image source target final bankFinal others resources channels)
    (index := ⟨4, by simp only [withRegisters, FinalReceiptEnsemble.install,
      List.length_set, base_tables_length]; omega⟩)
    (ram := true) (provider := OrderedFinalProvider.ramCircuit) withRegisters_ram_component (receiptWitness witness)

/-- The existing host proof view includes both added target consumers. No rows are removed. -/
def baseWitness (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels)) :
    EnsembleWitness (base image source target final bankFinal others resources channels) :=
  FinalReceiptEnsemble.project (ens := base image source target final bankFinal others resources channels)
    (index := ⟨3, by rw [base_tables_length]; omega⟩)
    (ram := false) (provider := OrderedFinalProvider.registerCircuit) base_register_component (registerWitness witness)

/-- Raw acceptance supplies every original host assertion and fixed lookup. -/
theorem baseWitness_constraints
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels))
    (checked : witness.Constraints) : (baseWitness witness).Constraints := by
  have raw : (receiptWitness witness).Constraints :=
    (FinalMemoryChangeBoundary.closed source.sail.memorySnapshot target).project_constraints witness checked
  unfold baseWitness
  apply (FinalReceiptEnsemble.project_constraints _ _).mpr
  unfold registerWitness
  exact (FinalReceiptEnsemble.project_constraints _ _).mpr raw

/-- Original table arrays remain byte-for-byte identical through the receipt proof views. -/
theorem baseWitness_rows
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels)) :
    (baseWitness witness).tables.map (·.table) = witness.tables.map (·.table) := by
  have registers := FinalReceiptEnsemble.project_rows
    (ens := base image source target final bankFinal others resources channels)
    (index := ⟨3, by rw [base_tables_length]; omega⟩)
    (ram := false) (provider := OrderedFinalProvider.registerCircuit) base_register_component (registerWitness witness)
  have ram := FinalReceiptEnsemble.project_rows
    (ens := withRegisters image source target final bankFinal others resources channels)
    (index := ⟨4, by simp only [withRegisters, FinalReceiptEnsemble.install,
      List.length_set, base_tables_length]; omega⟩)
    (ram := true) (provider := OrderedFinalProvider.ramCircuit) withRegisters_ram_component (receiptWitness witness)
  exact registers.trans (ram.trans (congrArg (List.map (fun physical : Table (ZMod p) => physical.table))
    ((FinalMemoryChangeBoundary.closed source.sail.memorySnapshot target).project_tables witness)))

/-- Original data and public inputs are retained in the host proof view. -/
theorem baseWitness_data
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels)) :
    (baseWitness witness).data = witness.data := by
  have inner : (registerWitness witness).data = witness.data := by
    unfold registerWitness
    exact (FinalReceiptEnsemble.project_data _ _).trans
      ((FinalMemoryChangeBoundary.closed source.sail.memorySnapshot target).project_data witness)
  unfold baseWitness
  exact (FinalReceiptEnsemble.project_data _ _).trans inner

/-- The complete original header remains attached to the same physical instruction rows. -/
theorem baseWitness_publicInput
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels)) :
    (baseWitness witness).publicInput = witness.publicInput := by
  have inner : (registerWitness witness).publicInput = witness.publicInput := by
    unfold registerWitness
    exact (FinalReceiptEnsemble.project_publicInput _ _).trans
      ((FinalMemoryChangeBoundary.closed source.sail.memorySnapshot target).project_publicInput witness)
  unfold baseWitness
  exact (FinalReceiptEnsemble.project_publicInput _ _).trans inner

/-- Guarantees transfer on every original channel independently of its projected balance. -/
theorem baseWitness_channelGuarantees
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels))
    (channel : RawChannel (ZMod p))
    (registers : channel ≠ (FinalMemoryValue.channel false).toRaw)
    (ram : channel ≠ (FinalMemoryValue.channel true).toRaw)
    (guarantees : ∀ table ∈ witness.allTables, table.ChannelGuarantees channel) :
    ∀ table ∈ (baseWitness witness).allTables, table.ChannelGuarantees channel :=
  FinalReceiptEnsemble.project_channelGuarantees _ (registerWitness witness) channel registers
    (FinalReceiptEnsemble.project_channelGuarantees _ (receiptWitness witness) channel ram
      ((FinalMemoryChangeBoundary.closed source.sail.memorySnapshot target).project_channelGuarantees
        witness channel guarantees))

/-- Existing host proofs inherit Byte guarantees from the complete physical acceptance argument. -/
theorem baseWitness_byte
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels))
    (guarantees : ∀ table ∈ witness.allTables, table.ChannelGuarantees byteChannel.toRaw) :
    ∀ table ∈ (baseWitness witness).allTables, table.ChannelGuarantees byteChannel.toRaw :=
  baseWitness_channelGuarantees witness byteChannel.toRaw
    (by simp [byteChannel, FinalMemoryValue.channel, Channel.toRaw])
    (by simp [byteChannel, FinalMemoryValue.channel, Channel.toRaw]) guarantees

/-- Original channel occurrences survive both receipt wrappers exactly. -/
theorem baseWitness_interactions
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels))
    (channel : RawChannel (ZMod p))
    (registers : channel ≠ (FinalMemoryValue.channel false).toRaw)
    (ram : channel ≠ (FinalMemoryValue.channel true).toRaw) :
    (baseWitness witness).interactionsWith channel = (receiptWitness witness).interactionsWith channel :=
  (FinalReceiptEnsemble.project_interactions _ (registerWitness witness) channel registers).trans
    (FinalReceiptEnsemble.project_interactions _ (receiptWitness witness) channel ram)

/-- Channels unaffected by the three new receipts retain their full balance and count bounds.
The target validators remain in this view, so their Byte demand is retained. -/
theorem baseWitness_balancedChannel
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels))
    (channel : RawChannel (ZMod p))
    (registers : channel ≠ (FinalMemoryValue.channel false).toRaw)
    (ram : channel ≠ (FinalMemoryValue.channel true).toRaw)
    (changes : channel ≠ FinalMemoryChange.channel.toRaw)
    (balanced : witness.BalancedChannel channel) : (baseWitness witness).BalancedChannel channel := by
  change BalancedInteractions ((baseWitness witness).interactionsWith channel)
  rw [baseWitness_interactions witness channel registers ram]
  exact (FinalMemoryChangeBoundary.closed source.sail.memorySnapshot target).project_balancedChannel
    witness channel (by simp [FinalMemoryChangeBoundary.closed, FinalMemoryChangeBoundary.circuit,
      circuit_norm, changes]) balanced

end SP1Clean.Soundness.HostFinalMemory
