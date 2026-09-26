import SP1Clean.Soundness.FinalMemoryChecks

/-! # Exact ledgers of the installed target Memory validators

All inventories below are decoded from registered physical tables. Unit receipts retain the
complete final records; changed-location interactions retain zero multiplicities. Auxiliary
silence is a static interface of the installed components, never a witness premise.
-/

namespace SP1Clean.Soundness.FinalMemoryChecks

open Circuit Air.Flat Channels Model.Core Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
  {source target : MemorySnapshot} {auxiliary : List (Component (ZMod p))}
  {channels : List (RawChannel (ZMod p))}

open scoped Classical

omit [Fact (2 ^ 17 < p)] in
private theorem single_interaction (table : Table (ZMod p)) (component : Component (ZMod p))
    (same : table.component = component) (channel : RawChannel (ZMod p))
    (message : Environment (ZMod p) → Interaction (ZMod p))
    (row : ∀ env, component.operations.interactionValuesWith channel env = [message env]) :
    table.interactionsWith channel = table.table.map (fun input => message (table.environment input)) := by
  simp only [Table.interactionsWith, same, row]
  exact List.map_eq_flatMap.symm

/-- One full register receipt is consumed for every actual validation row. -/
theorem register_pulls (witness : EnsembleWitness (ensemble source target auxiliary channels)) :
    (registerSlot.table witness).interactionsWith (FinalMemoryValue.channel false).toRaw =
      (registerInputs witness).map (fun input => (FinalMemoryValue.channel false).pulledValue input.record) := by
  rw [single_interaction _ _ (registerSlot.table_component witness)
    (FinalMemoryValue.channel false).toRaw
    (fun env => (FinalMemoryValue.channel false).pulledValue
      ((⟨FinalRegisterCheck.circuit target⟩ : Component (ZMod p)).rowInput env).record) ?_]
  · simp only [registerInputs, List.map_map, Function.comp_def]
  · intro env
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations]
    change ((FinalRegisterCheck.main target (varFromOffset FinalRegisterCheck.Inputs 0)).operations
      (size FinalRegisterCheck.Inputs)).interactionValuesWith _ env = _
    rw [FinalRegisterCheck.receipt_values]
    simp only [Component.rowInput, ← eval_varFromOffset_valueFromOffset, circuit_norm]

/-- One full RAM receipt is consumed for every actual validation row. -/
theorem ram_pulls (witness : EnsembleWitness (ensemble source target auxiliary channels)) :
    (ramSlot.table witness).interactionsWith (FinalMemoryValue.channel true).toRaw =
      (ramInputs witness).map (fun input => (FinalMemoryValue.channel true).pulledValue input.value.record) := by
  rw [single_interaction _ _ (ramSlot.table_component witness)
    (FinalMemoryValue.channel true).toRaw
    (fun env => (FinalMemoryValue.channel true).pulledValue
      ((⟨FinalRamCheck.circuit target⟩ : Component (ZMod p)).rowInput env).value.record) ?_]
  · simp only [ramInputs, List.map_map, Function.comp_def]
  · intro env
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations]
    change ((FinalRamCheck.main target (varFromOffset FinalRamCheck.Inputs 0)).operations
      (size FinalRamCheck.Inputs)).interactionValuesWith _ env = _
    rw [FinalRamCheck.receipt_values]
    simp only [Component.rowInput, ← eval_varFromOffset_valueFromOffset, circuit_norm]

/-- Physical register selection occurrences, including disabled ones. -/
theorem register_changes (witness : EnsembleWitness (ensemble source target auxiliary channels)) :
    (registerSlot.table witness).interactionsWith FinalMemoryChange.channel.toRaw =
      (registerInputs witness).map (fun input => FinalMemoryChange.channel.pushedIfValue input.selected
        (FinalMemoryChange.key false input.record)) := by
  rw [single_interaction _ _ (registerSlot.table_component witness) FinalMemoryChange.channel.toRaw
    (fun env => let input := (⟨FinalRegisterCheck.circuit target⟩ : Component (ZMod p)).rowInput env
      FinalMemoryChange.channel.pushedIfValue input.selected (FinalMemoryChange.key false input.record)) ?_]
  · simp only [registerInputs, List.map_map, Function.comp_def]
  · intro env
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations]
    change ((FinalRegisterCheck.main target (varFromOffset FinalRegisterCheck.Inputs 0)).operations
      (size FinalRegisterCheck.Inputs)).interactionValuesWith _ env = _
    rw [FinalRegisterCheck.change_values]
    simp only [Component.rowInput, ← eval_varFromOffset_valueFromOffset, circuit_norm]

/-- Physical RAM selection occurrences, including disabled ones. -/
theorem ram_changes (witness : EnsembleWitness (ensemble source target auxiliary channels)) :
    (ramSlot.table witness).interactionsWith FinalMemoryChange.channel.toRaw =
      (ramInputs witness).map (fun input => FinalMemoryChange.channel.pushedIfValue input.selected
        (FinalMemoryChange.key true input.value.record)) := by
  rw [single_interaction _ _ (ramSlot.table_component witness) FinalMemoryChange.channel.toRaw
    (fun env => let input := (⟨FinalRamCheck.circuit target⟩ : Component (ZMod p)).rowInput env
      FinalMemoryChange.channel.pushedIfValue input.selected (FinalMemoryChange.key true input.value.record)) ?_]
  · simp only [ramInputs, List.map_map, Function.comp_def]
  · intro env
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations]
    change ((FinalRamCheck.main target (varFromOffset FinalRamCheck.Inputs 0)).operations
      (size FinalRamCheck.Inputs)).interactionValuesWith _ env = _
    rw [FinalRamCheck.change_values]
    simp only [Component.rowInput, ← eval_varFromOffset_valueFromOffset, circuit_norm]

private theorem table_silent {component : Component (ZMod p)}
    (slot : TableSlot (ensemble source target auxiliary channels).tables component)
    (witness : EnsembleWitness (ensemble source target auxiliary channels)) (channel : RawChannel (ZMod p))
    (absent : (component.circuit.channels.map RawChannel.name).contains channel.name = false) :
    (slot.table witness).interactionsWith channel = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [slot.table_component witness]
  intro member
  have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) member)
  rw [absent] at present
  contradiction

/-- The verifier's only non-ordering interactions are the fixed complete change demand. -/
theorem verifier_values (witness : EnsembleWitness (ensemble source target auxiliary channels))
    (channel : RawChannel (ZMod p))
    (notOrdering : channel ≠ (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw) :
    witness.verifierTable.interactionsWith channel =
      if channel = FinalMemoryChange.channel.toRaw then
        (source.changes target).map (fun loc => FinalMemoryChange.channel.pulledValue (FinalMemoryChange.encode loc))
      else [] := by
  simp only [Table.interactionsWith, EnsembleWitness.verifierTable_flatMap,
    Operations.interactionValuesWith, EnsembleWitness.verifierTable_component,
    Ensemble.verifierTable_interactionsWith]
  change (ensemble source target auxiliary channels).verifierOperations.interactionValuesWith channel
    (Environment.fromInput witness.publicInput witness.data) = _
  refine ((FinalMemoryChangeBoundary.closed source target).verifier_interactions
    (base target auxiliary channels) witness.publicInput witness.data channel).trans ?_
  rw [ClosedVerifier.singleton_interactions]
  have original : (base target auxiliary channels).verifierOperations.interactionValuesWith channel
      (Environment.fromInput witness.publicInput witness.data) = [] := by
    change ((OrderedBoundaryVerifier.main OrderedFinalProvider.channelName
      OrderedMemoryEnsemble.startKey OrderedMemoryEnsemble.endKey ()).operations 0).interactionValuesWith channel _ = []
    simp [Operations.interactionValuesWith, OrderedBoundaryVerifier.main, circuit_norm,
      Ne.symm notOrdering]
  rw [original, List.nil_append]
  simp only [FinalMemoryChangeBoundary.closed, FinalMemoryChangeBoundary.circuit,
    FinalMemoryChangeBoundary.values, List.map_map, Function.comp_def]

/-- The complete register receipt ledger, in physical row order. -/
theorem register_ledger (witness : EnsembleWitness (ensemble source target auxiliary channels))
    (interface : Interface auxiliary) :
    witness.interactionsWith (FinalMemoryValue.channel false).toRaw =
      (FinalReceiptEnsemble.records (FinalMemoryReceipts.registerWitness (receiptWitness witness))).map
          (FinalMemoryValue.channel false).pushedValue ++
        (registerInputs witness).map (fun input => (FinalMemoryValue.channel false).pulledValue input.record) := by
  rw [private_interactions witness _ (interface.receipts false), verifier_values witness _ (by
    simp [FinalMemoryValue.channel, OrderedBoundary.channel, OrderedFinalProvider.channelName, Channel.toRaw])]
  rw [if_neg (by simp [FinalMemoryValue.channel, FinalMemoryChange.channel, Channel.toRaw])]
  rw [table_silent ramFinalSlot witness _ (by rfl), table_silent terminalSlot witness _ (by rfl),
    table_silent ramSlot witness _ (by rfl), register_pulls]
  rw [← registerFinalTable_eq, FinalMemoryReceipts.register_receipts (receiptWitness witness)]
  simp only [List.nil_append, List.append_nil]

/-- The complete RAM receipt ledger, in physical row order. -/
theorem ram_ledger (witness : EnsembleWitness (ensemble source target auxiliary channels))
    (interface : Interface auxiliary) :
    witness.interactionsWith (FinalMemoryValue.channel true).toRaw =
      (FinalReceiptEnsemble.records (receiptWitness witness)).map (FinalMemoryValue.channel true).pushedValue ++
        (ramInputs witness).map (fun input => (FinalMemoryValue.channel true).pulledValue input.value.record) := by
  rw [private_interactions witness _ (interface.receipts true), verifier_values witness _ (by
    simp [FinalMemoryValue.channel, OrderedBoundary.channel, OrderedFinalProvider.channelName, Channel.toRaw])]
  rw [if_neg (by simp [FinalMemoryValue.channel, FinalMemoryChange.channel, Channel.toRaw])]
  rw [table_silent registerFinalSlot witness _ (by rfl), table_silent terminalSlot witness _ (by rfl),
    table_silent registerSlot witness _ (by rfl), ram_pulls]
  rw [← ramFinalTable_eq, FinalMemoryReceipts.ram_receipts (receiptWitness witness)]
  simp only [List.nil_append, List.append_nil]

/-- Register receipt balance matches every finalizer record with exactly one validator input. -/
theorem register_receipts_perm (witness : EnsembleWitness (ensemble source target auxiliary channels))
    (interface : Interface auxiliary) (balanced : witness.BalancedChannels) :
    ((registerInputs witness).map (·.record)).Perm
      (FinalReceiptEnsemble.records (FinalMemoryReceipts.registerWitness (receiptWitness witness))) := by
  have balance := balanced (FinalMemoryValue.channel false).toRaw (by
    simp [ensemble, ClosedVerifier.install, base, FinalMemoryReceipts.ensemble,
      FinalMemoryReceipts.withRegisters, FinalReceiptEnsemble.install])
  change BalancedInteractions (witness.interactionsWith (FinalMemoryValue.channel false).toRaw) at balance
  rw [register_ledger witness interface] at balance
  exact ((FinalMemoryValue.channel false).balanced_unit_iff _ _).mp
    (by simpa only [List.map_map, Function.comp_def] using balance) |>.2.symm

/-- RAM receipt balance preserves complete values, addresses, and timestamps. -/
theorem ram_receipts_perm (witness : EnsembleWitness (ensemble source target auxiliary channels))
    (interface : Interface auxiliary) (balanced : witness.BalancedChannels) :
    ((ramInputs witness).map (fun input => input.value.record)).Perm
      (FinalReceiptEnsemble.records (receiptWitness witness)) := by
  have balance := balanced (FinalMemoryValue.channel true).toRaw (by
    simp [ensemble, ClosedVerifier.install, base, FinalMemoryReceipts.ensemble,
      FinalMemoryReceipts.withRegisters, FinalReceiptEnsemble.install])
  change BalancedInteractions (witness.interactionsWith (FinalMemoryValue.channel true).toRaw) at balance
  rw [ram_ledger witness interface] at balance
  exact ((FinalMemoryValue.channel true).balanced_unit_iff _ _).mp
    (by simpa only [List.map_map, Function.comp_def] using balance) |>.2.symm

/-- One common accounting view of the two actual validator tables. -/
def validationRows (witness : EnsembleWitness (ensemble source target auxiliary channels)) :
    List (FinalMemoryChangeCoverage.Row p) :=
  (registerInputs witness).map (fun input => (false, input)) ++
    (ramInputs witness).map (fun input => (true, ⟨input.value.record, input.selected⟩))

/-- Complete receipt balance identifies the validated inventory with the original final decoder. -/
theorem receipts_perm (witness : EnsembleWitness (ensemble source target auxiliary channels))
    (interface : Interface auxiliary) (balanced : witness.BalancedChannels) :
    ((validationRows witness).map fun row => row.2.record).Perm (records witness) := by
  rw [records, FinalMemoryReceipts.records_eq (receiptWitness witness)]
  simpa only [validationRows, List.map_append, List.map_map, Function.comp_def] using
    (register_receipts_perm witness interface balanced).append (ram_receipts_perm witness interface balanced)

/-- Every physical change occurrence is accounted for, including the verifier and disabled rows. -/
theorem changes_ledger (witness : EnsembleWitness (ensemble source target auxiliary channels))
    (interface : Interface auxiliary) :
    (witness.interactionsWith FinalMemoryChange.channel.toRaw).Perm
      (FinalMemoryChangeCoverage.ledger source target (validationRows witness)) := by
  rw [private_interactions witness _ interface.changes, verifier_values witness _ (by
    simp [FinalMemoryChange.channel, OrderedBoundary.channel, OrderedFinalProvider.channelName, Channel.toRaw])]
  rw [if_pos rfl, table_silent registerFinalSlot witness _ (by rfl),
    table_silent ramFinalSlot witness _ (by rfl), table_silent terminalSlot witness _ (by rfl),
    register_changes, ram_changes]
  simp only [FinalMemoryChangeCoverage.ledger, validationRows, List.map_append,
    List.map_map, Function.comp_def, List.append_nil, List.append_assoc]
  exact List.perm_append_comm.trans (List.Perm.of_eq (List.append_assoc ..))

/-- Actual full-ensemble balance closes the complete change ledger. -/
theorem changes_balanced (witness : EnsembleWitness (ensemble source target auxiliary channels))
    (interface : Interface auxiliary) (balanced : witness.BalancedChannels) :
    BalancedInteractions (FinalMemoryChangeCoverage.ledger source target (validationRows witness)) := by
  apply balancedInteractions_of_perm (balanced FinalMemoryChange.channel.toRaw ?_)
    (changes_ledger witness interface)
  apply List.mem_append_right
  exact List.mem_append_right _ (List.mem_cons_self ..)

end SP1Clean.Soundness.FinalMemoryChecks
