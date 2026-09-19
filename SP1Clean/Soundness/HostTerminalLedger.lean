import SP1Clean.Soundness.HostQueueCallProjection
import SP1Clean.Soundness.HostHintReadBanks
import ToClean.Air.UnitBalance

/-! # Terminal receipts in the installed host ledger

The complete physical ledger authenticates the optional outgoing exit. Only the HALT receiver
produces a receipt; its full call remains tied to the instruction inventory by HostCall balance.
Disabled endpoint pulls remain in the original interaction-count bound.
-/

namespace SP1Clean.Soundness.HostTerminalLedger

open Circuit Air.Flat Channels Model.Core HostHintReadLocal HostQueueCallProjection

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Select the complete exit word from a HALT call. -/
def receipt? (message : HostCallChip.Message (ZMod p)) : Option (Word (ZMod p)) :=
  if Word.toBitVec64 message.code = 0 then some message.arg1 else none

omit [Fact (2 ^ 25 < p)] in
private theorem values_silent (component : Component (ZMod p)) (env : Environment (ZMod p))
    (silent : HostExitBoundary.channel.toRaw ∉ component.circuit.channels) :
    component.operations.interactionValuesWith HostExitBoundary.channel.toRaw env = [] := by
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations,
    InteractionRecovery.interactionsWith_main_eq_nil _ _ _ _ silent, List.map_nil]

private theorem control_values (receiver : HostLocalHandoff.Receiver (p := p))
    (member : receiver ∈ (HostCallReceivers.available (p := p)).take 18)
    (env : Environment (ZMod p)) (constraints : receiver.component.operations.ConstraintsHold env)
    (bytes : receiver.component.operations.ChannelGuarantees byteChannel.toRaw env) :
    receiver.component.operations.interactionValuesWith HostExitBoundary.channel.toRaw env =
      ((receipt? (receiver.message env)).toList.map HostExitBoundary.channel.pushedValue) := by
  change receiver ∈ ([HostCallReceivers.halt, HostCallReceivers.enter] ++
    (List.ofFn fun slot => HostCallReceivers.commit false slot) ++
    (List.ofFn fun slot => HostCallReceivers.commit true slot)) at member
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_ofFn] at member
  rcases member with ((rfl | rfl) | ⟨slot, rfl⟩) | ⟨slot, rfl⟩
  · have valid := HostHaltChip.component_spec_of_byte env constraints bytes
    change HostHaltChip.Spec (valueFromOffset HostHaltChip.Inputs 0 env) at valid
    rw [HostCallReceivers.halt_message]
    have arg (input : Var HostHaltChip.Inputs (ZMod p)) :
        eval env input.call.arg1 = (eval env input).call.arg1 := by
      rcases input with ⟨⟨_, _, _, _, _, _, _⟩, _⟩
      simp only [circuit_norm]
    have zero : Word.toBitVec64 (0 : Word (ZMod p)) = 0 := by simp [Word.toBitVec64, Word.toNat]
    rw [receipt?, valid.1, zero, if_pos rfl]
    simp only [Option.toList_some, List.map_cons, List.map_nil]
    simp only [HostCallReceivers.halt, Operations.interactionValuesWith, Component.interactionsWith_eq]
    exact (HostHaltChip.terminal_values _ _ env).trans (by
      rw [arg, eval_varFromOffset_valueFromOffset])
  · have valid := HostEnterChip.component_spec_of_constraints env constraints
    change HostEnterChip.Spec (valueFromOffset HostEnterChip.Inputs 0 env) at valid
    have silent : HostExitBoundary.channel.toRaw ∉ (HostCallReceivers.enter (p := p)).component.circuit.channels := by
      intro used
      have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
      change false = true at present
      contradiction
    rw [values_silent _ env silent]
    rw [HostCallReceivers.enter_message]
    have three : (3 : ZMod p).val = 3 :=
      ZMod.val_natCast_of_lt (show (3 : ℕ) < p by have := Fact.out (p := 2 ^ 17 < p); omega)
    simp [receipt?, valid.1, HostEnterChip.codeWord, Word.toBitVec64, Word.toNat, three]
  · have valid := HostCommitBank.view_spec_of_byte false (some slot) env constraints bytes
    change HostCommitChip.Spec false slot (valueFromOffset HostCommitChip.Inputs 0 env) at valid
    have silent : HostExitBoundary.channel.toRaw ∉ (HostCallReceivers.commit (p := p) false slot).component.circuit.channels := by
      intro used
      have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
      change false = true at present
      contradiction
    rw [values_silent _ env silent]
    rw [HostCallReceivers.commit_message]
    have sixteen : (16 : ZMod p).val = 16 :=
      ZMod.val_natCast_of_lt (show (16 : ℕ) < p by have := Fact.out (p := 2 ^ 17 < p); omega)
    simp [receipt?, valid.1.1, HostCommitChip.codeWord, Word.toBitVec64, Word.toNat, sixteen]
  · have valid := HostCommitBank.view_spec_of_byte true (some slot) env constraints bytes
    change HostCommitChip.Spec true slot (valueFromOffset HostCommitChip.Inputs 0 env) at valid
    have silent : HostExitBoundary.channel.toRaw ∉ (HostCallReceivers.commit (p := p) true slot).component.circuit.channels := by
      intro used
      have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
      change false = true at present
      contradiction
    rw [values_silent _ env silent]
    rw [HostCallReceivers.commit_message]
    have twentySix : (26 : ZMod p).val = 26 :=
      ZMod.val_natCast_of_lt (show (26 : ℕ) < p by have := Fact.out (p := 2 ^ 17 < p); omega)
    simp [receipt?, valid.1.1, HostCommitChip.codeWord, Word.toBitVec64, Word.toNat, twentySix]

omit [Fact (2 ^ 25 < p)] in
private theorem receiver_values (receivers : List (HostLocalHandoff.Receiver (p := p)))
    (tables : List (Table (ZMod p)))
    (aligned : List.Forall₂ (fun receiver table => receiver.component = table.component) receivers tables)
    (select : HostCallChip.Message (ZMod p) → Option (Word (ZMod p)))
    (rowValues : ∀ receiver ∈ receivers, ∀ env,
      receiver.component.operations.ConstraintsHold env →
      receiver.component.operations.ChannelGuarantees byteChannel.toRaw env →
      receiver.component.operations.interactionValuesWith HostExitBoundary.channel.toRaw env =
        ((select (receiver.message env)).toList.map HostExitBoundary.channel.pushedValue))
    (constraints : ∀ table ∈ tables, table.Constraints)
    (bytes : ∀ table ∈ tables, table.ChannelGuarantees byteChannel.toRaw) :
    tables.flatMap (·.interactionsWith HostExitBoundary.channel.toRaw) =
      ((ReceiverView.messages receivers tables).filterMap select).map HostExitBoundary.channel.pushedValue := by
  induction aligned with
  | nil => rfl
  | @cons receiver table receivers tables same aligned ih =>
      rw [ReceiverView.messages_cons, List.filterMap_append, List.map_append, List.flatMap_cons]
      congr 1
      · simp only [Table.interactionsWith, ReceiverView.tableMessages, List.filterMap_map,
          List.map_filterMap, Function.comp_def]
        rw [List.filterMap_eq_flatMap_toList]
        apply List.flatMap_congr
        intro physical member
        rw [← same, rowValues receiver (List.mem_cons_self ..)]
        · exact (Option.toList_map ..).symm
        · rw [same]; exact constraints table (List.mem_cons_self ..) physical member
        · rw [same]; exact bytes table (List.mem_cons_self ..) physical member
      · exact ih (fun receiver member => rowValues receiver (List.mem_cons_of_mem _ member))
          (fun table member => constraints table (List.mem_cons_of_mem _ member))
          (fun table member => bytes table (List.mem_cons_of_mem _ member))

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {resources : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}

private theorem controls_interactions
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    (controlTables witness).flatMap (·.interactionsWith HostExitBoundary.channel.toRaw) =
      ((ReceiverView.messages ((HostCallReceivers.available (p := p)).take 18)
        (controlTables witness)).filterMap receipt?).map HostExitBoundary.channel.pushedValue := by
  have aligned := ReceiverView.aligned_of_map_eq ((HostCallReceivers.available (p := p)).take 18)
    (controlTables witness) (by
      simp only [controlTables, List.map_take, List.map_drop, HostLocalHandoff.receiverTables_components,
        List.map_cons, List.drop_succ_cons, List.drop_zero])
  have member (table : Table (ZMod p)) (present : table ∈ controlTables witness) : table ∈ witness.allTables :=
    witness.mem_allTables_of_mem_tables (List.mem_of_mem_drop (List.mem_of_mem_take
      (List.mem_of_mem_drop (List.mem_of_mem_take present))))
  exact receiver_values _ _ aligned receipt? (fun receiver member => control_values receiver member)
    (fun table present => constraints table (member table present))
    (fun table present => byte_guarantees witness interface constraints balanced table (member table present))

omit [Fact (2 ^ 25 < p)] in
private theorem receipt_none_of_queue (message : HostCallChip.Message (ZMod p))
    (event : HintQueue.Event) (selected : project message = some event) : receipt? message = none := by
  have nonzero : Word.toBitVec64 message.code ≠ 0 := by
    intro zero
    simp only [project, zero, queueCallEvent?, SyscallKind.code, BitVec.reduceEq, ↓reduceIte] at selected
    contradiction
  exact if_neg nonzero

private theorem queue_receipt (row : HostQueueOrder.Row (p := p))
    (valid : (HostQueueOrder.view row.1).component.Spec row.2) :
    receipt? (HostQueueCPUOrder.call row) = none :=
  receipt_none_of_queue _ _ (queue_projection row valid).2

private theorem filterMap_right {α β : Type*} (select : α → Option β)
    (all front back : List α) (permutation : all.Perm (front ++ back))
    (silent : ∀ value ∈ front, select value = none) :
    (all.filterMap select).Perm (back.filterMap select) := by
  have selected := permutation.filterMap select
  rw [List.filterMap_append, List.filterMap_eq_nil_iff.mpr silent, List.nil_append] at selected
  exact selected

private theorem calls_receipts
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels))
    (specs : ∀ table ∈ queueTables witness, table.Spec) :
    ((HostLocalHandoff.calls witness).filterMap receipt?).Perm
      ((ReceiverView.messages ((HostCallReceivers.available (p := p)).take 18)
        (controlTables witness)).filterMap receipt?) := by
  apply filterMap_right receipt? _ _ _ (calls_split witness)
  intro message member
  obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp member
  exact queue_receipt row
    (HostQueueOrder.rows_spec _ (queueTables_aligned witness) specs row rowMem)

variable {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}

private theorem auxiliary_components
    (witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)) :
    (witness.tables.drop 60).map (·.component) =
      (HostHintReadHandoff.receiver :: HostCallReceivers.available).map (·.component) ++
        (HostHintReadHandoff.wordResources ++ sourceResources source.host.io.hints) := by
  simp only [List.map_drop, witness.tables_map_component, HostHintQueueBoundary.ensemble,
    HaltPadding.install, ClosedVerifier.install, HostHintReadLocal.ensemble, HostLocalHandoff.ensemble,
    HostLocalCore.ensemble, HostLocalCore.tables]
  rw [List.drop_set_of_lt (by decide : 57 < 60),
    List.drop_left' (by simp only [List.length_set, ProtectedLocalCore.tables_length])]

private theorem auxiliary_controls
    (witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)) :
    (witness.tables.drop 60).flatMap (·.interactionsWith HostExitBoundary.channel.toRaw) =
      (controlTables (HostHintQueueBoundary.expanded witness)).flatMap
        (·.interactionsWith HostExitBoundary.channel.toRaw) := by
  have silent : ∀ table ∈ (witness.tables.drop 60).take 1 ++ (witness.tables.drop 60).drop 19,
      table.interactionsWith HostExitBoundary.channel.toRaw = [] := by
    have mapped := auxiliary_components witness
    have checked : (((HostHintReadHandoff.receiver (p := p) :: HostCallReceivers.available).map
        (fun receiver : HostLocalHandoff.Receiver (p := p) => receiver.component) ++
          (HostHintReadHandoff.wordResources ++ sourceResources source.host.io.hints)).take 1 ++
        ((HostHintReadHandoff.receiver :: HostCallReceivers.available).map
          (fun receiver : HostLocalHandoff.Receiver (p := p) => receiver.component) ++
          (HostHintReadHandoff.wordResources ++ sourceResources source.host.io.hints)).drop 19).all
        (fun component => !(component.circuit.channels.map RawChannel.name).contains
          (HostExitBoundary.channel (p := p)).toRaw.name) = true := rfl
    intro table member
    have present := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
    simp only [List.map_append, List.map_take, List.map_drop, mapped] at present
    apply table.interactionsWith_nil_of_channel_not_mem
    intro used
    have absent := List.all_eq_true.mp checked table.component present
    rw [List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)] at absent
    contradiction
  have first : ((witness.tables.drop 60).take 1).flatMap (·.interactionsWith HostExitBoundary.channel.toRaw) = [] :=
    List.flatMap_eq_nil_iff.mpr (fun table member => silent table (List.mem_append_left _ member))
  have last : ((witness.tables.drop 60).drop 19).flatMap (·.interactionsWith HostExitBoundary.channel.toRaw) = [] :=
    List.flatMap_eq_nil_iff.mpr (fun table member => silent table (List.mem_append_right _ member))
  have split := congrArg (List.flatMap (fun table : Table (ZMod p) =>
    table.interactionsWith HostExitBoundary.channel.toRaw)) (List.take_append_drop 1 (witness.tables.drop 60))
  have tail := congrArg (List.flatMap (fun table : Table (ZMod p) =>
    table.interactionsWith HostExitBoundary.channel.toRaw)) (List.take_append_drop 18 ((witness.tables.drop 60).drop 1))
  simp only [List.drop_drop] at last
  simp only [List.flatMap_append, List.drop_drop] at split tail
  rw [first, List.nil_append, ← tail, last, List.append_nil] at split
  rw [← split, controlTables, HostHintReadBanks.receiver_tables, List.drop_take, List.take_take]
  simp only [List.drop_drop, Nat.reduceSub, min_eq_left (by decide : 18 ≤ 20)]

/-- Only checked HALT calls produce terminal receipts; the fixed verifier supplies the sole pull. -/
theorem interactions
    (witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    (witness.interactionsWith HostExitBoundary.channel.toRaw).Perm
      ((((HostLocalHandoff.calls (HostHintQueueBoundary.expanded witness)).filterMap receipt?).map
        HostExitBoundary.channel.pushedValue) ++
      [HostExitBoundary.channel.pulledIfValue (if source.host.exitCode = none ∧ bankFinal.exitCode.isSome then 1 else 0)
        (HostExitBoundary.encode (bankFinal.exitCode.getD 0))]) := by
  have fresh : HostExitBoundary.channel.toRaw ∉ (LocalCore.ensemble (p := p) image source).channels := by
    intro used
    have names := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
    change false = true at names
    contradiction
  have wrapper : (HostLocalCore.hostCallTable (HostHintQueueBoundary.expanded witness)).interactionsWith
      HostExitBoundary.channel.toRaw = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    rw [HostLocalCore.hostCallTable_component]
    intro used
    have names := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
    change false = true at names
    contradiction
  have size := congrArg List.length (auxiliary_components witness)
  have count : (witness.tables.drop 60).length = 27 := by
    simp only [List.length_map] at size
    exact size
  have bound : 60 ≤ witness.tables.length := by
    simp only [List.length_drop] at count
    omega
  have split := HostLocalCore.interactions_split_new (HostHintQueueBoundary.expanded witness)
    HostExitBoundary.channel.toRaw fresh
    (by simp [HostExitBoundary.channel, WritePermissionProvider.channel, Channel.toRaw])
  rw [wrapper, List.nil_append] at split
  have tail : HostLocalCore.auxiliaryTables (HostHintQueueBoundary.expanded witness) =
      witness.tables.drop 60 ++ [(HostHintQueueBoundary.boundary source final bankFinal).singleton witness.data] :=
    HostHintQueueBoundary.expanded_drop witness 60 (by decide) bound
  simp only [tail, List.flatMap_append, auxiliary_controls, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, ClosedVerifier.singleton_interactions, HostBoundary.closed_main,
    HostBoundary.terminal_values] at split
  have checks := HostHintQueueBoundary.expanded_constraints witness constraints
  have balance := HostHintQueueBoundary.expanded_balanced witness balanced
  have interface := HostHintQueueBoundary.expanded_interface (source := source) (final := final)
    (bankFinal := bankFinal) (source_interface (p := p) source.host.io.hints)
  rw [controls_interactions _ interface checks balance] at split
  have selected := calls_receipts (HostHintQueueBoundary.expanded witness)
    (queue_specs _ interface _ (HostHintQueueBoundary.source_authentication witness constraints) checks balance)
  exact (HostHintQueueBoundary.expanded_interactions witness _).symm.trans
    ((List.Perm.of_eq split).trans ((selected.symm.map HostExitBoundary.channel.pushedValue).append_right _))

omit [Fact (2 ^ 25 < p)] in
private theorem balanced_receipts (produced : List (Word (ZMod p)))
    (source target : Option (BitVec 32))
    (balanced : BalancedInteractions (produced.map HostExitBoundary.channel.pushedValue ++
      [HostExitBoundary.channel.pulledIfValue (if source = none ∧ target.isSome then 1 else 0)
        (HostExitBoundary.encode (target.getD 0))])) :
    produced.Perm (if source = none then target.toList.map HostExitBoundary.encode else []) := by
  have active : (produced.map HostExitBoundary.channel.pushedValue).filter
      (fun interaction => decide (interaction.mult ≠ 0)) = produced.map HostExitBoundary.channel.pushedValue := by
    apply List.filter_eq_self.mpr
    intro interaction member
    obtain ⟨word, _, rfl⟩ := List.mem_map.mp member
    simp [Channel.pushedValue]
  have endpoint : [HostExitBoundary.channel.pulledIfValue (if source = none ∧ target.isSome then 1 else 0)
      (HostExitBoundary.encode (target.getD 0))].filter (fun interaction => decide (interaction.mult ≠ 0)) =
      (if source = none then target.toList.map HostExitBoundary.encode else []).map
        (HostExitBoundary.channel (p := p)).pulledValue := by
    cases source <;> cases target <;> simp [Channel.pulledIfValue, Channel.pulledValue]
  have selected := balanced.filter_nonzero
  rw [List.filter_append, active, endpoint] at selected
  exact ((HostExitBoundary.channel.balanced_unit_iff _ _).mp selected).2

/-- The actual HALT-call inventory is empty or the exact advertised terminal word. -/
theorem receipts
    (witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ((HostLocalHandoff.calls (HostHintQueueBoundary.expanded witness)).filterMap receipt?).Perm
      (if source.host.exitCode = none then bankFinal.exitCode.toList.map HostExitBoundary.encode else []) := by
  apply balanced_receipts
  apply balancedInteractions_of_perm (balanced HostExitBoundary.channel.toRaw ?_)
    (interactions witness constraints balanced)
  apply List.mem_append_right
  simp [HostHintQueueBoundary.boundary, HostBoundary.closed, HostBoundary.circuit, circuit_norm]

/-- A stopped source's supplied endpoint must retain its exact optional exit code. -/
theorem source_status
    (witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels))
    (constraints : witness.Constraints) :
    source.host.exitCode = none ∨ source.host.exitCode = bankFinal.exitCode := by
  have checked := ((HostHintQueueBoundary.boundary source final bankFinal).verifier_constraints _
    witness.publicInput witness.data).mp (EnsembleWitness.verifierConstraints_of_constraints constraints)
  have raw := ((HostHintQueueBoundary.boundary source final bankFinal).singleton_constraints witness.data).mp checked.2
  rw [HostBoundary.closed_main] at raw
  exact (HostBoundary.constraints_spec _ _ _ _ _ _ _ _ raw).2

end SP1Clean.Soundness.HostTerminalLedger
