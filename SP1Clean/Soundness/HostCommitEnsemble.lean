import SP1Clean.Soundness.HostCommitBank
import ToClean.Air.EnsembleBuild

/-! # A commitment bank bound by its actual Clean verifier

This composable ensemble registers the eight update tables and their terminal. Public input is
only the final bank words; genesis and the terminal clock are fixed by the verifier. Auxiliary
components may supply calls and Byte providers, but cannot write the private bank channel.
The soundness theorem derives local specs and endpoint balance from constraints and the actual
balanced ledger. Its auxiliary premises are static circuit-interface/provider proofs, not
witness-specific semantic boundary facts. Installation in the mixed machine remains separate.
-/

namespace SP1Clean.Soundness.HostCommitEnsemble

open Circuit Air.Flat HostCommitChip Model.Core HostCommitBank

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def ensemble (deferred : Bool) (auxiliary : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p))) : Ensemble (ZMod p) (ProvableVector Word 8) where
  tables := components deferred ++ auxiliary
  channels := (stateChannel deferred).toRaw :: Channels.byteChannel.toRaw ::
    HostCallChip.channel.toRaw :: Channels.publicValuesChannel.toRaw :: channels
  verifier := HostCommitBoundary.verifier deferred
  verifier_length_zero := by intros; rfl

variable {deferred : Bool} {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}

abbrev Witness := EnsembleWitness (ensemble deferred auxiliary channels)

def bankTables (witness : Witness (p := p) (deferred := deferred) (auxiliary := auxiliary) (channels := channels)) :=
  witness.tables.take (components (p := p) deferred).length

theorem tables_aligned (witness : Witness (p := p) (deferred := deferred) (auxiliary := auxiliary) (channels := channels)) :
    List.Forall₂ (fun index table => (view deferred index).component = table.component) indices (bankTables witness) := by
  have viewsAligned : List.Forall₂ (fun view table => view.component = table.component)
      (views deferred) (bankTables witness) := by
    apply TransitionView.aligned_of_map_eq
    have same := congrArg (List.take (components (p := p) deferred).length) witness.tables_map_component
    simpa only [← List.map_take, ensemble, List.take_left', HostCommitBank.components, List.length_map, bankTables] using same.symm
  simpa only [views, List.forall₂_map_left_iff] using viewsAligned

theorem auxiliary_silent (witness : Witness (p := p) (deferred := deferred) (auxiliary := auxiliary) (channels := channels))
    (privateChannel : ∀ component ∈ auxiliary, (stateChannel deferred).toRaw ∉ component.circuit.channels) :
    (witness.tables.drop (components (p := p) deferred).length).flatMap
      (·.interactionsWith (stateChannel deferred).toRaw) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro table member
  have same := congrArg (List.drop (components (p := p) deferred).length) witness.tables_map_component
  have mapped : (witness.tables.drop (components (p := p) deferred).length).map (·.component) = auxiliary := by
    simpa only [← List.map_drop, ensemble, List.drop_left'] using same
  have componentMem := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
  rw [mapped] at componentMem
  rw [Table.interactionsWith_eq_filter]
  apply List.filter_eq_nil_iff.mpr
  intro interaction member equal
  have sameChannel : interaction.channel = (stateChannel deferred).toRaw := by simpa using equal
  exact privateChannel table.component componentMem
    (sameChannel ▸ table.channel_mem_channels_of_mem_interactions interaction member)

/-- Public bank values are taken from the physical verifier row, without a boundary premise. -/
theorem interactions_eq (witness : Witness (p := p) (deferred := deferred) (auxiliary := auxiliary) (channels := channels))
    (privateChannel : ∀ component ∈ auxiliary, (stateChannel deferred).toRaw ∉ component.circuit.channels) :
    witness.interactionsWith (stateChannel deferred).toRaw =
      [(stateChannel deferred).pushedValue HostCommitBoundary.initial,
       (stateChannel deferred).pulledValue (HostCommitBoundary.final witness.publicInput)] ++
        (bankTables witness).flatMap (·.interactionsWith (stateChannel deferred).toRaw) := by
  rw [EnsembleWitness.interactionsWith, EnsembleWitness.allTables, List.flatMap_cons]
  have verifier : witness.verifierTable.interactionsWith (stateChannel deferred).toRaw =
      [(stateChannel deferred).pushedValue HostCommitBoundary.initial,
       (stateChannel deferred).pulledValue (HostCommitBoundary.final witness.publicInput)] := by
    simp only [Table.interactionsWith, EnsembleWitness.verifierTable_flatMap,
      Operations.interactionValuesWith, EnsembleWitness.verifierTable_component,
      Ensemble.verifierTable_interactionsWith]
    change ((HostCommitBoundary.verifierMain deferred (varFromOffset (ProvableVector Word 8) 0)).operations
      (size (ProvableVector Word 8))).interactionValuesWith (stateChannel deferred).toRaw _ = _
    rw [HostCommitBoundary.verifier_values, EnsembleWitness.verifierTable_environment,
      ProvableType.eval_fromInput_varFromOffset_zero]
  rw [verifier]
  have split := List.take_append_drop (components (p := p) deferred).length witness.tables
  rw [← split, List.flatMap_append, auxiliary_silent witness privateChannel, List.append_nil]
  rfl

private theorem bank_byte_requirements (index : Index) (env : Environment (ZMod p))
    (constraints : (view (p := p) deferred index).component.operations.ConstraintsHold env) :
    (view deferred index).component.operations.ChannelRequirements Channels.byteChannel.toRaw env := by
  apply Operations.requirements_of_not_mem _ _ _
    ((view deferred index).component.inChannelsOrRequirements_of_constraints env constraints)
  cases index with
  | none => simp [view, terminalView, HostCommitBoundary.terminal, stateChannel, Channels.byteChannel, circuit_norm]
  | some slot => simp [view, HostCommitHistory.view, HostCommitChip.circuit,
      stateChannel, HostCallChip.channel, Channels.byteChannel, Channels.publicValuesChannel, circuit_norm]

/-- The bank's Byte guarantees follow from actual ensemble balance and its auxiliary providers. -/
theorem byte_guarantees (witness : Witness (p := p) (deferred := deferred) (auxiliary := auxiliary) (channels := channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (providers : ∀ component ∈ auxiliary, ∀ env, component.operations.ConstraintsHold env →
      component.operations.ChannelRequirements Channels.byteChannel.toRaw env) :
    ∀ table ∈ witness.allTables, table.ChannelGuarantees Channels.byteChannel.toRaw := by
  apply witness.channelGuarantees_of_component_requirements Channels.byteChannel.toRaw constraints
    (balanced _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  intro component member env checked
  simp only [Ensemble.allTables, ensemble, List.mem_cons, List.mem_append] at member
  rcases member with rfl | bank | auxiliary
  · apply Operations.requirements_of_not_mem _ _ _
      ((ensemble deferred auxiliary channels).verifierTable.inChannelsOrRequirements_of_constraints env checked)
    simp [ensemble, Ensemble.verifierTable, HostCommitBoundary.verifier, stateChannel, Channels.byteChannel, circuit_norm]
  · obtain ⟨bankView, member, rfl⟩ := List.mem_map.mp bank
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact bank_byte_requirements index env checked
  · exact providers component auxiliary env checked

/-- Constraints and balance authenticate the public bank as the result of all its physical calls.
The auxiliary interface proofs can be discharged once when this subsystem is installed. -/
theorem sound (witness : Witness (p := p) (deferred := deferred) (auxiliary := auxiliary) (channels := channels))
    (privateChannel : ∀ component ∈ auxiliary, (stateChannel deferred).toRaw ∉ component.circuit.channels)
    (providers : ∀ component ∈ auxiliary, ∀ env, component.operations.ConstraintsHold env →
      component.operations.ChannelRequirements Channels.byteChannel.toRaw env)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (policy : HostPolicy) (characteristic : policy.characteristic = p)
    (context : HostReadContext) (host : HostState) :
    ∃ path : List (Row (p := p)),
      path.Perm (TransitionView.readIndexedRows indices (bankTables witness)) ∧
      Walk.IsWalk (edge deferred) HostCommitBoundary.initial (HostCommitBoundary.final witness.publicInput) path ∧
      path.foldlM (execute deferred policy context) ((HostCommitBoundary.initial (p := p)).apply deferred host) =
        some ((HostCommitBoundary.final witness.publicInput).apply deferred host) := by
  have inAll (table : Table (ZMod p)) (member : table ∈ bankTables witness) : table ∈ witness.allTables :=
    witness.mem_allTables_of_mem_tables (List.mem_of_mem_take member)
  apply ordered_history deferred (bankTables witness) witness.publicInput (tables_aligned witness)
    (fun table member => constraints table (inAll table member))
    (fun table member => byte_guarantees witness constraints balanced providers table (inAll table member))
    _ policy characteristic context host
  have bank := balanced (stateChannel deferred).toRaw (List.mem_cons_self ..)
  change BalancedInteractions (witness.interactionsWith (stateChannel deferred).toRaw) at bank
  rwa [interactions_eq witness privateChannel] at bank

end SP1Clean.Soundness.HostCommitEnsemble
