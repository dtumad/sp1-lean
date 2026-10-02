import SP1Clean.Soundness.FinalMemoryReceipts
import SP1Clean.Soundness.FinalMemoryChangeCoverage
import SP1Clean.Native.Operations.FinalRegisterCheck
import SP1Clean.Native.Operations.FinalRamCheck
import SP1Clean.Native.Operations.FinalMemoryChangeBoundary
import ToClean.Air.TableSlot

/-! # Physical assembly of complete target Memory checks

The original three ordered final tables are retained, with their full-record receipts. Two
target-check tables consume those receipts and contribute selected tagged changes. The verifier
owns the canonical change demand. Auxiliary tables supply execution Memory and Byte resources;
their static interface must keep the three boundary receipt channels private.

`FinalMemoryEnsemble.records` remains the decoder of the final inventory. Forgetting the closed
verifier below is only a physical proof view: no full balance is asserted for that view.
-/

namespace SP1Clean.Soundness.FinalMemoryChecks

open Circuit Air.Flat Channels Model.Core Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Existing value/selection subcircuits, in their registered physical order. -/
def checkTables (target : MemorySnapshot) : List (Component (ZMod p)) :=
  [{ circuit := FinalRegisterCheck.circuit target }, { circuit := FinalRamCheck.circuit target }]

/-- The five fixed boundary components have distinct names for every target snapshot. -/
theorem empty_unique_names (target : MemorySnapshot) :
    (((FinalMemoryEnsemble.inventory (p := p)).views.map TransitionView.component ++
      (checkTables (p := p) target ++ [])).map
        (fun component : Component (ZMod p) => component.circuit.name)).Nodup :=
  of_decide_eq_true rfl

/-- Receipt-bearing finalizers with both target-check tables installed. -/
@[reducible] def base (target : MemorySnapshot) (auxiliary : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p)))
    (names : (((FinalMemoryEnsemble.inventory (p := p)).views.map TransitionView.component ++
      (checkTables (p := p) target ++ auxiliary)).map
        (fun component : Component (ZMod p) => component.circuit.name)).Nodup) :
    Ensemble (ZMod p) unit :=
  FinalMemoryReceipts.ensemble (checkTables target ++ auxiliary)
    (byteChannel.toRaw :: memoryChannel.toRaw ::
      auxiliary.flatMap (fun component => component.circuit.channels) ++ channels) names

/-- The complete canonical change inventory is invoked exactly once by the verifier. -/
def ensemble (source target : MemorySnapshot) (auxiliary : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p)))
    (names : (((FinalMemoryEnsemble.inventory (p := p)).views.map TransitionView.component ++
      (checkTables (p := p) target ++ auxiliary)).map
        (fun component : Component (ZMod p) => component.circuit.name)).Nodup) :
    Ensemble (ZMod p) unit :=
  (FinalMemoryChangeBoundary.closed source target).install (base target auxiliary channels names)

/-- The concrete prefix is a proved view of the existing finalizer/check registrations. -/
theorem tables_eq (source target : MemorySnapshot) (auxiliary : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p)))
    (names : (((FinalMemoryEnsemble.inventory (p := p)).views.map TransitionView.component ++
      (checkTables (p := p) target ++ auxiliary)).map
        (fun component : Component (ZMod p) => component.circuit.name)).Nodup) :
    (ensemble source target auxiliary channels names).tables =
      [{ circuit := FinalMemoryReceipt.circuit false OrderedFinalProvider.registerCircuit },
       { circuit := FinalMemoryReceipt.circuit true OrderedFinalProvider.ramCircuit },
       (FinalMemoryEnsemble.viewFor .terminal).component,
       { circuit := FinalRegisterCheck.circuit target }, { circuit := FinalRamCheck.circuit target }] ++ auxiliary := rfl

variable {source target : MemorySnapshot} {auxiliary : List (Component (ZMod p))}
  {channels : List (RawChannel (ZMod p))}
variable {names : (((FinalMemoryEnsemble.inventory (p := p)).views.map TransitionView.component ++
      (checkTables (p := p) target ++ auxiliary)).map
        (fun component : Component (ZMod p) => component.circuit.name)).Nodup}

/-- Receipt-bearing register finalizer at its preserved position. -/
def registerFinalSlot : TableSlot (ensemble source target auxiliary channels names).tables
    { circuit := FinalMemoryReceipt.circuit false OrderedFinalProvider.registerCircuit } where
  index := ⟨0, by rw [tables_eq]; simp⟩
  component_eq := rfl

/-- Receipt-bearing RAM finalizer at its preserved position. -/
def ramFinalSlot : TableSlot (ensemble source target auxiliary channels names).tables
    { circuit := FinalMemoryReceipt.circuit true OrderedFinalProvider.ramCircuit } where
  index := ⟨1, by rw [tables_eq]; simp⟩
  component_eq := rfl

/-- The existing final-order terminal, with no value receipt. -/
def terminalSlot : TableSlot (ensemble source target auxiliary channels names).tables
    (FinalMemoryEnsemble.viewFor .terminal).component where
  index := ⟨2, by rw [tables_eq]; simp⟩
  component_eq := rfl

/-- The target-register consumer is selected from the original physical inventory. -/
def registerSlot : TableSlot (ensemble source target auxiliary channels names).tables
    { circuit := FinalRegisterCheck.circuit target } where
  index := ⟨3, by rw [tables_eq]; simp⟩
  component_eq := rfl

/-- The target-RAM consumer is selected from the original physical inventory. -/
def ramSlot : TableSlot (ensemble source target auxiliary channels names).tables
    { circuit := FinalRamCheck.circuit target } where
  index := ⟨4, by rw [tables_eq]; simp⟩
  component_eq := rfl

/-- Forget only the closed verifier; all tables, rows, data and public input remain literal. -/
def receiptWitness (witness : EnsembleWitness (ensemble source target auxiliary channels names)) :
    EnsembleWitness (base target auxiliary channels names) :=
  (FinalMemoryChangeBoundary.closed source target).project witness

/-- The authoritative ordered final inventory, decoded through its existing implementation. -/
def records (witness : EnsembleWitness (ensemble source target auxiliary channels names)) :
    List (MemoryMsg (ZMod p)) :=
  FinalMemoryEnsemble.records (FinalMemoryReceipts.original (receiptWitness witness))

/-- The receipt proof view uses the actual shared fixed-lookup environment. -/
theorem receiptWitness_data (witness : EnsembleWitness (ensemble source target auxiliary channels names)) :
    (receiptWitness witness).data = witness.data :=
  (FinalMemoryChangeBoundary.closed source target).project_data witness

theorem ramFinalTable_eq (witness : EnsembleWitness (ensemble source target auxiliary channels names)) :
    FinalMemoryReceipts.ramTable (receiptWitness witness) = ramFinalSlot.table witness := rfl

theorem registerFinalTable_eq (witness : EnsembleWitness (ensemble source target auxiliary channels names)) :
    FinalMemoryReceipts.registerTable (receiptWitness witness) = registerFinalSlot.table witness := by
  simp only [FinalMemoryReceipts.registerTable, FinalMemoryReceipts.registerWitness,
    FinalReceiptEnsemble.project, FinalReceiptEnsemble.table, TableSlot.table,
    FinalReceiptEnsemble.slot, EnsembleWitness.ofTables_tables, receiptWitness,
    List.getElem_set_ne (by decide : 1 ≠ 0), registerFinalSlot, ClosedVerifier.project]
  rfl

private theorem head_tables (witness : EnsembleWitness (ensemble source target auxiliary channels names)) :
    witness.tables.take 5 = [registerFinalSlot.table witness, ramFinalSlot.table witness,
      terminalSlot.table witness, registerSlot.table witness, ramSlot.table witness] := by
  have length : 5 ≤ witness.tables.length := by
    rw [← witness.same_length, tables_eq]
    simp
  rw [List.take_succ_eq_append_getElem (by omega : 4 < witness.tables.length),
    List.take_succ_eq_append_getElem (by omega : 3 < witness.tables.length),
    List.take_succ_eq_append_getElem (by omega : 2 < witness.tables.length),
    List.take_succ_eq_append_getElem (by omega : 1 < witness.tables.length),
    List.take_succ_eq_append_getElem (by omega : 0 < witness.tables.length)]
  rfl

private theorem auxiliary_silent (witness : EnsembleWitness (ensemble source target auxiliary channels names))
    (channel : RawChannel (ZMod p))
    (silent : ∀ component ∈ auxiliary, channel ∉ component.circuit.channels) :
    (witness.tables.drop 5).flatMap (·.interactionsWith witness.data channel) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro table member
  have component := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
  rw [List.map_drop, witness.tables_map_component, tables_eq] at component
  exact table.interactionsWith_nil_of_channel_not_mem (silent table.component component)

/-- A boundary-private channel retains precisely the verifier and all five registered tables. -/
theorem private_interactions (witness : EnsembleWitness (ensemble source target auxiliary channels names))
    (channel : RawChannel (ZMod p))
    (silent : ∀ component ∈ auxiliary, channel ∉ component.circuit.channels) :
    witness.interactionsWith channel = witness.verifierInteractionsWith channel ++
      (registerFinalSlot.table witness).interactionsWith witness.data channel ++
      (ramFinalSlot.table witness).interactionsWith witness.data channel ++
      (terminalSlot.table witness).interactionsWith witness.data channel ++
      (registerSlot.table witness).interactionsWith witness.data channel ++
      (ramSlot.table witness).interactionsWith witness.data channel := by
  simp only [EnsembleWitness.interactionsWith, EnsembleWitness.tableContext,
    TableContext.interactionsWith]
  rw [← List.take_append_drop 5 witness.tables, List.flatMap_append,
    auxiliary_silent witness channel silent, List.append_nil, head_tables]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

/-- Raw acceptance retains all original finalizer/check constraints when the closed demand
is forgotten. This does not project balance on the newly installed change channel. -/
theorem receiptWitness_constraints
    (witness : EnsembleWitness (ensemble source target auxiliary channels names))
    (checked : witness.Constraints) : (receiptWitness witness).Constraints :=
  (FinalMemoryChangeBoundary.closed source target).project_constraints witness |>.mp checked

/-- Static resource obligations; none depends on a witness or a semantic execution. -/
structure Interface (auxiliary : List (Component (ZMod p))) : Prop where
  /-- Byte providers establish their own requirements from local constraints. -/
  byte : ∀ component ∈ auxiliary, ∀ env, component.operations.ConstraintsHold env →
    component.operations.ChannelRequirements byteChannel.toRaw env
  /-- Only the installed finalizers and validators may use the two complete-record channels. -/
  receipts : ∀ ram, ∀ component ∈ auxiliary,
    (FinalMemoryValue.channel ram).toRaw ∉ component.circuit.channels
  /-- Only the installed validators and verifier may use changed-location receipts. -/
  changes : ∀ component ∈ auxiliary,
    FinalMemoryChange.channel.toRaw ∉ component.circuit.channels

/-- Extending the physical resources cannot omit their channels from acceptance. -/
theorem auxiliary_channel_registered (component : Component (ZMod p))
    (member : component ∈ auxiliary) (channel : RawChannel (ZMod p))
    (used : channel ∈ component.circuit.channels) :
    channel ∈ (ensemble source target auxiliary channels names).channels := by
  have present : channel ∈ auxiliary.flatMap (fun component => component.circuit.channels) :=
    List.mem_flatMap.mpr ⟨component, member, used⟩
  simp only [ensemble, ClosedVerifier.install, ClosedVerifier.withInteractions, base, FinalMemoryReceipts.ensemble,
    FinalMemoryReceipts.withRegisters, FinalReceiptEnsemble.install, Ensemble.replaceComponent,
    FinalMemoryEnsemble.ensemble,
    OrderedMemoryEnsemble.Inventory.ensemble, OrderedBoundaryEnsemble.ensemble,
    List.mem_append, List.mem_cons]
  tauto

private theorem byte_requirements (interface : Interface auxiliary)
    (component : Component (ZMod p))
    (member : component ∈ (ensemble source target auxiliary channels names).tables)
    (env : Environment (ZMod p)) (checked : component.operations.ConstraintsHold env) :
    component.operations.ChannelRequirements byteChannel.toRaw env := by
  let nativeTables : List (Component (ZMod p)) :=
    [{ circuit := FinalMemoryReceipt.circuit false OrderedFinalProvider.registerCircuit },
     { circuit := FinalMemoryReceipt.circuit true OrderedFinalProvider.ramCircuit },
     (FinalMemoryEnsemble.viewFor .terminal).component,
     { circuit := FinalRegisterCheck.circuit target }, { circuit := FinalRamCheck.circuit target }]
  have split : component ∈ nativeTables ∨ component ∈ auxiliary := by
    simpa only [tables_eq, List.mem_append] using member
  rcases split with native | resource
  · apply Operations.requirements_of_not_mem _ _ _
      (component.inChannelsOrRequirements_of_constraints env checked)
    have silent : nativeTables.all (fun component =>
        !(component.circuit.channelsWithRequirements.map RawChannel.name).contains "SP1Byte") = true := rfl
    have valid := List.all_eq_true.mp silent component native
    intro used
    have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
    change (component.circuit.channelsWithRequirements.map RawChannel.name).contains "SP1Byte" = true at present
    rw [present] at valid
    contradiction
  · exact interface.byte component resource env checked

/-- Close Byte from its actual channel without assuming other ledgers are balanced. -/
theorem byte_guarantees_of_balancedChannel (witness : EnsembleWitness (ensemble source target auxiliary channels names))
    (interface : Interface auxiliary) (checked : witness.Constraints)
    (balanced : witness.BalancedChannel byteChannel.toRaw) :
    ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw := by
  apply (witness.channelGuarantees_of_component_requirements byteChannel.toRaw checked
    balanced ?_ (byte_requirements interface)).2
  intro input data
  apply Ensemble.verifierChannelRequirements_of_not_mem
  have noAssertions : (FinalMemoryChangeBoundary.closed (p := p) source target).operations.constraints = [] :=
    FinalMemoryChangeBoundary.raw_constraints _ _
  change byteChannel.toRaw ∉
    ((OrderedBoundaryVerifier.verifierProgram OrderedFinalProvider.channelName
      OrderedMemoryEnsemble.startKey OrderedMemoryEnsemble.endKey).andThen
      ((FinalMemoryChangeBoundary.closed source target).program
        (base target auxiliary channels names))).channelsWithRequirements
  simp only [Verifier.Program.channelsWithRequirements, Verifier.Program.operations,
    Verifier.Program.andThen, Verifier.operations_bind, ClosedVerifier.program,
    noAssertions, Verifier.checkZeros_operations, List.flatMap_nil, List.append_nil]
  simp [ClosedVerifier.emit, ClosedVerifier.operations, FinalMemoryChangeBoundary.closed,
    FinalMemoryChangeBoundary.circuit, FinalMemoryChangeBoundary.raw_interactions,
    OrderedBoundaryVerifier.verifierProgram, OrderedBoundaryVerifier.main, Verifier.ofInteractions,
    OrderedBoundary.channel, OrderedFinalProvider.channelName, FinalMemoryChange.channel, byteChannel, circuit_norm]

/-- Target reads stay inside the actual Byte ledger. Its own constraints and balance supply
their guarantees, together with those of the finalizers and every auxiliary table. -/
theorem byte_guarantees (witness : EnsembleWitness (ensemble source target auxiliary channels names))
    (interface : Interface auxiliary) (checked : witness.Constraints)
    (balanced : witness.BalancedChannels) :
    ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw := by
  apply byte_guarantees_of_balancedChannel witness interface checked (balanced _ ?_)
  simp [ensemble, ClosedVerifier.install, ClosedVerifier.withInteractions, base, FinalMemoryReceipts.ensemble,
    FinalMemoryReceipts.withRegisters, FinalReceiptEnsemble.install, Ensemble.replaceComponent,
    FinalMemoryEnsemble.ensemble,
    OrderedMemoryEnsemble.Inventory.ensemble, OrderedBoundaryEnsemble.ensemble]

/-- Decode only the inputs of the actual registered register-check rows. -/
def registerInputs (witness : EnsembleWitness (ensemble source target auxiliary channels names)) :
    List (FinalRegisterCheck.Inputs (ZMod p)) :=
  (registerSlot.table witness).table.map fun row =>
    ({ circuit := FinalRegisterCheck.circuit target } : Component (ZMod p)).rowInput
      (Environment.fromArray row witness.data)

/-- Decode only the inputs of the actual registered RAM-check rows. -/
def ramInputs (witness : EnsembleWitness (ensemble source target auxiliary channels names)) :
    List (FinalRamCheck.Inputs (ZMod p)) :=
  (ramSlot.table witness).table.map fun row =>
    ({ circuit := FinalRamCheck.circuit target } : Component (ZMod p)).rowInput
      (Environment.fromArray row witness.data)

private theorem check_spec (component : Component (ZMod p)) (member : component ∈ checkTables target)
    (env : Environment (ZMod p)) (checked : component.operations.ConstraintsHold env)
    (bytes : component.operations.ChannelGuarantees byteChannel.toRaw env) : component.Spec env := by
  have assumptions : component.CircuitAssumptions env := by
    simp only [checkTables, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> trivial
  have used : component.circuit.channelsWithGuarantees ⊆
      [byteChannel.toRaw, (FinalMemoryValue.channel false).toRaw,
        (FinalMemoryValue.channel true).toRaw, FinalMemoryChange.channel.toRaw] := by
    simp only [checkTables, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      simp [FinalRegisterCheck.circuit, FinalRamCheck.circuit, FinalRegisterValue.circuit,
        FinalRamValue.circuit, circuit_norm]
  apply (Component.weakSoundness assumptions checked ?_).1
  rw [Operations.guarantees_iff _ _ _ (component.inChannelsOrGuarantees env)]
  intro channel member
  rcases List.mem_cons.mp (used member) with rfl | member
  · exact bytes
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;>
      exact Operations.channelGuarantees_of_trivial _ (by
        simp [FinalMemoryValue.channel, FinalMemoryChange.channel, Channel.toRaw]) _ _

/-- Registered target contracts inherit Byte guarantees from the complete enclosing assembly. -/
theorem registerInputs_spec_of_byte (witness : EnsembleWitness (ensemble source target auxiliary channels names))
    (checked : witness.Constraints)
    (byte : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw) :
    ∀ input ∈ registerInputs witness, FinalRegisterCheck.Spec target input := by
  intro input member
  obtain ⟨row, present, rfl⟩ := List.mem_map.mp member
  have constraints := (registerSlot.table_constraints witness checked) row present
  have bytes := (registerSlot.table_channelGuarantees witness byteChannel.toRaw
    byte) row present
  rw [registerSlot.table_component witness] at constraints bytes
  exact check_spec (target := target) _ (by simp [checkTables]) _ constraints bytes

/-- Authenticate target RAM reads with inherited Byte guarantees, retaining their physical rows. -/
theorem ramInputs_spec_of_byte (witness : EnsembleWitness (ensemble source target auxiliary channels names))
    (checked : witness.Constraints)
    (byte : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw) :
    ∀ input ∈ ramInputs witness, FinalRamCheck.Spec target input := by
  intro input member
  obtain ⟨row, present, rfl⟩ := List.mem_map.mp member
  have constraints := (ramSlot.table_constraints witness checked) row present
  have bytes := (ramSlot.table_channelGuarantees witness byteChannel.toRaw
    byte) row present
  rw [ramSlot.table_component witness] at constraints bytes
  exact check_spec (target := target) _ (by simp [checkTables]) _ constraints bytes

/-- Raw constraints and the complete Byte closure prove all registered target-check contracts. -/
theorem registerInputs_spec (witness : EnsembleWitness (ensemble source target auxiliary channels names))
    (interface : Interface auxiliary) (checked : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ input ∈ registerInputs witness, FinalRegisterCheck.Spec target input :=
  registerInputs_spec_of_byte witness checked (byte_guarantees witness interface checked balanced)

/-- The RAM target read is authenticated by the actual assembly's Byte ledger. -/
theorem ramInputs_spec (witness : EnsembleWitness (ensemble source target auxiliary channels names))
    (interface : Interface auxiliary) (checked : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ input ∈ ramInputs witness, FinalRamCheck.Spec target input :=
  ramInputs_spec_of_byte witness checked (byte_guarantees witness interface checked balanced)

end SP1Clean.Soundness.FinalMemoryChecks
