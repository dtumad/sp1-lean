import SP1Clean.Export.WriteSourceRegistry
import SP1Clean.Soundness.HostObservedProducers
import SP1Clean.Soundness.WriteSourcePulls

/-! # Authentic Memory predecessors from the physical supervisor

Read-back publishers and the execution decoder see the same ordinary rows, with the same
incoming State and active Memory pulls. The identification uses the original physical arrays
for any final hint cursor and any host event tape.
-/

namespace SP1Clean.Export.WriteSourceRegistry

open Circuit Air.Flat Semantics Soundness Channels WriteProbe WriteProbe.AccessInventory

private abbrev Fp := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State Fp}

/-- Typed physical position of a registered read-back source before publication. -/
def originalSlot (id : Source) : TableSlot (base image source target final).tables (original id) :=
  let present := original_at image source target final id
  let valid := (List.getElem?_eq_some_iff.mp present).choose_spec
  ⟨⟨position id, (List.getElem?_eq_some_iff.mp present).choose⟩, valid⟩

/-- The original physical source arrays in their own canonical witness's data environment. -/
def raw (witness : EnsembleWitness (base image source target final)) (id : Source) : Table Fp :=
  (originalSlot id).table witness

/-- All raw source arrays come from the actual 31 registered components. -/
theorem raw_registered (witness : EnsembleWitness (base image source target final)) (id : Source) :
    (raw witness id).component = original id := (originalSlot id).table_component witness

/-- The local execution decoder retains ownership of its ordinary rows in the source registry. -/
theorem ordinary_origin (witness : EnsembleWitness (base image source target final))
    {row : DecodedInstructionRow SP1Prime}
    (member : row ∈ LocalCore.instructionRows (HostFinalMemory.coreWitness (HostObserved.baseWitness witness))) :
    ∃ id, row.chip = supportedChipFor id ∧ row.physical ∈ (raw witness (.ordinary id)).table := by
  obtain ⟨j, chipBound, _, chip, physical⟩ := position_of_mem_decodeInstructionTables member
  have bound : j < 25 := by simpa only [supportedChips_length] using chipBound
  let id := InstructionChipId.all[j]'bound
  have index : InstructionChipId.all.idxOf id = j := by
    apply InstructionChipId.all_nodup.getElem_inj_iff.mp
    exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (InstructionChipId.mem_all id))
  refine ⟨id, chip.trans ?_, ?_⟩
  · simp only [supportedChips, List.getElem_map]
    rfl
  simp only [LocalCore.instructionTables, List.getElem_take, List.getElem_drop] at physical
  have count := witness.same_length.symm.trans (HostObserved.tables_length (image := image)
    (source := source) (target := target) (final := final))
  rw [HostObserved.core_rows_before_halt witness ⟨7 + j, by omega⟩ _ (by change 7 + j < witness.tables.length; omega)] at physical
  change row.physical ∈ (witness.tables[7 + InstructionChipId.all.idxOf id]'_).table
  simpa only [index] using physical

local instance : DecidableEq Fp := FiniteField.instDecidableEq

private theorem raw_pull {xs : List (TypedInteraction (memoryChannel (p := SP1Prime)))} {prior : MemoryMsg Fp}
    (pulled : prior ∈ consumedMessages xs) :
    memoryChannel.pulledIfValue 1 prior ∈ xs.map TypedInteraction.raw := by
  obtain ⟨i, used, rfl⟩ := List.mem_map.mp pulled
  obtain ⟨member, active⟩ := List.mem_filter.mp used
  obtain ⟨direction, weight⟩ := of_decide_eq_true active
  refine List.mem_map.mpr ⟨i, member, ?_⟩
  have msg := i.message_toElements
  have channel := i.channel_eq
  generalize i.message = value at msg ⊢
  change i.raw.mult = 1 at weight
  cases h : i.raw
  simp_all only [Channel.pulledIfValue]

private theorem protected_memory (id : InstructionChipId) :
    (original (p := SP1Prime) (.ordinary id)).operations.interactionsWith memoryChannel.toRaw =
      (supportedChipFor id).table.operations.interactionsWith memoryChannel.toRaw := by
  change (ProtectedOrdinaryReceipt.component id).operations.interactionsWith _ = _
  rw [ProtectedOrdinaryReceipt.interactions id _ (by intro eq; exact Bool.noConfusion (congrArg (fun c => c.name == "SP1Memory") eq)),
    ProtectedOrdinaryReceipt.provider_interactions id _ (by intro eq; exact Bool.noConfusion (congrArg (fun c => c.name == "SP1Memory") eq))]

/-- Evaluate the existing typed input projection on the actual source array. -/
local instance (id : InstructionChipId) : ProvableType (supportedChipFor (p := SP1Prime) id).kind.Inputs :=
  (supportedChipFor (p := SP1Prime) id).kind.provableInputs

/-- Evaluate the registered output of the same instruction circuit. -/
local instance (id : InstructionChipId) : ProvableType (supportedChipFor (p := SP1Prime) id).kind.Cols :=
  (supportedChipFor (p := SP1Prime) id).kind.provableCols

private theorem incoming_meaning {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (generation : WitnessGeneration.Generation Fp Input) (provider : GeneralFormalCircuit Fp Input Output)
    (locations : AccessSupply.Layout SP1Prime Input)
    (view : Input Fp → Output Fp → Trace.RowView Fp)
    (agrees : OrdinarySources.IncomingAgrees provider locations view) (env : Environment Fp) :
    let component : Component Fp := { circuit := provider, generation, Assumptions := provider.Assumptions }
    eval env (locations.incoming (varFromOffset Input 0)) =
      statePullOfView (view (component.rowInput env) (component.rowOutput env)) := by
  have result := agrees (varFromOffset Input 0) (size Input) env
  simpa only [Component.rowInput, Component.rowOutput, circuit_norm, eval_varFromOffset_valueFromOffset] using result

private theorem ordinary_upper (id : InstructionChipId) (data : ProverData Fp) (physical : Array Fp) :
    let state := statePullMessage ((supportedChipFor id).decodeRow data physical)
    upper (.ordinary id) (Environment.fromArray physical data) = (state.clk_high, state.clk_low) := by
  let chip := supportedChipFor (p := SP1Prime) id
  have same := incoming_meaning chip.generation chip.circuit (OrdinarySources.layout id) chip.kind.view
    (OrdinarySources.incoming_agrees id) (Environment.fromArray physical data)
  exact congrArg (fun s : StateMsg Fp => (s.clk_high, s.clk_low)) same

/-- Every active predecessor read by every ordinary execution row occurs in the registered
physical source tape with that row's exact incoming State clock and original Memory word. -/
theorem ordinary_predecessor (witness : EnsembleWitness (base image source target final))
    {row : DecodedInstructionRow SP1Prime}
    (member : row ∈ LocalCore.instructionRows (HostFinalMemory.coreWitness (HostObserved.baseWitness witness)))
    (data : ProverData Fp) {prior : MemoryMsg Fp} {time : ℕ}
    (pulled : (prior, time) ∈ (row.ordinaryRowFacts data).memPulls) :
    let state := (row.ordinaryRowFacts data).statePull
    time = Semantics.StateMsg.timeNat state ∧
      (1, AccessSupply.atClock (state.clk_high, state.clk_low) prior) ∈ records (raw witness) := by
  obtain ⟨id, chip, physical⟩ := ordinary_origin witness member
  obtain ⟨msg, took, same⟩ := List.mem_map.mp pulled
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  refine ⟨rfl, ?_⟩
  have seen := raw_pull took
  rw [row.interactionsWith_raw] at seen
  let table := raw witness (.ordinary id)
  have transport : row.chip.table.operations.interactionValuesWith memoryChannel.toRaw (row.environment data) =
      table.component.operations.interactionValuesWith memoryChannel.toRaw (table.environment row.physical) := by
    rw [chip, raw_registered]
    unfold Operations.interactionValuesWith
    rw [protected_memory]
    exact Operations.interactionValuesWith_congr rfl
  have receipt := records_of_pull (raw witness) (raw_registered witness) (.ordinary id) row.physical
    physical 1 msg (transport ▸ seen)
  change (_, AccessSupply.atClock (upper (.ordinary id) (Environment.fromArray row.physical table.data)) _) ∈ _ at receipt
  rw [ordinary_upper, ← chip, ← row.chip.decodeRow_setData data table.data] at receipt
  exact receipt

/-- The ordinary case of the CPU execution inventory uses the same physical supply at every
State cut, before or after the State ledger orders the event occurrences. -/
theorem execution_ordinary_predecessor (witness : EnsembleWitness (base image source target final))
    {row : DecodedInstructionRow SP1Prime}
    (member : NativeCore.ExecutionRow.instruction row ∈
      LocalCore.executionRows (HostFinalMemory.coreWitness (HostObserved.baseWitness witness)))
    (data : ProverData Fp) {prior : MemoryMsg Fp} {time : ℕ}
    (pulled : (prior, time) ∈ (row.ordinaryRowFacts data).memPulls) :
    let state := (row.ordinaryRowFacts data).statePull
    time = Semantics.StateMsg.timeNat state ∧
      (1, AccessSupply.atClock (state.clk_high, state.clk_low) prior) ∈ records (raw witness) := by
  apply ordinary_predecessor witness _ data pulled
  simp only [LocalCore.executionRows, List.mem_append, List.mem_map,
    NativeCore.ExecutionRow.instruction.injEq, reduceCtorEq, and_false, exists_false, or_false] at member
  obtain ⟨_, active, rfl⟩ := member
  exact (List.mem_filter.mp active).1

end SP1Clean.Export.WriteSourceRegistry
