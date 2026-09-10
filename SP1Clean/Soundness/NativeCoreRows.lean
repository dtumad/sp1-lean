import SP1Clean.Soundness.NativeCoreMemory
import SP1Clean.Soundness.NativeCoreDecode
import SP1Clean.Soundness.SystemMemoryRows

/-! # Physical mixed rows of the authenticated native core

The physical instruction and system tables decode into one execution-row carrier. Memory refresh
pairs remain separate because they do not execute instructions. Exact ledger projections remove
only disabled rows and Memory-silent providers, retaining every active HALT and syscall occurrence.
This module establishes the row-level balance needed before refresh elimination and timed walking;
it does not assert an execution order or host semantics.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics
open TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

private theorem witness_length {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) : witness.tables.length = 59 := by
  rw [← witness.same_length]
  exact tables_length image

/-- The physical refresh, StateBump, HALT, and syscall tables, in their registered order. -/
def systemTable {image : ProgramImage} (witness : EnsembleWitness (ensemble (p := p) image))
    (index : Fin 4) : Table (ZMod p) :=
  witness.tables[55 + index.val]'(by have := witness_length witness; omega)

theorem systemTable_component {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) (index : Fin 4) :
    (systemTable witness index).component =
      ([⟨MemoryBumpChip.circuit⟩, ⟨StateBumpChip.circuit⟩, ⟨HaltChip.circuit⟩,
        ⟨SyscallInstrsChip.circuit⟩] : List (Component (ZMod p)))[index.val] := by
  have same := witness.same_circuits (55 + index.val)
    (by change 55 + index.val < (tables image).length; rw [tables_length]; omega)
  apply same.symm.trans
  fin_cases index <;> rfl

theorem systemTable_mem {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) (index : Fin 4) :
    systemTable witness index ∈ witness.allTables :=
  witness.mem_allTables_of_mem_tables (List.getElem_mem _)

theorem systemTable_constraints {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) (constraints : witness.Constraints)
    (index : Fin 4) : (systemTable witness index).Constraints :=
  constraints _ (systemTable_mem witness index)

private theorem systemTables_eq {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
    witness.tables.drop 55 = [systemTable witness 0, systemTable witness 1,
      systemTable witness 2, systemTable witness 3] := by
  have length := witness_length witness
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    List.drop_eq_nil_of_le (by omega)]
  rfl

omit [Fact (2 ^ 24 < p)] in
private theorem typedMemory_nil (table : Table (ZMod p))
    (silent : memoryChannel.toRaw ∉ table.component.circuit.channels) :
    typedTableInteractionsWith table memoryChannel = [] := by
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [typedTableInteractionsWith_raw, List.map_nil]
  exact table.interactionsWith_nil_of_channel_not_mem silent

private theorem byteTables_memory_silent {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
    ((witness.tables.drop 32).take 23).flatMap (typedTableInteractionsWith · memoryChannel) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro table member
  apply typedMemory_nil
  have mapped := List.mem_map_of_mem (f := fun t : Table (ZMod p) => t.component) member
  rw [List.map_take, List.map_drop, witness.tables_map_component] at mapped
  change table.component ∈ (sp1ProviderTables (p := p)).take 23 at mapped
  rw [sp1ProviderTables, ← List.map_take] at mapped
  obtain ⟨id, idMem, componentEq⟩ := List.mem_map.mp mapped
  rw [← componentEq]
  have prefixEq : ProviderTableId.all.take 23 =
      ByteProviderId.all.map .byte ++ (List.finRange 17).map .range := by decide
  rw [prefixEq] at idMem
  rcases List.mem_append.mp idMem with byte | range
  · obtain ⟨provider, _, rfl⟩ := List.mem_map.mp byte
    cases provider <;> change memoryChannel.toRaw ∉ [byteChannel.toRaw]
    all_goals simp [memoryChannel_eq_byteChannel_false]
  · obtain ⟨width, _, rfl⟩ := List.mem_map.mp range
    change memoryChannel.toRaw ∉ [byteChannel.toRaw]
    simp [memoryChannel_eq_byteChannel_false]

private theorem flatMap_split {α β : Type*} (items : List α) (f : α → List β) (start count : ℕ) :
    (items.drop start).flatMap f = ((items.drop start).take count).flatMap f ++
      (items.drop (start + count)).flatMap f := by
  have split := congrArg (List.flatMap f) (List.take_append_drop count (items.drop start))
  simpa only [List.flatMap_append, List.drop_drop, Nat.add_comm] using split.symm

/-- The complete physical Memory interior: ordinary rows plus the three participating system
tables. Fixed Program, Byte/Range, and StateBump are proved Memory-silent. -/
theorem memoryInterior_split {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
    memoryInterior witness =
      (instructionTables witness).flatMap (typedTableInteractionsWith · memoryChannel) ++
      typedTableInteractionsWith (systemTable witness 0) memoryChannel ++
      typedTableInteractionsWith (systemTable witness 2) memoryChannel ++
      typedTableInteractionsWith (systemTable witness 3) memoryChannel := by
  have programSilent : typedTableInteractionsWith (programTable witness) memoryChannel = [] := by
    apply typedMemory_nil
    rw [programTable_component]
    change memoryChannel.toRaw ∉ [programChannel.toRaw]
    simp [memoryChannel_eq_programChannel_false]
  have stateSilent : typedTableInteractionsWith (systemTable witness 1) memoryChannel = [] := by
    apply typedMemory_nil
    rw [systemTable_component]
    change memoryChannel.toRaw ∉ [byteChannel.toRaw, stateChannel.toRaw]
    simp [memoryChannel_eq_byteChannel_false, memoryChannel_eq_stateChannel_false]
  have head : witness.tables.drop 6 = programTable witness :: witness.tables.drop 7 := by
    rw [List.drop_eq_getElem_cons (by have := witness_length witness; omega)]
    rfl
  rw [memoryInterior, head, List.flatMap_cons, programSilent, List.nil_append,
    flatMap_split witness.tables _ 7 25, flatMap_split witness.tables _ 32 23,
    byteTables_memory_silent, List.nil_append, systemTables_eq]
  simp only [List.flatMap_cons, List.flatMap_nil, stateSilent, List.nil_append,
    List.append_nil, List.append_assoc, instructionTables]

/-- Active ordinary rows decoded from the unchanged physical instruction batch. -/
noncomputable def activeInstructionRows {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) : List (DecodedInstructionRow p) :=
  (instructionRows witness).filter (fun row => (row.toChipRow witness.data).is_real = 1)

/-- All real instruction events, including the legacy terminal row and inline syscalls. -/
inductive ExecutionRow (p : ℕ) [Fact p.Prime] [Fact (2 ^ 24 < p)] where
  | instruction (row : DecodedInstructionRow p)
  | halt (row : HaltChip.Inputs (ZMod p))
  | syscall (row : SyscallInstrsChip.Inputs (ZMod p))

/-- One row's semantic carrier. Subsequent alignment chooses read currency points; refresh
elimination may replace prior records by equal-value earlier records. -/
noncomputable def ExecutionRow.facts (data : ProverData (ZMod p)) : ExecutionRow p → RowFacts p
  | .instruction row => row.ordinaryRowFacts data
  | .halt row => haltRowFacts row
  | .syscall row => syscallRowFacts row

/-- The complete physical event inventory, before State-bus ordering. -/
noncomputable def executionRows {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) : List (ExecutionRow p) :=
  (activeInstructionRows witness).map .instruction ++
    (activeSystemRows (systemTable witness 2) haltRow (·.is_real)).map .halt ++
    (activeSystemRows (systemTable witness 3) syscallInstrsRow (·.is_real)).map .syscall

/-- Actual active refresh pairs, kept separate from instruction execution. -/
noncomputable def memoryRefreshes {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
    List (MemoryMsg (ZMod p) × MemoryMsg (ZMod p)) :=
  (activeSystemRows (systemTable witness 0) memoryBumpRow (·.is_real)).flatMap MemoryBumpChip.memoryPairs

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem flatMap_filter_inactive {α β : Type*} (rows : List α) (keep : α → Bool)
    (f : α → List β) (inactive : ∀ row ∈ rows, keep row = false → f row = []) :
    (rows.filter keep).flatMap f = rows.flatMap f := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have rest := ih (fun item member => inactive item (List.mem_cons_of_mem _ member))
    cases active : keep row
    · simp [active, rest, inactive row List.mem_cons_self active]
    · simp [active, rest]

/-- Selecting active ordinary rows preserves both complete Memory message lists. -/
theorem activeInstructionRows_memory {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) (constraints : witness.Constraints) :
    producedMessages ((instructionTables witness).flatMap (typedTableInteractionsWith · memoryChannel)) =
        (activeInstructionRows witness).flatMap (·.producedMemoryMessages witness.data) ∧
    consumedMessages ((instructionTables witness).flatMap (typedTableInteractionsWith · memoryChannel)) =
        (activeInstructionRows witness).flatMap (·.consumedMemoryMessages witness.data) := by
  have ledger : (instructionTables witness).flatMap (typedTableInteractionsWith · memoryChannel) =
      (instructionRows witness).flatMap (·.interactionsWith witness.data memoryChannel) :=
    (decodedInstructionInteractionsWith_eq_tables witness.data memoryChannel
      (instructionTables_aligned witness)).symm
  have padding : ∀ row ∈ instructionRows witness, (row.toChipRow witness.data).is_real ≠ 1 →
      row.producedMemoryMessages witness.data = [] ∧ row.consumedMemoryMessages witness.data = [] := by
    intro row member disabled
    exact row.paddingMemoryMessages_eq_nil witness.data (witness.tables.drop 7) member
      (instructionRows_constraints witness constraints row member) disabled
  rw [ledger, producedMessages_flatMap, consumedMessages_flatMap]
  constructor
  · exact (flatMap_filter_inactive _ _ _ (fun row member inactive =>
      (padding row member (by simpa using inactive)).1)).symm
  · exact (flatMap_filter_inactive _ _ _ (fun row member inactive =>
      (padding row member (by simpa using inactive)).2)).symm

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem pushesAt_flatMap (rows : List (RowFacts p)) (loc : MemLoc) :
    pushesAt rows loc = Multiset.filter (fun message => MemoryMsg.locOf message = loc)
      (↑(rows.flatMap (·.memPushes)) : Multiset (MemoryMsg (ZMod p))) := by
  rw [filter_coe_flatMap]
  simp only [pushesAt, Multiset.filter_coe, rowPushesAt]

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem pullsAt_flatMap (rows : List (RowFacts p)) (loc : MemLoc) :
    pullsAt rows loc = Multiset.filter (fun message => MemoryMsg.locOf message = loc)
      (↑(rows.flatMap (fun row => row.memPulls.map Prod.fst)) : Multiset (MemoryMsg (ZMod p))) := by
  rw [filter_coe_flatMap]
  simp only [pullsAt, Multiset.filter_coe, rowPullsAt]

/-- The mixed execution carrier plus the separate refresh pairs accounts for exactly the
interior's active Memory messages, at every location and with their full multiplicities. -/
theorem executionRows_memory_projection {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (loc : MemLoc) :
    pushesAt ((executionRows witness).map (ExecutionRow.facts witness.data)) loc +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑((memoryRefreshes witness).map Prod.snd) : Multiset _) =
      Multiset.filter (fun message => MemoryMsg.locOf message = loc)
        (↑(producedMessages (memoryInterior witness)) : Multiset _) ∧
    pullsAt ((executionRows witness).map (ExecutionRow.facts witness.data)) loc +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑((memoryRefreshes witness).map Prod.fst) : Multiset _) =
      Multiset.filter (fun message => MemoryMsg.locOf message = loc)
        (↑(consumedMessages (memoryInterior witness)) : Multiset _) := by
  have ordinary := activeInstructionRows_memory witness constraints
  have refresh := memoryBumpRows_projection (systemTable witness 0) (systemTable_component witness 0)
    (systemTable_constraints witness constraints 0)
  have halt := haltRows_projection (systemTable witness 2) (systemTable_component witness 2)
    (systemTable_constraints witness constraints 2)
  have syscall := syscallRows_projection (systemTable witness 3) (systemTable_component witness 3)
    (systemTable_constraints witness constraints 3)
  rw [pushesAt_flatMap, pullsAt_flatMap, memoryInterior_split]
  simp only [producedMessages_append, consumedMessages_append, ordinary.1, ordinary.2,
    refresh.1, refresh.2, halt.1, halt.2, syscall.1, syscall.2,
    executionRows, List.map_append, List.flatMap_append, List.flatMap_map, ExecutionRow.facts,
    DecodedInstructionRow.ordinaryRowFacts_memPushes, DecodedInstructionRow.ordinaryRowFacts_memPulls,
    haltRowFacts, syscallRowFacts, SyscallInstrsChip.memoryPairs, memoryRefreshes,
    List.map_flatMap, List.map_map, Function.comp_def, List.map_id_fun',
    List.map_cons, List.map_nil, filter_coe_append]
  constructor <;> ac_rfl

/-- The authenticated Memory balance in the timed engine's row vocabulary. All active instruction,
HALT, and syscall rows are absorbed exactly once; actual refresh pairs are the only side terms. -/
theorem executionRows_memory_balance {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) (loc : MemLoc) :
    optMS (memoryInitialFrontier witness loc) +
        pushesAt ((executionRows witness).map (ExecutionRow.facts witness.data)) loc +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑((memoryRefreshes witness).map Prod.snd) : Multiset _) =
      optMS (memoryFinalFrontier witness loc) +
        pullsAt ((executionRows witness).map (ExecutionRow.facts witness.data)) loc +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑((memoryRefreshes witness).map Prod.fst) : Multiset _) := by
  rw [add_assoc, add_assoc, (executionRows_memory_projection witness constraints loc).1,
    (executionRows_memory_projection witness constraints loc).2]
  exact memory_frontier_balance witness constraints balanced loc

end SP1Clean.Soundness.NativeCore
