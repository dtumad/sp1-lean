import SP1Clean.Proofs.Completeness.ExecutionObservationEndpoint
import SP1Clean.Soundness.HostFinalMemoryLookups

/-! # Observation witnesses at the complete inventory's canonical data

The four observation tables read their own committed cells and use only the Byte, ordinary
receipt and observation-state channels. Each channel's guarantee depends on the message and its
weight. Installing the data derived from every component therefore preserves the observation
constraints, channel guarantees and literal ledgers.
-/

namespace SP1Clean.TraceGen
open Circuit Air.Flat Semantics Machine FormalModel.Shard OrdinaryObservation Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

private theorem channels_of_observed (c : Component (ZMod p)) (observed : c ∈ Soundness.OrdinaryObservation.tables) :
    c.circuit.channels ⊆ [Channels.byteChannel.toRaw, InstructionReceipt.channel.toRaw, stateChannel.toRaw] := by
  simp only [Soundness.OrdinaryObservation.tables, List.mem_cons, List.not_mem_nil, or_false] at observed
  rcases observed with rfl | rfl | rfl | rfl
  · exact Soundness.OrdinaryObservation.consumer_channels
  all_goals rw [Soundness.OrdinaryObservation.terminal_channels]; simp

/-- A generated observation table retains its local checks when installed in a larger inventory.
The physical rows and component stay fixed; the canonical data includes all the other tables. -/
theorem observation_setData (table : Table (ZMod p)) (observed : table.component ∈ Soundness.OrdinaryObservation.tables)
    (checked : table.Constraints ∧ table.Guarantees) (data : ProverData (ZMod p))
    (consistent : data.tables table.component.circuit.name (size table.component.Input) = table.rowPrefixes (size table.component.Input)) :
    let rebound : Table (ZMod p) := { table with data, data_consistent := consistent }
    rebound.Constraints ∧ rebound.Guarantees ∧ ∀ channel, rebound.interactionsWith channel = table.interactionsWith channel := by
  let rebound : Table (ZMod p) := { table with data, data_consistent := consistent }
  have occurrences : rebound.interactions = table.interactions := by
    exact congrArg List.flatten (List.map_congr_left fun row _ =>
      Operations.interactionValues_congr (ops := table.component.operations)
        (env := rebound.environment row) (env' := table.environment row) rfl)
  refine ⟨fun row member => table.component.constraintsHold_setData
    (Soundness.HostFinalMemory.observation_lookupFree _ observed) (checked.1 row member), ?_, Table.interactionsWith_setData table data consistent⟩
  apply rebound.guarantees_iff_forall.mpr
  intro i member pull
  have original : i ∈ table.interactions := occurrences ▸ member
  have used := channels_of_observed table.component observed (table.channel_mem_channels_of_mem_interactions i original)
  have independent (ch : RawChannel (ZMod p)) (listed : ch ∈ [Channels.byteChannel.toRaw, InstructionReceipt.channel.toRaw, stateChannel.toRaw])
      (mult : ZMod p) (message : Vector (ZMod p) ch.arity) :
      ch.Guarantees mult message table.data → ch.Guarantees mult message data := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl | rfl <;> exact id
  exact independent i.channel used _ _ (table.guarantees_iff_forall.mp checked.2 i original pull)

/-- The checked observation row at a particular physical slot survives Clean's canonicalization
of the full inventory, with all of its channel occurrences in their original order. -/
theorem observation_atSlot (inventory : List (Table (ZMod p)))
    (unique : (inventory.map fun table => table.component.circuit.name).Nodup) (publicInput : Array (ZMod p))
    (i : Fin inventory.length) (observed : inventory[i.val].component ∈ Soundness.OrdinaryObservation.tables)
    (checked : inventory[i.val].Constraints ∧ inventory[i.val].Guarantees) :
    ∃ actual, (withDerivedData inventory unique publicInput)[i.val]? = some actual ∧
      actual.component = inventory[i.val].component ∧ actual.table = inventory[i.val].table ∧
      actual.data = deriveProverData inventory publicInput ∧ actual.Constraints ∧ actual.Guarantees ∧
      ∀ channel, actual.interactionsWith channel = inventory[i.val].interactionsWith channel := by
  let original := inventory[i.val]
  let data := deriveProverData inventory publicInput
  have consistent : data.tables original.component.circuit.name (size original.component.Input) =
      original.rowPrefixes (size original.component.Input) := deriveTables_eq_of_mem inventory unique (List.getElem_mem i.isLt) _
  let actual : Table (ZMod p) := { original with data, data_consistent := consistent }
  obtain ⟨constraints, guarantees, ledgers⟩ := observation_setData original observed checked data consistent
  refine ⟨actual, ?_, rfl, rfl, rfl, constraints, guarantees, ledgers⟩
  have bound : i.val < (withDerivedData inventory unique publicInput).length := by simp [withDerivedData]
  rw [List.getElem?_eq_getElem bound]
  simp [withDerivedData, actual, original, data]

/-- An admissible execution supplies all four observation tables without any generation data
from other components. Wherever each table occurs in a full layout, the actual canonicalized
slot retains all committed rows, checks, and receipt/state occurrences. -/
theorem admissibleExecution_observationData {limits : ResourceLimits} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events) :
    ∃ rows, routeObservations? (policy p image) image.program (fun _ => 0) source.realize events = some rows ∧
      ∃ height : rows.length + WitnessGeneration.demandPadding rows.length ≤ UInt64.size,
      let data := ProverData.empty (ZMod p)
      let start := startFor (p := p) source.sail
      let consumer := paddedTable source.sail rows (WitnessGeneration.demandPadding rows.length) data height
      let mode := Mode.of source.sail target.sail
      let input := terminalInput (history start rows).2
      let block := consumer :: observationTerminalTables mode input data
      block.map Table.component = Soundness.OrdinaryObservation.tables ∧
        ∀ (inventory : List (Table (ZMod p))) (unique : (inventory.map fun table => table.component.circuit.name).Nodup)
          (publicInput : Array (ZMod p)) (i : Fin inventory.length), inventory[i.val] ∈ block →
          ∃ actual, (withDerivedData inventory unique publicInput)[i.val]? = some actual ∧
            actual.component = inventory[i.val].component ∧ actual.table = inventory[i.val].table ∧
            actual.data = deriveProverData inventory publicInput ∧ actual.Constraints ∧ actual.Guarantees ∧
            ∀ channel, actual.interactionsWith channel = inventory[i.val].interactionsWith channel := by
  obtain ⟨rows, route, _, _, height, consumerOK, consumerGuarantees, terminals, _, _, _, _⟩ :=
    admissibleExecution_observationWitness execution (ProverData.empty _)
  refine ⟨rows, route, height, rfl, ?_⟩
  intro inventory unique publicInput i member
  apply observation_atSlot inventory unique publicInput i
  · exact List.mem_map_of_mem (f := Table.component) member
  · rcases List.mem_cons.mp member with first | later
    · rw [first]
      exact ⟨consumerOK, consumerGuarantees⟩
    · exact terminals _ later

end SP1Clean.TraceGen
