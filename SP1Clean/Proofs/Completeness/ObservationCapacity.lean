import SP1Clean.Proofs.Completeness.ExecutionObservationEndpoint
import SP1Clean.FormalModel.ShardResources

/-! # Physical capacity of the constructed observation subsystem

The observation-state channel has two public interactions, two per physical consumer row, and
two in the selected terminal. These counts include disabled consumer rows. The receipt count
below covers the consumer only; the instruction tables have their own physical padding.
-/

namespace SP1Clean.TraceGen

open Circuit Air.Flat Semantics Machine FormalModel.Shard OrdinaryObservation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- Physical row and occurrence counts for the four observation tables, including all padding.
The verifier contributes the two endpoint occurrences in the state ledger. -/
theorem observation_counts (source target : SailSnapshot) (rows : List RoutedEvent)
    (data : ProverData (ZMod p)) (height : rows.length + WitnessGeneration.demandPadding rows.length ≤ UInt64.size) :
    let h := WitnessGeneration.demandHeight rows.length
    let table := paddedTable source rows (WitnessGeneration.demandPadding rows.length) data height
    let start := startFor (p := p) source
    let selected := Mode.of source target
    let input := terminalInput (history start rows).2
    let terminals := observationTerminalTables selected input data
    table.length = h ∧ (terminals.map Table.length).sum = 1 ∧
      (table.interactionsWith InstructionReceipt.channel.toRaw).length = h ∧
      (([stateChannel.pushedValue start, stateChannel.pulledValue (finalFor source target)] ++
        table.interactionsWith stateChannel.toRaw) ++ terminals.flatMap (·.interactionsWith stateChannel.toRaw)).length = 2 * h + 4 := by
  dsimp only
  let table := paddedTable source rows (WitnessGeneration.demandPadding rows.length) data height
  have count : table.length = WitnessGeneration.demandHeight rows.length := by
    calc
      table.length = (paddedInputs (p := p) source rows (WitnessGeneration.demandPadding rows.length)).length := by
        exact List.length_map ..
      _ = _ := (paddedInputs_length ..).trans (WitnessGeneration.add_demandPadding _)
  refine ⟨count, ?_, (Soundness.OrdinaryObservation.receipt_count table data rfl).trans count, ?_⟩
  · generalize Mode.of source target = mode
    cases mode <;> rfl
  · rw [observationTerminalTables_ledger, List.length_append, List.length_append,
      Soundness.OrdinaryObservation.state_count table data rfl, count]
    simp only [List.length_cons, List.length_nil]
    omega

omit [Fact p.Prime] in
/-- Under the public native event limit, the complete observation-state ledger fits the field
occurrence bound and the demand-padded table fits the row budget. -/
theorem admissibleExecution_observationFits {image : ProgramImage} {source target : ExecutionSnapshot}
    {events : List ExecutionEvent} (execution : AdmissibleExecution (ResourceLimits.native p) p image source target events) :
    let h := WitnessGeneration.demandHeight (events.countP ExecutionEvent.isOrdinary)
    h ≤ (ResourceLimits.native p).tableRows ∧ 2 * h + 4 ≤ (ResourceLimits.native p).channelOccurrences := by
  have count := (List.countP_le_length (p := ExecutionEvent.isOrdinary) (l := events)).trans execution.work.1
  change events.countP ExecutionEvent.isOrdinary ≤ 2 ^ 21 at count
  have bounds := (WitnessGeneration.demandHeight_bounds (events.countP ExecutionEvent.isOrdinary)).2
  have primeSize := Fact.out (p := 2 ^ 25 < p)
  change _ ≤ p - 1 ∧ _ ≤ p - 1
  omega

end SP1Clean.TraceGen
