import SP1Clean.Proofs.Completeness.OrdinaryObservationHistory
import SP1Clean.Soundness.OrdinaryObservation
import ToClean.Air.MessageFilter

/-! # Constructing the installed ordinary observation consumer with padding

The 25-family router supplies the chronological sequence. Each element produces a live
consumer row. Additional physical rows use Clean's own demand-mode padding input. The
table's committed prefixes and their prover data are constructed together.
-/

namespace SP1Clean.OrdinaryObservation

open Circuit Air.Flat Semantics TraceGen
open Soundness.OrdinaryObservation (consumer)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- The live history followed by the padding rows selected by the installed demand mode. -/
def paddedInputs (source : SailSnapshot) (events : List RoutedEvent) (padding : ℕ) : List (RowInput (ZMod p)) :=
  (history (startFor source) events).1.map activeRow ++ List.replicate padding 0

omit [Fact (2 ^ 25 < p)] in
/-- Physical height counts every padding row. -/
theorem paddedInputs_length (source : SailSnapshot) (events : List RoutedEvent) (padding : ℕ) :
    (paddedInputs (p := p) source events padding).length = events.length + padding := by
  simp only [paddedInputs, List.length_append, List.length_map, history_length, List.length_replicate]

/-- Populate all rows using their canonical named input data and Clean's existing builder. -/
def paddedTable (source : SailSnapshot) (events : List RoutedEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (height : events.length + padding ≤ UInt64.size) : Table (ZMod p) :=
  let rows := paddedInputs source events padding
  Table.build consumer rows (consumer.inputData rows data) (ProverHint.empty _)
    ((paddedInputs_length (p := p) source events padding).trans_le height) (by trivial) (consumer.inputData_consistent rows data)

/-- Chronological, representable source clocks construct both local constraints and channel
guarantees of the installed consumer for any number of disabled physical rows. -/
theorem paddedTable_valid (source : SailSnapshot) (events : List RoutedEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (height : events.length + padding ≤ UInt64.size)
    (positive : ∀ event ∈ events, 0 < event.clock) (bounded : ∀ event ∈ events, event.clock < 2 ^ 48)
    (ordered : events.Pairwise (fun a b => a.clock < b.clock)) :
    (paddedTable source events padding data height).Constraints ∧
      (paddedTable source events padding data height).Guarantees := by
  let rows := paddedInputs (p := p) source events padding
  have valid (row : RowInput (ZMod p)) (member : row ∈ rows) :
      (consumer (p := p)).circuit.ProverAssumptions row (consumer.inputData rows data) (ProverHint.empty _) := by
    change IsBool row.2 ∧ (row.2 = 1 → Spec row.1)
    rcases List.mem_append.mp member with live | disabled
    · obtain ⟨input, occurs, rfl⟩ := List.mem_map.mp live
      exact ⟨Or.inr rfl, fun _ => history_spec source events positive bounded ordered input occurs⟩
    · obtain ⟨_, rfl⟩ := List.mem_replicate.mp disabled
      change IsBool (0 : ZMod p) ∧ ((0 : ZMod p) = 1 → _)
      exact ⟨Or.inl rfl, fun impossible => (zero_ne_one impossible).elim⟩
  unfold paddedTable
  constructor
  · apply Table.build_constraints
    exact valid
  · apply Table.build_guarantees
    exact valid

private theorem read_rows {F : Type} [FiniteField F] (component : Component F)
    (inputs : List (component.Input F)) (data evaluationData : ProverData F) (hint : ProverHint F) :
    (inputs.map (fun input => component.buildRow input data hint)).map
      (fun physical => component.rowInput (Environment.fromArray physical evaluationData)) = inputs := by
  simp only [List.map_map, Function.comp_def, Component.rowInput_buildRow, List.map_id']

/-- Reading the committed guarded rows recovers the active history and every padding input. -/
theorem paddedTable_rows (source : SailSnapshot) (events : List RoutedEvent) (padding : ℕ)
    (data evaluationData : ProverData (ZMod p)) (height : events.length + padding ≤ UInt64.size) :
    Soundness.OrdinaryObservation.rows (paddedTable source events padding data height) evaluationData =
      paddedInputs source events padding := by
  exact read_rows consumer (paddedInputs source events padding) _ evaluationData (ProverHint.empty _)

/-- One signed field sum for each raw receipt and observation link, including disabled rows.
Occurrence bounds are measured on the full physical lists by the ensemble. -/
theorem paddedTable_logUp (source : SailSnapshot) (events : List RoutedEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (height : events.length + padding ≤ UInt64.size) :
    let initial := startFor (p := p) source
    let held := (history initial events).2
    let table := paddedTable source events padding data height
    LogUpBalanced ((events.map fun event => InstructionReceipt.channel.pushedValue event.rawPushState.toMessage) ++
      table.interactionsWith InstructionReceipt.channel.toRaw) ∧
    LogUpBalanced ([stateChannel.pushedValue initial, stateChannel.pulledValue held] ++
      table.interactionsWith stateChannel.toRaw) := by
  dsimp only
  let initial := startFor (p := p) source
  let inputs := (history initial events).1
  let held := (history initial events).2
  let table := paddedTable source events padding data height
  have decoded := paddedTable_rows source events padding data data height
  have receipt := Soundness.OrdinaryObservation.receipt_ledger table data rfl
  have states := Soundness.OrdinaryObservation.state_ledger table data rfl
  rw [decoded] at receipt states
  rw [receipt, states]
  have paired := (InstructionReceipt.channel (p := p)).balanced_unit_iff
    (events.map fun event => event.rawPushState.toMessage) (inputs.map Inputs.receipt)
  have same : (events.map fun event => event.rawPushState.toMessage (p := p)).Perm (inputs.map Inputs.receipt) := by
    rw [history_receipts]
  have receipts := (paired.mpr same).logUp_of_isBool (by
    intro i member
    rcases List.mem_append.mp member with producer | seen
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp producer
      exact Or.inr rfl
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp seen
      exact Or.inr rfl)
  have links := (history_states initial events).logUp_of_isBool (by
    intro i member
    change i ∈ [_ , _] ++ List.flatMap _ _ at member
    rcases List.mem_append.mp member with ends | historyRow
    · rcases List.mem_cons.mp ends with rfl | last
      · exact Or.inr rfl
      · obtain rfl := List.mem_singleton.mp last
        exact Or.inr rfl
    · obtain ⟨_, _, occurrence⟩ := List.mem_flatMap.mp historyRow
      rcases List.mem_cons.mp occurrence with rfl | last
      · exact Or.inr rfl
      · obtain rfl := List.mem_singleton.mp last
        exact Or.inr rfl)
  have zero (i : Interaction (ZMod p)) (disabled : i.mult = 0) (rest : List (Interaction (ZMod p))) (msg : Array (ZMod p)) :
      balanceOf (i :: rest) msg = balanceOf rest msg := by
    have z : i.signedMult = 0 := by cases h : i.direction <;> simp [Interaction.signedMult, h, disabled]
    simp only [balanceOf_cons, z, ite_self, zero_add]
  have skip (extra : ℕ) (msg : Array (ZMod p)) :
      balanceOf ((List.replicate extra (0 : RowInput (ZMod p))).map
        (fun row => InstructionReceipt.channel.pulledIfValue row.2 row.1.receipt)) msg = 0 ∧
      balanceOf ((List.replicate extra (0 : RowInput (ZMod p))).flatMap
        (fun row => [stateChannel.pulledIfValue row.2 row.1.previous, stateChannel.pushedIfValue row.2 row.1.next])) msg = 0 := by
    induction extra with
    | zero => exact ⟨rfl, rfl⟩
    | succ n ih =>
      simp only [List.replicate_succ, List.map_cons, List.flatMap_cons, List.cons_append, List.nil_append]
      rw [zero _ rfl, zero _ rfl, zero _ rfl]
      exact ih
  constructor
  · intro msg
    simp only [paddedInputs, List.map_append, List.map_map, ← List.append_assoc, balanceOf_append _ _ msg,
      (skip padding msg).1, add_zero]
    simpa only [List.map_map, Function.comp_def, balanceOf_append, activeRow, Channel.pulledIfValue,
      Channel.pulledValue, inputs, initial] using receipts msg
  · intro msg
    simp only [paddedInputs, List.flatMap_append, List.flatMap_map, ← List.append_assoc,
      balanceOf_append _ _ msg, (skip padding msg).2, add_zero]
    simpa only [Channel.transitionLedger, balanceOf_append, activeRow, Channel.pulledIfValue, Channel.pushedIfValue,
      Channel.pulledValue, Channel.pushedValue, initial] using links msg

end SP1Clean.OrdinaryObservation
