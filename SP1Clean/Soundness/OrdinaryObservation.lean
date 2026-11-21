import SP1Clean.Proofs.Operations.OrdinaryObservation
import SP1Clean.Soundness.RankedGrounding
import SP1Clean.Soundness.OrdinaryStateReceipt
import SP1Clean.Semantics.Execution.SailBookkeeping
import ToClean.Air.TransitionView
import SP1Clean.Soundness.OrdinaryObservationResources

/-! # Exhaustive ordinary observation histories

The existing ranked grounding theorem orders the actual consumer rows. It excludes detached
cycles and derives the complete retirement count and final raw successor PC. These are subsystem
results: the mixed ensemble must derive Byte guarantees, balance the producer receipts and
authenticate the initial/final observation states. No second execution relation is introduced.
-/

namespace SP1Clean.Soundness.OrdinaryObservation

open Circuit Air.Flat SP1Clean.OrdinaryObservation RankedGrounding
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
variable {generation : WitnessGeneration.DemandMode (ZMod p) Inputs}

/-- Match the field equality used by Clean's gated balance filters. -/
local instance cleanBalanceDecidableEq : DecidableEq (ZMod p) := FiniteField.instDecidableEq

/-- The actual circuit's pull/push pair supplies the common transition interface. -/
def view (generation : WitnessGeneration.DemandMode (ZMod p) Inputs) : TransitionView (stateChannel (p := p)) where
  component := { circuit := circuit, generation := .demand generation, Assumptions := circuit.Assumptions }
  edge env :=
    let input := valueFromOffset Inputs 0 env
    (input.previous, input.next)
  interactions := state_values

/-- The installed consumer is the transition view's component. -/
theorem consumer_view : (consumer (p := p)) = (view consumerDemand).component := rfl

/-- Read observation inputs directly from their physical arrays and shared data. -/
def rows (table : Table (ZMod p)) (data : ProverData (ZMod p)) : List (Inputs (ZMod p)) :=
  table.table.map (fun physical => valueFromOffset Inputs 0 (Environment.fromArray physical data))

/-- A row links the previous observation to the exact receipt and computed counter. -/
def edge (input : Inputs (ZMod p)) : State (ZMod p) × State (ZMod p) :=
  (input.previous, input.next)

/-- The natural source clock ranks the observation history. -/
def rank (state : State (ZMod p)) : ℕ := Semantics.clkNat state.clkHigh state.clkLow

/-- No projected rows or synthetic receipt ledger is needed to read the unit consumers. -/
theorem receipt_ledger (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (registered : table.component = (view generation).component) :
    table.interactionsWith InstructionReceipt.channel.toRaw =
      (rows table data).map (fun input => InstructionReceipt.channel.pulledValue input.receipt) := by
  simp only [Table.interactionsWith, registered, view, receipt_values, rows, List.map_map]
  exact List.map_eq_flatMap.symm

/-- Observation transitions are the literal evaluated table ledger. -/
theorem state_ledger (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (registered : table.component = (view generation).component) :
    table.interactionsWith stateChannel.toRaw = (rows table data).flatMap (fun input =>
      [stateChannel.pulledValue input.previous, stateChannel.pushedValue input.next]) := by
  have cells (physical : Array (ZMod p)) :
      valueFromOffset Inputs 0 (table.environment physical) =
        valueFromOffset Inputs 0 (Environment.fromArray physical data) :=
    ProvableType.valueFromOffset_congr _ _ (fun _ _ => rfl)
  simp only [Table.interactionsWith, registered, view, state_values, rows, List.flatMap_map, cells]

/-- One receipt occurrence is consumed for each physical row, with no padding discount. -/
theorem receipt_count (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (registered : table.component = (view generation).component) :
    (table.interactionsWith InstructionReceipt.channel.toRaw).length = table.length := by
  rw [receipt_ledger table data registered]
  simp only [rows, List.length_map]

/-- Every consumer contributes two physical observation-channel occurrences. -/
theorem state_count (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (registered : table.component = (view generation).component) :
    (table.interactionsWith stateChannel.toRaw).length = 2 * table.length := by
  rw [state_ledger table data registered, List.length_flatMap]
  simp [rows, Function.comp_def, List.sum_replicate, Nat.mul_comm]

/-- A balanced producer/consumer ledger matches complete successor messages, with padding
removed only after applying the real physical count bound. The activity fact is supplied by
the original chip contracts when the components are installed in the mixed ensemble. -/
theorem receipts_exact (id : InstructionChipId) (original consumer : Table (ZMod p))
    (data : ProverData (ZMod p))
    (source : original.component = (supportedChipFor id).table)
    (registered : consumer.component = (view generation).component)
    (binary : ∀ physical ∈ original.table,
      ((supportedChipFor (p := p) id).decodeRow data physical).is_real = 0 ∨
        ((supportedChipFor (p := p) id).decodeRow data physical).is_real = 1)
    (balanced : BalancedInteractions
      ((OrdinaryStateReceipt.construct id original source).interactionsWith InstructionReceipt.channel.toRaw ++
        consumer.interactionsWith InstructionReceipt.channel.toRaw)) :
    ((original.table.filter (fun physical => decide
      (((supportedChipFor (p := p) id).decodeRow data physical).is_real = 1))).map
        (fun physical => statePushMessage ((supportedChipFor (p := p) id).decodeRow data physical))).Perm
      ((rows consumer data).map Inputs.receipt) := by
  rw [OrdinaryStateReceipt.construct_receipts, receipt_ledger consumer data registered] at balanced
  apply InstructionReceipt.channel.gated_unit_perm_of_balanced original.table
    (fun physical => ((supportedChipFor (p := p) id).decodeRow data physical).is_real)
    (fun physical => statePushMessage ((supportedChipFor (p := p) id).decodeRow data physical))
    ((rows consumer data).map Inputs.receipt) binary
  simpa only [List.map_map, Function.comp_def] using balanced

private theorem rows_spec (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (registered : table.component = (view generation).component) (valid : table.Spec) :
    ∀ input ∈ rows table data, Spec input := by
  intro input member
  change input ∈ table.table.map (fun physical => valueFromOffset Inputs 0 (Environment.fromArray physical data)) at member
  obtain ⟨physical, inTable, equal⟩ := List.mem_map.mp member
  subst input
  have result := valid physical inTable
  rw [registered] at result
  exact result

omit [Fact (2 ^ 25 < p)] in
private theorem counter_of_walk (initial final : State (ZMod p))
    (path : List (Inputs (ZMod p))) (valid : ∀ input ∈ path, Spec input)
    (walk : Walk.IsWalk edge initial final path) :
    final.enabled = initial.enabled ∧
      Word.toBitVec64 final.counter =
        Word.toBitVec64 initial.counter + BitVec.ofNat 64 (path.length * initial.enabled.val) := by
  induction path generalizing initial with
  | nil =>
    change initial = final at walk
    subst final
    simp
  | cons input rest ih =>
    obtain ⟨source, tail⟩ := walk
    change input.previous = initial at source
    subst source
    have step := (valid input (List.mem_cons_self ..)).2.2.2.2
    obtain ⟨flag, counter⟩ := ih input.next (fun row member => valid row (List.mem_cons_of_mem _ member)) tail
    refine ⟨flag, ?_⟩
    rw [counter]
    change Word.toBitVec64 input.counter + BitVec.ofNat 64 (rest.length * input.previous.enabled.val) = _
    rw [step, BitVec.add_assoc, ← BitVec.ofNat_add, List.length_cons, Nat.succ_mul, Nat.add_comm]

omit [Fact (2 ^ 25 < p)] in
private theorem pc_of_walk (initial final : State (ZMod p)) (path : List (Inputs (ZMod p)))
    (walk : Walk.IsWalk edge initial final path) :
    final.pc = path.foldl (fun _ input => input.next.pc) initial.pc := by
  induction path generalizing initial with
  | nil => exact congrArg State.pc walk.symm
  | cons input rest ih =>
    exact ih input.next walk.2

/-- Raw observation balance and local table meaning force one exhaustive ordered history.
The endpoint parameters are an installation boundary, not capstone caller premises. -/
theorem ordered_history (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (registered : table.component = (view generation).component) (valid : table.Spec)
    (initial final : State (ZMod p))
    (balanced : BalancedInteractions
      ([stateChannel.pushedValue initial, stateChannel.pulledValue final] ++
        table.interactionsWith stateChannel.toRaw)) :
    ∃ path : List (Inputs (ZMod p)), path.Perm (rows table data) ∧
      Walk.IsWalk edge initial final path ∧
      (path.map (fun input => rank input.next)).Pairwise (· < ·) ∧
      final.enabled = initial.enabled ∧
      Word.toBitVec64 final.counter =
        Word.toBitVec64 initial.counter + BitVec.ofNat 64 (table.length * initial.enabled.val) ∧
      final.pc = path.foldl (fun _ input => input.next.pc) initial.pc := by
  rw [state_ledger table data registered] at balanced
  have endpoints := (stateChannel.transitionLedger_balanced_iff initial final (rows table data) edge).mp balanced
  have endpointBalance : EndpointBalanced (↑(rows table data)) edge initial final := by
    simpa only [EndpointBalanced, Multiset.map_coe, Multiset.cons_coe, Multiset.coe_eq_coe] using endpoints
  have specs := rows_spec table data registered valid
  have strict : ∀ input ∈ rows table data, rank input.previous < rank input.next :=
    fun input member => (specs input member).1.2.2.2.2
  obtain ⟨path, walk, exhaustive⟩ := exists_exhaustiveTrail_of_endpointBalanced
    (↑(rows table data)) edge rank initial final endpointBalance
    (fun input member => strict input (Multiset.mem_coe.mp member))
  have perm := Multiset.coe_eq_coe.mp exhaustive
  have pathSpecs := fun input member => specs input (perm.mem_iff.mp member)
  have length : path.length = table.length := by simpa only [rows, List.length_map] using perm.length_eq
  obtain ⟨flag, counter⟩ := counter_of_walk initial final path pathSpecs walk
  refine ⟨path, perm, walk, ?_, flag, by rwa [← length], pc_of_walk initial final path walk⟩
  exact targetRanks_pairwise_of_isWalk edge rank walk
    (fun input member => strict input (perm.mem_iff.mp member))

omit [Fact (2 ^ 25 < p)] in
/-- Counter observations agree with the existing semantic retirement fold, including inhibition,
when the chain's flag denotes the semantic retirement flag. An empty ordinary history leaves the
supplied incoming increment flag untouched. -/
theorem retirement_fold (initial final : State (ZMod p)) (path : List (Inputs (ZMod p)))
    (flag : Option Bool) (valid : ∀ input ∈ path, Spec input) (walk : Walk.IsWalk edge initial final path)
    (enabled : Bool) (denotes : initial.enabled.val = if enabled then 1 else 0) :
    path.foldl (fun values _ => Semantics.retirementTick values true)
      (enabled, flag, some (Word.toBitVec64 initial.counter)) =
        (enabled, if path.length = 0 then flag else some enabled, some (Word.toBitVec64 final.counter)) := by
  rw [Semantics.retirementTick_fold (fun _ : Inputs (ZMod p) => true)]
  simp only [List.countP_true, Option.map_some]
  rw [(counter_of_walk initial final path valid walk).2, denotes]
  cases enabled <;> simp

end SP1Clean.Soundness.OrdinaryObservation
