import SP1Clean.Export.OrdinaryRowCapacity
import SP1Clean.Export.InstalledVerifierCapacity
import SP1Clean.Proofs.Completeness.OrdinaryBucketCapacity

/-! # Installed capacity for the 25 ordinary instruction tables

The physical heights are the separately padded stable buckets of the actual, chronological
semantic compiler. The fixed providers, the HINT_READ handler and transfers, and all ordinary
rows share the existing installed verifier's channel counts.
-/

namespace SP1Clean.Export.InstalledAssembly
open Circuit Air.Flat TraceGen Semantics Machine Soundness FormalModel.Shard

/-- Physical rows added at the 25 distinct installed ordinary instruction slots. -/
def ordinaryHeights (rows : List RoutedEvent) (table : Component Fp) : ℕ :=
  (InstructionChipId.all.map fun id => slotRows (ProtectedOrdinaryReceipt.component id)
      (EventBuckets.paddedHeight rows id) table).sum

/-- Each of the installed instruction components uses Clean's demand padding. -/
theorem ordinary_targetHeight (state : WitnessGeneration.ComponentState Fp) (id : InstructionChipId)
    (selected : state.component = ProtectedOrdinaryReceipt.component id) :
    state.targetHeight = WitnessGeneration.demandHeight state.rows.size := by
  cases state with
  | mk component multiplicity operations interactions rows messageRows =>
    change component = _ at selected
    subst component
    cases id <;> exact WitnessGeneration.ComponentState.targetHeight_of_demand _ rfl

private theorem sum_slot_cost (ctx : Context) (rows : List RoutedEvent) (name : String) (ids : List InstructionChipId) :
    additionalOccurrences ctx (fun t => (ids.map fun id => slotRows (ProtectedOrdinaryReceipt.component id)
        (EventBuckets.paddedHeight rows id) t).sum) name =
      (ids.map fun id => EventBuckets.paddedHeight rows id * rowOccurrences (ProtectedOrdinaryReceipt.component id) name).sum := by
  induction ids with
  | nil => simp [additionalOccurrences]
  | cons id ids ih =>
    simp only [List.map_cons, List.sum_cons, additionalOccurrences_add, ih,
      additionalOccurrences_slot _ _ (ordinary_receipt_registered ctx id)]

/-- Literal cost of all installed ordinary rows on a selected channel, including repeated
emissions and inactive padding, as the sum of each bucket's own cost. -/
theorem ordinary_occurrences (ctx : Context) (rows : List RoutedEvent) (name : String) :
    additionalOccurrences ctx (ordinaryHeights rows) name =
      (InstructionChipId.all.map fun id => EventBuckets.paddedHeight rows id *
        rowOccurrences (ProtectedOrdinaryReceipt.component id) name).sum :=
  sum_slot_cost ctx rows name _

/-- Each tape position pays for one ordinary family. The semantic bound doubles the
chronological length once for the separately padded buckets. -/
theorem ordinary_occurrences_le (ctx : Context) (rows : List RoutedEvent) (name : String) :
    additionalOccurrences ctx (ordinaryHeights rows) name ≤ 2 * rows.length * ordinaryRowBound name := by
  rw [ordinary_occurrences]
  calc
    _ ≤ (InstructionChipId.all.map fun id => EventBuckets.paddedHeight rows id * ordinaryRowBound name).sum :=
      List.sum_le_sum (fun id _ => Nat.mul_le_mul_left _ (ordinary_row_width id name))
    _ ≤ _ := by
      rw [List.sum_map_mul_right]
      exact Nat.mul_le_mul_right _ (EventBuckets.sum_padded_heights rows)

/-- The existing mixed-shard preset covers the actual verifier and 38 installed components.
Other physical slots may spend the remaining per-channel allowance. The returned chronological
rows are the original semantic routing result on this same complete execution. -/
theorem fixedProviderPreset_ordinary_capacity (ctx : Context) {events : List ExecutionEvent}
    (execution : AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE fixedProviderPreset) (other : Component Fp → ℕ)
    (headroom : ∀ ch ∈ (assembly ctx).channels,
      additionalOccurrences ctx other ch.name ≤ SP1Prime - 1 - (2 ^ 30 + 1056) - 14 * 2 ^ 24
        - 2 ^ 22 * ordinaryRowBound ch.name) :
    ∃ rows, routeObservations? (policy SP1Prime ctx.image) ctx.image.program (fun _ => 0)
        ctx.source.realize events = some rows ∧ rows.length = events.countP ExecutionEvent.isOrdinary ∧
      (assembly ctx).interactionsFit .logUp (physicalHeights ctx fun t =>
        fixedHeight t + hintReadHeights events t + (ordinaryHeights rows t + other t)) := by
  obtain ⟨rows, route, count, _⟩ := admissibleExecution_routeObservations execution
  refine ⟨rows, route, count, fixedProviderPreset_capacity ctx execution preset _ ?_⟩
  intro ch registered
  rw [additionalOccurrences_add]
  have eventLimit : ctx.limits.events ≤ 2 ^ 21 := preset.1
  have active : rows.length ≤ 2 ^ 21 := by
    rw [count]
    exact List.countP_le_length.trans (execution.work.1.trans eventLimit)
  have padded : 2 * rows.length ≤ 2 ^ 22 := by omega
  have cost := (ordinary_occurrences_le ctx rows ch.name).trans (Nat.mul_le_mul_right _ padded)
  have maxWidth := Nat.mul_le_mul_left (2 ^ 22) (ordinaryRowBound_le ch.name)
  have room := headroom ch registered
  have enough : 2 ^ 22 * 126 ≤ SP1Prime - 1 - (2 ^ 30 + 1056) - 14 * 2 ^ 24 := by decide
  omega

/-- At least 293,600,224 additional occurrences remain on every registered channel after
the verifier and all 38 covered components. -/
theorem fixedProviderPreset_ordinary_fit (ctx : Context) {events : List ExecutionEvent}
    (execution : AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE fixedProviderPreset) (other : Component Fp → ℕ)
    (remaining : ∀ ch ∈ (assembly ctx).channels, additionalOccurrences ctx other ch.name ≤ 293600224) :
    ∃ rows, routeObservations? (policy SP1Prime ctx.image) ctx.image.program (fun _ => 0)
        ctx.source.realize events = some rows ∧ rows.length = events.countP ExecutionEvent.isOrdinary ∧
      (assembly ctx).interactionsFit .logUp (physicalHeights ctx fun t =>
        fixedHeight t + hintReadHeights events t + (ordinaryHeights rows t + other t)) := by
  apply fixedProviderPreset_ordinary_capacity ctx execution preset
  intro ch registered
  apply (remaining ch registered).trans
  have largest := Nat.mul_le_mul_left (2 ^ 22) (ordinaryRowBound_le ch.name)
  have atMax : 293600224 ≤ SP1Prime - 1 - (2 ^ 30 + 1056) - 14 * 2 ^ 24 - 2 ^ 22 * 126 := by decide
  omega

/-- The 38-table allocation fits on the actual mixed path with no additional demand rows. -/
theorem fixedProviderPreset_ordinary_base_fits (ctx : Context) {events : List ExecutionEvent}
    (execution : AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE fixedProviderPreset) :
    ∃ rows, routeObservations? (policy SP1Prime ctx.image) ctx.image.program (fun _ => 0)
        ctx.source.realize events = some rows ∧ rows.length = events.countP ExecutionEvent.isOrdinary ∧
      (assembly ctx).interactionsFit .logUp (physicalHeights ctx fun t =>
        fixedHeight t + hintReadHeights events t + ordinaryHeights rows t) := by
  simpa only [Nat.add_zero] using fixedProviderPreset_ordinary_fit ctx execution preset (fun _ => 0)
    (by intro ch registered; simp [additionalOccurrences])

end SP1Clean.Export.InstalledAssembly
