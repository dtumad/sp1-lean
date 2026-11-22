import SP1Clean.Proofs.Completeness.ExecutionObservation
import ToClean.Air.DemandPadding

/-! # Total physical height of the chronological ordinary-instruction buckets

Every chronological occurrence increases one registry bucket. Demand padding rounds the
buckets independently and leaves empty buckets at height zero.
-/

namespace SP1Clean.TraceGen.EventBuckets
open Circuit Air.Flat Semantics Machine Soundness FormalModel.Shard

private theorem occurs_once (row : RoutedEvent) (ids : List InstructionChipId) :
    (ids.map fun id => (row.forId? id).toList.length).sum = ids.count row.id := by
  induction ids with
  | nil => rfl
  | cons id rest ih =>
    by_cases eq : row.id = id
    · cases row with
      | mk actual event =>
        subst id
        simp [ih, Nat.add_comm]
    · simp [RoutedEvent.forId?_eq_none_of_ne _ eq, ih, Ne.symm eq]

/-- All 25 buckets together contain exactly the chronological ordinary rows, counting
repeated occurrences at their original positions. -/
theorem sum_lengths (events : List RoutedEvent) :
    (InstructionChipId.all.map fun id => (ofChronological events id).length).sum = events.length := by
  induction events with
  | nil => simp
  | cons row later ih =>
    simp only [ofChronological_cons, List.length_append, List.sum_map_add, ih, List.length_cons]
    have one := (occurs_once row InstructionChipId.all).trans
      (List.count_eq_one_of_mem InstructionChipId.all_nodup (InstructionChipId.mem_all row.id))
    omega

/-- Native physical height of the installed instruction family selected by the released
typed registry, obtained from the stable chronological bucket. -/
def paddedHeight (rows : List RoutedEvent) (id : InstructionChipId) : ℕ :=
  WitnessGeneration.demandHeight (ofChronological rows id).length

/-- Separately padding the 25 tables costs at most twice the count of all ordinary events
together, regardless of their distribution among instruction families. -/
theorem sum_padded_heights (rows : List RoutedEvent) :
    (InstructionChipId.all.map (paddedHeight rows)).sum ≤ 2 * rows.length := by
  calc
    _ ≤ (InstructionChipId.all.map fun id => 2 * (ofChronological rows id).length).sum :=
      List.sum_le_sum (fun id _ => (WitnessGeneration.demandHeight_bounds _).2)
    _ = 2 * rows.length := by rw [List.sum_map_mul_left, sum_lengths]

end SP1Clean.TraceGen.EventBuckets
