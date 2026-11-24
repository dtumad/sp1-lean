import SP1Clean.Proofs.Completeness.MixedMemoryHistory
import SP1Clean.Soundness.TypedMemoryBalance

/-! # Comparing real Memory writes with the mixed compiler's replay

At one location, an ordered replay observes the timestamp and value of each posted
record. Agreement of these physical occurrences, including readbacks and refreshes,
fixes the value at every cut. The HINT_READ word tables provide their original
typed Memory messages, including the removal of precisely the zero-multiplicity padding.
-/

namespace SP1Clean.TraceGen.MixedMemoryHistory

open Air.Flat Circuit Channels Semantics Soundness Machine FormalModel.Shard

private abbrev F := ZMod SP1Prime

/-- A chronological post at a fixed location. -/
def post (access : MemoryHistoryAccess) := (access.current, access.pushed)

private theorem heldAt_of_ordered_posts {left right : List MemoryHistoryAccess}
    (same : left.map post = right.map post) (seed : BitVec 64) (clock : ℕ) :
    MemoryHistoryAccess.heldAt seed clock left = MemoryHistoryAccess.heldAt seed clock right := by
  induction left generalizing right seed with
  | nil =>
    cases right with
    | nil => rfl
    | cons a rest => simp at same
  | cons a tail ih =>
    cases right with
    | nil => simp at same
    | cons b rest =>
      obtain ⟨eq, remaining⟩ := List.cons.inj same
      have time : a.current = b.current := congrArg Prod.fst eq
      have value : a.pushed = b.pushed := congrArg Prod.snd eq
      simp only [MemoryHistoryAccess.heldAt, time, value]
      split
      · rfl
      · exact ih remaining _

/-- Matching the full multiset of posted timestamps and words suffices. Strict physical
ordering makes the result independent of table bucketing and arbitrary source enumerations. -/
theorem heldAt_of_posts {left right : List MemoryHistoryAccess}
    (orderedLeft : (left.map (·.current)).Pairwise (· < ·)) (orderedRight : (right.map (·.current)).Pairwise (· < ·))
    (same : (left.map post).Perm (right.map post)) (seed : BitVec 64) (clock : ℕ) :
    MemoryHistoryAccess.heldAt seed clock left = MemoryHistoryAccess.heldAt seed clock right := by
  apply heldAt_of_ordered_posts _ seed clock
  apply same.eq_of_pairwise (le := fun a b => a.1 < b.1) (fun _ _ _ _ h h' => (Nat.lt_asymm h h').elim)
  · exact List.pairwise_map.mpr (List.pairwise_map.mp orderedLeft)
  · exact List.pairwise_map.mpr (List.pairwise_map.mp orderedRight)

/-- The original HINT_READ table has exactly the semantic word rows' posted messages.
It retains the input order of its actual continuing or final variant. -/
theorem hint_table_posts (last : Bool) (entries : List (Bool × HintReadWordChip.RowInput F))
    (data : ProverData F) (height) (active : ∀ e ∈ entries, e.2.2 = 1) :
    producedMessages (typedTableInteractionsWith (HintReadTransfers.wordTable last entries data height) memoryChannel) =
      (HintReadTransfers.selected last entries).map (fun r => r.1.ram.pushed) := by
  let inputs := HintReadTransfers.physicalInputs last entries
  let pair (r : HintReadWordChip.RowInput F) : List (TypedInteraction memoryChannel) :=
    [TypedInteraction.pulledIfValue memoryChannel r.2 r.1.ram.prior, TypedInteraction.pushedIfValue memoryChannel r.2 r.1.ram.pushed]
  have messages : typedTableInteractionsWith (HintReadTransfers.wordTable last entries data height) memoryChannel = inputs.flatMap pair := by
    apply List.map_injective_iff.mpr TypedInteraction.raw_injective
    rw [typedTableInteractionsWith_raw, HintReadTransfers.wordTable_memory, List.map_flatMap]
    rfl
  rw [messages, producedMessages_flatMap]
  have enabled (row : HintReadWordChip.RowInput F) (inRows : row ∈ HintReadTransfers.selected last entries) :
      producedMessages (pair row) = [row.1.ram.pushed] := by
    obtain ⟨entry, inside, rfl⟩ := List.mem_map.mp inRows
    have real := active entry (List.mem_filter.mp inside).1
    simp [pair, producedMessages, TypedInteraction.pulledIfValue, TypedInteraction.pushedIfValue,
      Channel.pulledIfValue, Channel.pushedIfValue, TypedInteraction.mult, TypedInteraction.message, ProvableType.fromElements_toElements, real]
  have inactive : producedMessages (pair 0) = [] := by
    simp [pair, producedMessages, TypedInteraction.pulledIfValue, TypedInteraction.pushedIfValue,
      Channel.pulledIfValue, Channel.pushedIfValue, TypedInteraction.mult]
  simp only [inputs, HintReadTransfers.physicalInputs, List.flatMap_append]
  rw [List.flatMap_congr enabled, List.flatMap_replicate, inactive]
  simp
  exact List.map_eq_flatMap.symm

private theorem variants (entries : List (Bool × HintReadWordChip.RowInput F)) :
    ((HintReadTransfers.selected false entries) ++ (HintReadTransfers.selected true entries)).Perm (entries.map Prod.snd) := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
    cases head with
    | mk flag row =>
      cases flag with
      | false => simpa [HintReadTransfers.selected] using ih.cons row
      | true =>
        simpa [HintReadTransfers.selected] using (List.perm_middle (a := row) (l₁ := HintReadTransfers.selected false tail)
          (l₂ := HintReadTransfers.selected true tail)).trans (ih.cons row)

/-- The two generated HINT_READ tables jointly account for every semantic host word
post once across the full mixed path, independently of their two physical heights. -/
theorem hint_tables_posts {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    (data : ProverData F) (height : ∀ last, WitnessGeneration.demandHeight (HintReadTransfers.selected last (HintReadTransfers.history image source events)).length ≤ UInt64.size) :
    let h := HintReadTransfers.history image source events
    let physical (last : Bool) := producedMessages (typedTableInteractionsWith (HintReadTransfers.wordTable last h data (height last)) memoryChannel)
    (physical false ++ physical true).Perm (h.map (fun e => e.2.1.ram.pushed)) := by
  intro h physical
  dsimp only [physical]
  rw [hint_table_posts _ _ _ _ (HintReadTransfers.history_active run), hint_table_posts _ _ _ _ (HintReadTransfers.history_active run)]
  simpa only [List.map_append, List.map_map, Function.comp_def] using (variants h).map (fun r => r.1.ram.pushed)

/-- Splitting CPU and HINT_READ occurrences out of tape order preserves their
multiplicities and per-event schedules, including all scheduled register refreshes. -/
theorem stream_partition (image : ProgramImage) (source : ExecutionSnapshot) (events : List ExecutionEvent)
    (rows : List MixedCompiledRow) (length : rows.length = events.length) :
    (stream image source events rows).Perm
      (rows.flatMap cpu ++ (HintReadTransfers.history image source events).map (fun e => hint e.2)) := by
  let extras (index : ℕ) := ((HintReadTransfers.rowsAt? image source events index).getD []).map (fun e => hint e.2)
  have split := List.flatMap_append_perm (List.finRange rows.length) (fun i => cpu rows[i]) (fun i => extras i.val)
  have cpuRows : (List.finRange rows.length).flatMap (fun i => cpu rows[i]) = rows.flatMap cpu := by
    rw [← List.flatMap_map]
    exact congrArg (List.flatMap cpu) (List.map_getElem_finRange rows)
  have extraRows : (List.finRange rows.length).flatMap (fun i => extras i.val) =
      (HintReadTransfers.history image source events).map (fun e => hint e.2) := by
    rw [HintReadTransfers.history, List.map_flatMap]
    change (List.finRange rows.length).flatMap (fun i => extras i.val) = (List.finRange events.length).flatMap (fun i => extras i.val)
    rw [length]
  rw [cpuRows, extraRows] at split
  exact split.symm

end SP1Clean.TraceGen.MixedMemoryHistory
