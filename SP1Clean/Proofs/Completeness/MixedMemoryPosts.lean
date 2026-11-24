import SP1Clean.Proofs.Completeness.MixedMemoryHistory
import SP1Clean.Proofs.Completeness.MixedBumpInventory
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

/-- Timestamp and value of the predecessor consumed by the same access. -/
def prior (access : MemoryHistoryAccess) := (access.previous, access.pulled)

private theorem posts_shift (first : MemoryHistoryAccess) (rest : List MemoryHistoryAccess)
    (chain : (first :: rest).IsChain MemoryHistoryAccess.Continues) :
    prior first :: ((first :: rest).map post) =
      (first :: rest).map prior ++ [post ((first :: rest).getLast (by simp))] := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih =>
    obtain ⟨link, links⟩ := List.isChain_cons_cons.mp chain
    have joins : post first = prior next := Prod.ext link.2.1.symm link.2.2.symm
    apply congrArg (prior first :: ·)
    change post first :: _ = _
    rw [joins]
    exact ih next links

/-- For genuine handoff chains, equal predecessor occurrences and the same endpoints
determine every post. This includes instructions whose output word is computed by the chip. -/
theorem posts_of_priors {left right : MemoryLocationHistory}
    (physical : left.IsRecordChain) (compiled : right.IsRecordChain)
    (initial : prior left.first = prior right.first) (final : post left.last = post right.last)
    (same : (left.accesses.map prior).Perm (right.accesses.map prior)) :
    (left.accesses.map post).Perm (right.accesses.map post) := by
  have shifts (h : MemoryLocationHistory) (chain : h.IsRecordChain) :
      prior h.first :: h.accesses.map post = h.accesses.map prior ++ [post h.last] := by
    cases eq : h.accesses with
    | nil => exact (h.nonempty eq).elim
    | cons a rest =>
      simpa [MemoryLocationHistory.first, MemoryLocationHistory.last, eq] using
        posts_shift a rest (eq ▸ chain.adjacent)
  apply List.Perm.cons_inv (a := prior left.first)
  conv_rhs => rw [initial]
  rw [shifts left physical, shifts right compiled, final]
  exact same.append_right _

private def hintPair (r : HintReadWordChip.RowInput F) : List (TypedInteraction (memoryChannel (p := SP1Prime))) :=
  [TypedInteraction.pulledIfValue memoryChannel r.2 r.1.ram.prior,
   TypedInteraction.pushedIfValue memoryChannel r.2 r.1.ram.pushed]

private theorem hintMessages (last : Bool) (entries : List (Bool × HintReadWordChip.RowInput F))
    (data : ProverData F) (height) :
    typedTableInteractionsWith (HintReadTransfers.wordTable last entries data height) memoryChannel =
      (HintReadTransfers.physicalInputs last entries).flatMap hintPair := by
  apply List.map_injective_iff.mpr TypedInteraction.raw_injective
  rw [typedTableInteractionsWith_raw, HintReadTransfers.wordTable_memory, List.map_flatMap]
  rfl

private theorem hintSide (last : Bool) (entries : List (Bool × HintReadWordChip.RowInput F))
    (active : ∀ e ∈ entries, e.2.2 = 1) (select : List (TypedInteraction (memoryChannel (p := SP1Prime))) → List (MemoryMsg F))
    (value : HintReadWordChip.RowInput F → MemoryMsg F)
    (enabled : ∀ row : HintReadWordChip.RowInput F, row.2 = 1 → select (hintPair row) = [value row])
    (inactive : select (hintPair 0) = []) :
    (HintReadTransfers.physicalInputs last entries).flatMap (fun row => select (hintPair row)) =
      (HintReadTransfers.selected last entries).map value := by
  have live (row : HintReadWordChip.RowInput F) (inRows : row ∈ HintReadTransfers.selected last entries) :
      select (hintPair row) = [value row] := by
    obtain ⟨entry, inside, rfl⟩ := List.mem_map.mp inRows
    exact enabled entry.2 (active entry (List.mem_filter.mp inside).1)
  simp only [HintReadTransfers.physicalInputs, List.flatMap_append]
  rw [List.flatMap_congr live, List.flatMap_replicate, inactive]
  simp
  exact List.map_eq_flatMap.symm

/-- Both signed sides of the physical HINT_READ Memory ledger, including the removal of
exactly the inactive padding. Their order is the compiler's order within this variant. -/
theorem hint_table_memory (last : Bool) (entries : List (Bool × HintReadWordChip.RowInput F))
    (data : ProverData F) (height) (active : ∀ e ∈ entries, e.2.2 = 1) :
    let messages := typedTableInteractionsWith (HintReadTransfers.wordTable last entries data height) memoryChannel
    let rows := HintReadTransfers.selected last entries
    consumedMessages messages = rows.map (fun r => r.1.ram.prior) ∧
      producedMessages messages = rows.map (fun r => r.1.ram.pushed) := by
  dsimp only
  rw [hintMessages, consumedMessages_flatMap, producedMessages_flatMap]
  constructor <;> apply hintSide last entries active <;>
    simp +contextual [hintPair, consumedMessages, producedMessages, TypedInteraction.pulledIfValue,
      TypedInteraction.pushedIfValue, Channel.pulledIfValue, Channel.pushedIfValue, TypedInteraction.mult,
      TypedInteraction.message, ProvableType.fromElements_toElements]

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

/-- The two generated word variants jointly account for every HINT_READ transfer on
both sides of the Memory ledger, independently of their physical heights. -/
theorem hint_tables_memory {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    (data : ProverData F) (height : ∀ last, WitnessGeneration.demandHeight (HintReadTransfers.selected last (HintReadTransfers.history image source events)).length ≤ UInt64.size) :
    let h := HintReadTransfers.history image source events
    let messages (last : Bool) := typedTableInteractionsWith (HintReadTransfers.wordTable last h data (height last)) memoryChannel
    (consumedMessages (messages false) ++ consumedMessages (messages true)).Perm (h.map (fun e => e.2.1.ram.prior)) ∧
      (producedMessages (messages false) ++ producedMessages (messages true)).Perm (h.map (fun e => e.2.1.ram.pushed)) := by
  intro h messages
  have rows (last : Bool) := hint_table_memory last h data (height last) (HintReadTransfers.history_active run)
  dsimp only [messages]
  rw [(rows false).1, (rows true).1, (rows false).2, (rows true).2]
  exact ⟨by simpa only [List.map_append, List.map_map, Function.comp_def] using (variants h).map (fun r => r.1.ram.prior),
    by simpa only [List.map_append, List.map_map, Function.comp_def] using (variants h).map (fun r => r.1.ram.pushed)⟩

/-- The genuine CPU touches without the distinct register refresh table. -/
def instruction : MixedCompiledRow → List MemoryHistoryAccess
  | .ordinary row => row.stamped.map (MemoryHistoryAccess.ofStamped row.routed.clock)
  | .syscall frontier base call => (scheduleAccessPlan frontier base (syscallRegisterPlan call)).stampedTouches.map
      (MemoryHistoryAccess.ofStamped base)

private theorem schedule_partition (base : ℕ) (s : AccessSchedule) :
    (MemoryHistoryAccess.ofAccessSchedule base s).Perm
      (s.memoryBumps.map MemoryHistoryAccess.ofMemoryBump ++ s.stampedTouches.map (MemoryHistoryAccess.ofStamped base)) := by
  have split := (List.flatMap_append_perm s.accesses
    (fun a => a.memoryBump?.toList.map MemoryHistoryAccess.ofMemoryBump)
    (fun a => [MemoryHistoryAccess.ofStamped base a.stamped])).symm
  simp only [AccessSchedule.stampedTouches, AccessSchedule.memoryBumps, List.map_map,
    List.filterMap_eq_flatMap_toList, List.map_flatMap]
  exact split.trans (by rw [← List.map_eq_flatMap]; rfl)

/-- All CPU schedules partition into the exact separately generated register refresh list
and the chronological instruction touches. Every aliased register occurrence survives. -/
theorem cpu_partition (rows : List MixedCompiledRow) :
    (rows.flatMap cpu).Perm
      ((MixedBumpInput.memoryRows (rows.map MixedCompiledRow.bumpInput)).map MemoryHistoryAccess.ofMemoryBump ++
        rows.flatMap instruction) := by
  let bumps (row : MixedCompiledRow) := row.bumpInput.refreshes.map MemoryHistoryAccess.ofMemoryBump
  have row (r : MixedCompiledRow) : (cpu r).Perm (bumps r ++ instruction r) := by
    cases r <;> apply schedule_partition
  exact (List.Perm.flatMap_left rows (fun r _ => row r)).trans (by
    simpa only [MixedBumpInput.memoryRows, List.flatMap_map, List.map_flatMap, Function.comp_def, bumps] using
      (List.flatMap_append_perm rows bumps instruction).symm)

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
