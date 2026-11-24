import SP1Clean.Proofs.Completeness.MemoryVersionHistory
import SP1Clean.Semantics.Memory.MemorySnapshot

/-! # Closed read-back intervals and sparse untouched finalizers

A value-preserving physical access authenticates both ends of its interval. A final
record at timestamp zero belongs to an untouched location when every genuine access
strictly advances its timestamp. The additional sparse location starts with its source
snapshot word and retains that word for every probe time.
-/

namespace SP1Clean.TraceGen.MemoryHistoryAccess

private theorem heldAt_current_ordered (seed : BitVec 64) {records : List MemoryHistoryAccess}
    (ordered : records.Pairwise (fun a b => a.current < b.current)) {a : MemoryHistoryAccess}
    (member : a ∈ records) : heldAt seed a.current records = a.pushed := by
  induction records generalizing seed with
  | nil => contradiction
  | cons first rest ih =>
    obtain ⟨before, tail⟩ := List.pairwise_cons.mp ordered
    rcases List.mem_cons.mp member with rfl | later
    · cases rest with
      | nil => simp [heldAt]
      | cons second later => simp [heldAt, before second List.mem_cons_self]
    · rw [heldAt, ite_eq_right (Nat.not_lt_of_ge (before a later).le)]
      exact ih first.pushed tail later

/-- At its exact push timestamp a genuine access installs its own pushed word. -/
theorem heldAt_current (seed : BitVec 64) {records : List MemoryHistoryAccess}
    (links : List.IsChain Continues records) (strict : ∀ r ∈ records, r.previous < r.current)
    {a : MemoryHistoryAccess} (member : a ∈ records) : heldAt seed a.current records = a.pushed := by
  let earlier (a b : MemoryHistoryAccess) := a.current < b.current
  let _ : Trans earlier earlier earlier := ⟨Nat.lt_trans⟩
  have chronological : List.IsChain earlier records := by
    apply List.IsChain.imp_of_mem_imp _ links
    intro a b _ occurs handoff
    change a.current < b.current
    rw [← handoff.2.1]
    exact strict b occurs
  exact heldAt_current_ordered seed (List.isChain_iff_pairwise.mp chronological) member

end SP1Clean.TraceGen.MemoryHistoryAccess

namespace SP1Clean.TraceGen.MemoryLocationHistory

/-- A genuine unchanged-word access supplies its pulled value throughout the closed interval
including the push itself, even in the presence of other accesses to the same location. -/
theorem heldAt_readback (history : MemoryLocationHistory) (chain : history.IsRecordChain)
    (strict : ∀ a ∈ history.accesses, a.previous < a.current) {a : MemoryHistoryAccess}
    (member : a ∈ history.accesses) (unchanged : a.pushed = a.pulled)
    {time : ℕ} (covers : a.previous ≤ time ∧ time ≤ a.current) :
    MemoryHistoryAccess.heldAt history.first.pulled time history.accesses = a.pulled := by
  rcases covers.2.lt_or_eq with before | atPush
  · exact history.heldAt_interval chain strict member ⟨covers.1, before⟩
  · exact atPush ▸ (MemoryHistoryAccess.heldAt_current _ chain.adjacent strict member).trans unchanged

/-- Specialization to the compiler's genuine value-preserving MemoryBump records. -/
theorem heldAt_memoryBump (history : MemoryLocationHistory) (chain : history.IsRecordChain)
    (strict : ∀ a ∈ history.accesses, a.previous < a.current) {event : MemoryBumpEvent}
    (member : MemoryHistoryAccess.ofMemoryBump event ∈ history.accesses)
    {time : ℕ} (covers : event.prevTs ≤ time ∧ time ≤ event.currTs) :
    MemoryHistoryAccess.heldAt history.first.pulled time history.accesses = BitVec.ofNat 64 event.value :=
  history.heldAt_readback chain strict member rfl covers

/-- Every original finalizer for a touched key has a strictly positive clock. -/
theorem finalEntry_clock_pos (history : MemoryLocationHistory)
    (strict : ∀ a ∈ history.accesses, a.previous < a.current) : 0 < history.finalEntry.clk :=
  Nat.zero_lt_of_lt (strict history.last (List.getLast_mem history.nonempty))

end SP1Clean.TraceGen.MemoryLocationHistory

namespace SP1Clean.TraceGen

open Semantics

private theorem history_empty_iff {stream : List MemoryHistoryAccess} {loc : MemLoc} :
    memoryHistoryAt stream loc = [] ↔ loc ∉ touchedMemoryLocations stream := by
  constructor
  · exact fun absent used => memoryHistoryAt_ne_nil_of_mem used absent
  · intro unused
    apply List.filter_eq_nil_iff.mpr
    intro a member same
    exact unused (mem_touchedMemoryLocations.mpr ⟨a, member, of_decide_eq_true same⟩)

/-- For a queried sparse location, zero is the last clock precisely when its filtered
access history is empty. The deterministic inventory still contains only touched locations. -/
theorem finalClock_zero_iff_untouched {stream : List MemoryHistoryAccess} {loc : MemLoc}
    (strict : ∀ a ∈ memoryHistoryAt stream loc, a.previous < a.current) :
    (((memoryHistoryAt stream loc).getLast?.map (·.current)).getD 0 = 0) ↔ loc ∉ touchedMemoryLocations stream := by
  rw [← history_empty_iff]
  cases h : memoryHistoryAt stream loc with
  | nil => simp
  | cons a rest =>
    rw [h] at strict
    have pos := strict ((a :: rest).getLast (by simp)) (List.getLast_mem (by simp))
    simp [List.getLast?_eq_some_getLast, Nat.ne_of_gt (Nat.zero_lt_of_lt pos)]

/-- A sparse time-zero final record authenticates the canonical source snapshot word at
every time, including zero. This applies to any queried untouched location. -/
theorem heldAt_zeroFinal (source : MemorySnapshot) {stream : List MemoryHistoryAccess} {loc : MemLoc}
    (strict : ∀ a ∈ memoryHistoryAt stream loc, a.previous < a.current)
    (zeroClock : ((memoryHistoryAt stream loc).getLast?.map (·.current)).getD 0 = 0) (time : ℕ) :
    MemoryHistoryAccess.matchingValues 0 (source.read loc) time (memoryHistoryAt stream loc) = [source.read loc] ∧
      MemoryHistoryAccess.heldAt (source.read loc) time (memoryHistoryAt stream loc) = source.read loc := by
  have unused := (finalClock_zero_iff_untouched strict).mp zeroClock
  have absent := history_empty_iff.mpr unused
  simp [absent, MemoryHistoryAccess.matchingValues, MemoryHistoryAccess.heldAt]

end SP1Clean.TraceGen
