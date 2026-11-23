import SP1Clean.Proofs.Completeness.MemoryReadbackIntervals

/-! # Coverage of incoming CPU cuts by genuine predecessor records

A mutating Memory push lands strictly after its row's incoming clock. An access at exactly
that clock is value-preserving. Real CPU starts are at least eight ticks apart, so clipping a
predecessor interval to the incoming clock drops no eligible CPU cut before its push.
-/

namespace SP1Clean.TraceGen.MemoryLocationHistory

open Semantics Soundness.TimedGrounding

variable {p : ℕ} [Fact p.Prime]

/-- The closed interval emitted by a Memory pull carries the pulled word even at the
accessing row's exact incoming clock. Later aliased predecessors may have an empty interval. -/
theorem heldAt_incoming (history : MemoryLocationHistory) (chain : history.IsRecordChain)
    (strict : ∀ a ∈ history.accesses, a.previous < a.current)
    {rowTime time : ℕ} {touch : Touch p} (shape : TouchOK rowTime touch.1 touch.2)
    (member : MemoryHistoryAccess.ofTouch touch ∈ history.accesses)
    (first : MemoryMsg.timeNat touch.1.1 ≤ time) (last : time ≤ rowTime) :
    MemoryHistoryAccess.heldAt history.first.pulled time history.accesses = touch.1.1.value.toBitVec64 := by
  have future := shape.push_lo
  by_cases inside : time < MemoryMsg.timeNat touch.2
  · exact history.heldAt_interval chain strict member ⟨first, inside⟩
  have equal : time = MemoryMsg.timeNat touch.2 := by omega
  rcases shape.push_kind with ⟨same, _⟩ | effect
  · apply history.heldAt_readback chain strict member (congrArg Word.toBitVec64 same) ⟨first, equal.le⟩
  · have positive : 0 < writeOffset (MemoryMsg.locOf touch.2) := by
      cases MemoryMsg.locOf touch.2 <;> simp only [writeOffset_reg, writeOffset_ram] <;> decide
    omega

/-- Any genuine incoming cut in the original half-open predecessor interval is contained in
its clipped receipt. The same physical word therefore funds every such CPU cut. -/
theorem incoming_covers_cut (history : MemoryLocationHistory) (chain : history.IsRecordChain)
    (strict : ∀ a ∈ history.accesses, a.previous < a.current)
    (timeline : Timeline) (row cut : ℕ) {touch : Touch p} (shape : TouchOK (timeline.start row) touch.1 touch.2)
    (member : MemoryHistoryAccess.ofTouch touch ∈ history.accesses)
    (within : MemoryMsg.timeNat touch.1.1 ≤ timeline.start cut ∧ timeline.start cut < MemoryMsg.timeNat touch.2) :
    timeline.start cut ≤ timeline.start row ∧
      MemoryHistoryAccess.heldAt history.first.pulled (timeline.start cut) history.accesses = touch.1.1.value.toBitVec64 := by
  have before : cut ≤ row := by
    by_contra! later
    have next := timeline.start_le_of_le (show row + 1 ≤ cut by omega)
    have gap := timeline.gap row
    have latest := shape.push_hi
    omega
  have order := timeline.start_le_of_le before
  exact ⟨order, history.heldAt_incoming chain strict shape member within.1 order⟩

end SP1Clean.TraceGen.MemoryLocationHistory
