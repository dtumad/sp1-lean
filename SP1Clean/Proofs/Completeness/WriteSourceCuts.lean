import SP1Clean.Soundness.WriteSourcePulls
import SP1Clean.Proofs.Completeness.WriteSourceCoverage

/-! # A genuine predecessor at a checked execution cut funds its exact read

The original Memory pull is looked up in the complete 31-table physical inventory. Its
true interval is clipped at the accessing row's incoming clock, so aliases within that
instruction cannot overwrite the value read at the cut.
-/

namespace SP1Clean.WriteProbe.Counted

open Circuit Air.Flat Channels Semantics TraceGen Soundness Soundness.TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
/-- The existing low-limb handle and the public timestamp bound imply both 24-bit bounds. -/
theorem bounded_of_times (record : Readback (ZMod p))
    (lo : record.previousLow.val < 2 ^ 24 ∧ record.currentLow.val < 2 ^ 24)
    (previous : clkNat record.previousHigh record.previousLow < 2 ^ 48)
    (current : clkNat record.currentHigh record.currentLow < 2 ^ 48) : Bounded record := by
  unfold clkNat at previous current
  exact ⟨by omega, lo.1, by omega, lo.2⟩

/-- An active physical predecessor receipt covers the word held throughout its closed
interval. Both endpoints are the original Memory and publication clocks. -/
theorem covers_predecessor (tape : List (ZMod p × Readback (ZMod p))) (upper : ZMod p × ZMod p)
    (prior : MemoryMsg (ZMod p)) (occurrence : (1, AccessSupply.atClock upper prior) ∈ tape)
    (canonical : MemoryBoundary.CanonicalSpec prior) (key : ValidKey (MemoryMsg.locOf prior).busAddress)
    (word : MemoryMsg.isU64 prior) (time : ℕ) (priorBound : MemoryMsg.ClkBound prior)
    (covered : upper.2.val < 2 ^ 24 ∧ MemoryMsg.timeNat prior ≤ time ∧ time ≤ clkNat upper.1 upper.2 ∧
      clkNat upper.1 upper.2 < 2 ^ 48) :
    ∃ r ∈ live tape, Covers r ⟨Address.ofNat (MemoryMsg.locOf prior).busAddress, Address.ofNat time, prior.value⟩ := by
  let r := AccessSupply.atClock upper prior
  have liveRecord : r ∈ live tape := List.mem_map.mpr ⟨(1, r), List.mem_filter.mpr ⟨occurrence, by simp⟩, rfl⟩
  obtain ⟨low, first, last, bound⟩ := covered
  have bounded : Bounded r := bounded_of_times r ⟨priorBound, low⟩ ((first.trans last).trans_lt bound) bound
  have keyBound : Address.Bounded r.key := Address.bounded_of_isU64_asWord canonical.2.1
  have correct : Address.toNat r.key = (MemoryMsg.locOf prior).busAddress := (Address.toNat_asWord r.key).symm.trans canonical.2.2
  have covers := covers_record r bounded keyBound (correct ▸ key) word time (last.trans_lt bound) ⟨first, last⟩
  have fields : Address.ofNat (MemoryMsg.locOf prior).busAddress = r.key := correct ▸ Address.ofNat_toNat keyBound
  exact ⟨r, liveRecord, by rw [fields]; exact covers⟩

/-- A genuine, live original Memory pull covers its own held value throughout the exact
physical interval. The clock high limbs follow from integer time bounds. -/
theorem covers_pull (raw : AccessInventory.Source → Table (ZMod p))
    (registered : ∀ id, (raw id).component = AccessInventory.original id)
    (id : AccessInventory.Source) (physical : Array (ZMod p)) (rowMem : physical ∈ (raw id).table)
    (prior : MemoryMsg (ZMod p)) (pull : memoryChannel.pulledIfValue 1 prior ∈
      (raw id).component.operations.interactionValuesWith memoryChannel.toRaw ((raw id).environment physical))
    (canonical : MemoryBoundary.CanonicalSpec prior) (key : ValidKey (MemoryMsg.locOf prior).busAddress)
    (word : MemoryMsg.isU64 prior) (time : ℕ) (priorBound : MemoryMsg.ClkBound prior)
    (covered : let upper := AccessInventory.upper id ((raw id).environment physical)
               upper.2.val < 2 ^ 24 ∧ MemoryMsg.timeNat prior ≤ time ∧ time ≤ clkNat upper.1 upper.2 ∧
                 clkNat upper.1 upper.2 < 2 ^ 48) :
    ∃ r ∈ live (AccessInventory.records raw),
      Covers r ⟨Address.ofNat (MemoryMsg.locOf prior).busAddress, Address.ofNat time, prior.value⟩ := by
  exact covers_predecessor _ _ prior (AccessInventory.records_of_pull raw registered id physical rowMem 1 prior pull)
    canonical key word time priorBound covered

/-- For a selected genuine next access, the actual counted sources contain a record for
the exact semantic word at this incoming cut. Only facts about the original Memory row,
its checked clock, and the existing ordered location history enter this construction. -/
theorem covers_incoming_pull (raw : AccessInventory.Source → Table (ZMod p))
    (registered : ∀ id, (raw id).component = AccessInventory.original id)
    (id : AccessInventory.Source) (physical : Array (ZMod p)) (rowMem : physical ∈ (raw id).table)
    (history : MemoryLocationHistory) (chain : history.IsRecordChain) (strict : ∀ a ∈ history.accesses, a.previous < a.current)
    (timeline : Timeline) (row cut : ℕ) (touch : Touch p) (shape : TouchOK (timeline.start row) touch.1 touch.2)
    (access : MemoryHistoryAccess.ofTouch touch ∈ history.accesses)
    (window : MemoryMsg.timeNat touch.1.1 ≤ timeline.start cut ∧ timeline.start cut < MemoryMsg.timeNat touch.2)
    (pull : memoryChannel.pulledIfValue 1 touch.1.1 ∈ (raw id).component.operations.interactionValuesWith
      memoryChannel.toRaw ((raw id).environment physical))
    (rowTime : let upper := AccessInventory.upper id ((raw id).environment physical)
               clkNat upper.1 upper.2 = timeline.start row ∧ upper.2.val < 2 ^ 24)
    (rowBound : timeline.start row < 2 ^ 48) (priorBound : MemoryMsg.ClkBound touch.1.1)
    (canonical : MemoryBoundary.CanonicalSpec touch.1.1) (key : ValidKey (MemoryMsg.locOf touch.1.1).busAddress)
    (word : MemoryMsg.isU64 touch.1.1) :
    ∃ record ∈ live (AccessInventory.records raw),
      Covers record ⟨Address.ofNat (MemoryMsg.locOf touch.1.1).busAddress, Address.ofNat (timeline.start cut),
        Target.bitVecToWord (MemoryHistoryAccess.heldAt history.first.pulled (timeline.start cut) history.accesses)⟩ := by
  obtain ⟨before, held⟩ := history.incoming_covers_cut chain strict timeline row cut shape access window
  obtain ⟨r, member, covers⟩ := covers_pull raw registered id physical rowMem touch.1.1 pull canonical key word
    (timeline.start cut) priorBound ⟨rowTime.2, window.1, before.trans_eq rowTime.1.symm, rowTime.1.trans_lt rowBound⟩
  have value : Target.bitVecToWord (MemoryHistoryAccess.heldAt history.first.pulled (timeline.start cut) history.accesses) = touch.1.1.value :=
    Word.eq_of_toBitVec64_eq (Target.isU64_bitVecToWord _) word ((Target.toBitVec64_bitVecToWord _).trans held)
  exact ⟨r, member, by rw [value]; exact covers⟩

/-- A value-preserving register refresh covers its actual closed interval, including the
installation timestamp, using the Memory pull from the registered refresh slot. -/
theorem covers_refresh_pull (raw : AccessInventory.Source → Table (ZMod p))
    (registered : ∀ id, (raw id).component = AccessInventory.original id)
    (physical : Array (ZMod p)) (rowMem : physical ∈ (raw .refresh).table)
    (history : MemoryLocationHistory) (chain : history.IsRecordChain) (strict : ∀ a ∈ history.accesses, a.previous < a.current)
    (event : MemoryBumpEvent) (honest : event.WellFormed) (access : MemoryHistoryAccess.ofMemoryBump event ∈ history.accesses)
    (prior : MemoryMsg (ZMod p)) (pull : memoryChannel.pulledIfValue 1 prior ∈
      (raw .refresh).component.operations.interactionValuesWith memoryChannel.toRaw ((raw .refresh).environment physical))
    (times : let upper := AccessInventory.upper .refresh ((raw .refresh).environment physical)
             MemoryMsg.timeNat prior = event.prevTs ∧ clkNat upper.1 upper.2 = event.currTs ∧ upper.2.val < 2 ^ 24)
    (content : prior.value.toBitVec64 = BitVec.ofNat 64 event.value) (lower : MemoryMsg.ClkBound prior)
    (canonical : MemoryBoundary.CanonicalSpec prior) (key : ValidKey (MemoryMsg.locOf prior).busAddress) (word : MemoryMsg.isU64 prior)
    (time : ℕ) (within : event.prevTs ≤ time ∧ time ≤ event.currTs) :
    ∃ r ∈ live (AccessInventory.records raw), Covers r ⟨Address.ofNat (MemoryMsg.locOf prior).busAddress, Address.ofNat time,
      Target.bitVecToWord (MemoryHistoryAccess.heldAt history.first.pulled time history.accesses)⟩ := by
  obtain ⟨r, member, covers⟩ := covers_pull raw registered .refresh physical rowMem prior pull canonical key word time lower
    ⟨times.2.2, times.1.trans_le within.1, within.2.trans_eq times.2.1.symm, times.2.1.trans_lt honest.currLt⟩
  have held := (history.heldAt_memoryBump chain strict access within).trans content.symm
  have value : Target.bitVecToWord (MemoryHistoryAccess.heldAt history.first.pulled time history.accesses) = prior.value :=
    Word.eq_of_toBitVec64_eq (Target.isU64_bitVecToWord _) word ((Target.toBitVec64_bitVecToWord _).trans held)
  exact ⟨r, member, by rw [value]; exact covers⟩

/-- After the last genuine update to a touched location, its actual registered finalizer funds
the exact held word at every later representable cut, including the last update time itself. -/
theorem covers_final_pull (raw : AccessInventory.Source → Table (ZMod p))
    (registered : ∀ id, (raw id).component = AccessInventory.original id)
    (ram : Bool) (physical : Array (ZMod p)) (rowMem : physical ∈ (raw (.finalizer ram)).table)
    (history : MemoryLocationHistory) (chain : history.IsRecordChain) (strict : ∀ a ∈ history.accesses, a.previous < a.current)
    (record : MemoryMsg (ZMod p)) (pull : memoryChannel.pulledIfValue 1 record ∈
      (raw (.finalizer ram)).component.operations.interactionValuesWith memoryChannel.toRaw ((raw (.finalizer ram)).environment physical))
    (timestamp : history.last.current = MemoryMsg.timeNat record) (content : history.last.pushed = record.value.toBitVec64)
    (prior : MemoryMsg.ClkBound record) (canonical : MemoryBoundary.FinalSpec record)
    (key : ValidKey (MemoryMsg.locOf record).busAddress) (word : MemoryMsg.isU64 record)
    (time : ℕ) (within : history.last.current ≤ time) (fits : time < 2 ^ 48) :
    ∃ r ∈ live (AccessInventory.records raw), Covers r ⟨Address.ofNat (MemoryMsg.locOf record).busAddress, Address.ofNat time,
      Target.bitVecToWord (MemoryHistoryAccess.heldAt history.first.pulled time history.accesses)⟩ := by
  obtain ⟨_, upper⟩ := finalReadback_clocks record
  have top : (16777215 : ZMod p).val = 16777215 := ZMod.val_natCast_of_lt
    (Nat.lt_trans (by decide : (16777215 : ℕ) < 2 ^ 25) (Fact.out (p := 2 ^ 25 < p)))
  have upperTime : clkNat (16777215 : ZMod p) 16777215 = 2 ^ 48 - 1 := upper
  have withinUpper : time ≤ clkNat (16777215 : ZMod p) 16777215 := by rw [upperTime]; omega
  obtain ⟨r, member, covers⟩ := covers_pull raw registered (.finalizer ram) physical rowMem record pull canonical key word time prior
    ⟨top.trans_lt (by decide), timestamp.symm.trans_le within, withinUpper, upperTime.trans_lt (by decide)⟩
  have held := (history.heldAt_final chain strict within).trans content
  have value : Target.bitVecToWord (MemoryHistoryAccess.heldAt history.first.pulled time history.accesses) = record.value :=
    Word.eq_of_toBitVec64_eq (Target.isU64_bitVecToWord _) word ((Target.toBitVec64_bitVecToWord _).trans held)
  exact ⟨r, member, by rw [value]; exact covers⟩

end SP1Clean.WriteProbe.Counted
