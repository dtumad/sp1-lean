import SP1Clean.Native.Operations.WriteProbeAccess
import SP1Clean.Proofs.Completeness.WriteCountedRouting
import SP1Clean.Proofs.Completeness.WriteSparseBoundaries

/-! # Covering a WRITE request with its genuine physical predecessor

A bounded original receipt covers precisely the expected key, held word and interval.
An otherwise untouched x12 or RAM address has a concrete checked pair of boundary rows
that covers every representable incoming clock and returns its exact source snapshot word.
-/

namespace SP1Clean.WriteProbe.Counted

open Circuit Air.Flat Semantics TraceGen Soundness Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- The native circuit accepts the full desired read directly from its original physical
split-clock receipt at every covered incoming clock. -/
theorem covers_record (r : Readback (ZMod p)) (bounded : Bounded r)
    (keyBound : Address.Bounded r.key) (legal : ValidKey (Address.toNat r.key))
    (word : Word.isU64 r.value) (clock : ℕ) (fits : clock < 2 ^ 48)
    (within : clkNat r.previousHigh r.previousLow ≤ clock ∧ clock ≤ clkNat r.currentHigh r.currentLow) :
    Covers r ⟨r.key, Address.ofNat clock, r.value⟩ := by
  obtain ⟨ph, pl, ch, cl⟩ := bounded
  obtain ⟨previous, prevHigh, prevLow⟩ := ClockParts.split_spec _ _ ph pl
  obtain ⟨current, currHigh, currLow⟩ := ClockParts.split_spec _ _ ch cl
  have low := (ClockParts.split r.previousHigh r.previousLow).time previous
  have high := (ClockParts.split r.currentHigh r.currentLow).time current
  rw [prevHigh, prevLow] at low
  rw [currHigh, currLow] at high
  refine ⟨⟨keyBound, legal, word, ClockParts.address_bounded _ previous, Address.bounded_ofNat _, ClockParts.address_bounded _ current, ?_, ?_⟩, rfl⟩
  · change Address.toNat (ClockParts.split r.previousHigh r.previousLow).address ≤ Address.toNat (Address.ofNat clock)
    simpa only [low, Address.toNat_ofNat _ fits] using within.1
  · change Address.toNat (Address.ofNat clock) ≤ Address.toNat (ClockParts.split r.currentHigh r.currentLow).address
    simpa only [high, Address.toNat_ofNat _ fits] using within.2

/-- Both timestamp pairs on an encoded Memory predecessor fit the 24-bit supply columns. -/
theorem bounded_compiled_entry (entry : MemRecordEntry) (last : ℕ) (previous : entry.clk < 2 ^ 48)
    (current : last < 2 ^ 48) :
    Bounded (AccessSupply.atClock (F := ZMod p) ((last / 2 ^ 24 : ℕ), (last % 2 ^ 24 : ℕ)) entry.toMemoryMsg) := by
  have characteristic := Fact.out (p := 2 ^ 24 < p)
  change ((entry.clk / 2 ^ 24 : ℕ) : ZMod p).val < _ ∧ ((entry.clk % 2 ^ 24 : ℕ) : ZMod p).val < _ ∧
    ((last / 2 ^ 24 : ℕ) : ZMod p).val < _ ∧ ((last % 2 ^ 24 : ℕ) : ZMod p).val < _
  repeat' rw [ZMod.val_natCast_of_lt (by omega)]
  omega

/-- A canonical split-clock Memory entry covers its exact field-encoded address and value up to
the physical receipt's closing clock. This applies to original accesses and to finalizers. -/
theorem covers_compiled_entry (entry : MemRecordEntry) (last time : ℕ) (legal : ValidKey entry.addr)
    (lo : entry.clk ≤ time) (hi : time ≤ last) (fits : last < 2 ^ 48) :
    let receipt := AccessSupply.atClock (F := ZMod p) ((last / 2 ^ 24 : ℕ), (last % 2 ^ 24 : ℕ)) entry.toMemoryMsg
    Covers receipt ⟨Address.ofNat entry.addr, Address.ofNat time, Target.bitVecToWord (BitVec.ofNat 64 entry.value)⟩ := by
  intro receipt
  have characteristic := Fact.out (p := 2 ^ 24 < p)
  have bounded := bounded_compiled_entry (p := p) entry last (lo.trans_lt (hi.trans_lt fits)) fits
  have key : receipt.key = Address.ofNat entry.addr := rfl
  have addressFits : entry.addr < 2 ^ 48 := by
    rcases legal with reg | ram
    · omega
    · exact ram.2.1
  have decode (n : ℕ) (small : n < 2 ^ 48) :
      clkNat ((n / 2 ^ 24 : ℕ) : ZMod p) ((n % 2 ^ 24 : ℕ) : ZMod p) = n := by
    unfold clkNat
    repeat' rw [ZMod.val_natCast_of_lt (by omega)]
    omega
  have value : receipt.value = Target.bitVecToWord (BitVec.ofNat 64 entry.value) :=
    Word.eq_of_toBitVec64_eq (wordOfNat_isU64 _) (Target.isU64_bitVecToWord _)
      ((toBitVec64_wordOfNat _).trans (Target.toBitVec64_bitVecToWord _).symm)
  have within : clkNat receipt.previousHigh receipt.previousLow ≤ time ∧ time ≤ clkNat receipt.currentHigh receipt.currentLow := by
    change clkNat ((entry.clk / 2 ^ 24 : ℕ) : ZMod p) ((entry.clk % 2 ^ 24 : ℕ) : ZMod p) ≤ _ ∧
      _ ≤ clkNat ((last / 2 ^ 24 : ℕ) : ZMod p) ((last % 2 ^ 24 : ℕ) : ZMod p)
    rw [decode _ (by omega), decode last fits]
    exact ⟨lo, hi⟩
  have result := covers_record receipt bounded (key ▸ Address.bounded_ofNat _) (by rwa [key, Address.toNat_ofNat _ addressFits])
    (wordOfNat_isU64 _) time (hi.trans_lt fits) within
  rwa [key, value] at result

/-- Each extra key requested from the real snapshot has a concrete original finalizer row
that supplies the entire time range as a source for the counted table. Both boundary rows
pass their original local constraints and cancel their original Memory messages. -/
theorem sparse_covers (snapshot : MemorySnapshot) (stream : List MemoryHistoryAccess) (requested : List ℕ)
    (key : ℕ) (wanted : key ∈ requested) (legal : ValidKey key)
    (fresh : key ∉ (memoryInitialEntries stream).map MemRecordEntry.addr) (time : ℕ) (timeBound : time < 2 ^ 48)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ∃ rows ∈ SparseBoundary.buildAll snapshot ((memoryInitialEntries stream).map MemRecordEntry.addr) requested data hint,
      rows.key = key ∧ rows.Checked snapshot data ∧
      ∃ record : MemoryMsg (ZMod p), (finalComponent rows.ram).operations.interactionValuesWith readbackChannel.toRaw
          (Environment.fromArray rows.final data) = [readbackChannel.pushedValue (finalReadback record)] ∧
        (MemoryMsg.locOf record).busAddress = key ∧
        Covers (finalReadback record) ⟨Address.ofNat key, Address.ofNat time,
          Target.bitVecToWord (snapshot.read (MemoryMsg.locOf record))⟩ := by
  let touched := (memoryInitialEntries stream).map MemRecordEntry.addr
  have member := SparseBoundary.mem_keys.mpr (Or.inr ⟨wanted, legal⟩ : key ∈ touched ∨ _)
  obtain ⟨i, inside, eq⟩ := List.mem_iff_getElem.mp member
  obtain ⟨rows, live, placed, checked⟩ := SparseBoundary.buildAll_covers snapshot touched requested ⟨i, inside⟩ (eq ▸ fresh) data hint
  have used : rows.key = key := placed.trans eq
  let r := SparseBoundary.sourceRecord snapshot rows.ram (Environment.fromArray rows.initial data)
  have atKey : MemoryBoundary.SnapshotAtSpec snapshot key r := used ▸ checked.2.2.1
  have address := atKey.1.canonical.2.2.symm.trans atKey.2
  obtain ⟨first, last, _⟩ := SparseBoundary.sparse_interval snapshot stream atKey fresh
  have zero := atKey.1.2.2.1
  change r.clk_high.val * 2 ^ 24 + r.clk_low.val = 0 at zero
  have top : (16777215 : ZMod p).val = 16777215 := ZMod.val_natCast_of_lt (Nat.lt_trans (by decide : (16777215 : ℕ) < 2 ^ 25) (Fact.out (p := 2 ^ 25 < p)))
  have bounded : Bounded (finalReadback r) := by
    change r.clk_high.val < _ ∧ r.clk_low.val < _ ∧ (16777215 : ZMod p).val < _ ∧ (16777215 : ZMod p).val < _
    rw [top]
    omega
  have keyBound : Address.Bounded (finalReadback r).key := Address.bounded_of_isU64_asWord atKey.1.canonical.2.1
  have asNat : Address.toNat (finalReadback r).key = key :=
    (Address.toNat_asWord (finalReadback r).key).symm.trans atKey.2
  have window : clkNat (finalReadback r).previousHigh (finalReadback r).previousLow ≤ time ∧
      time ≤ clkNat (finalReadback r).currentHigh (finalReadback r).currentLow := by omega
  have covers := covers_record (finalReadback r) bounded keyBound (asNat ▸ legal) atKey.1.1 time timeBound window
  have keyFields : Address.ofNat key = (finalReadback r).key := asNat ▸ Address.ofNat_toNat keyBound
  have wordFields : Target.bitVecToWord (snapshot.read (MemoryMsg.locOf r)) = r.value :=
    Word.eq_of_toBitVec64_eq (Target.isU64_bitVecToWord _) atKey.1.1
      ((Target.toBitVec64_bitVecToWord _).trans atKey.1.2.2.2.2.1)
  exact ⟨rows, live, used, checked, r, checked.2.2.2.2.2, address, by rw [keyFields, wordFields]; exact covers⟩

end SP1Clean.WriteProbe.Counted
