import SP1Clean.Proofs.Completeness.MixedCommitCalls
import SP1Clean.Soundness.HostCommitEnsemble

/-! # Compiling the two native commitment-bank histories

Rows are generated from the complete incoming bank and the actual ordered calls. Each update
carries the preceding bank timestamp, including across repeated writes to the same lane.
-/

namespace SP1Clean.TraceGen.CommitBanks

open Circuit Air.Flat Machine Semantics Soundness Soundness.Target FormalModel.Shard HostCommitChip

private abbrev F := ZMod SP1Prime
/-- A single chronological commitment update, before choosing its physical bank-lane table. -/
abbrev Entry := Fin 8 × Inputs F

/-- Encode every word of the current local bank at its last update time. -/
def stateAt (clock : ℕ) (values : Vector (BitVec 32) 8) : State F :=
  ⟨(clock / 2 ^ 24 : ℕ), (clock % 2 ^ 24 : ℕ), values.map (fun value => bitVecToWord (value.setWidth 64))⟩

/-- Populate a bank in one chronological pass. An out-of-range lane fails at its own call. -/
def rows? (deferred : Bool) (previous : ℕ) (values : Vector (BitVec 32) 8) : List CoreSyscallEvent → Option (List Entry)
  | [] => some []
  | call :: rest =>
    if valid : call.arg1.toNat < 8 then
      let slot : Fin 8 := ⟨_, valid⟩
      let row := populate deferred (message call) (stateAt previous values)
      (rows? deferred call.clock (bankUpdate values (call.arg1,call.arg2)) rest).map ((slot,row) :: ·)
    else none

private theorem arg2_field (c : CoreSyscallEvent) : (message c).arg2 = bitVecToWord c.arg2 := by
  change wordOfNat c.arg2.toNat = _
  apply Word.eq_of_toBitVec64_eq (wordOfNat_isU64 _) (isU64_bitVecToWord _)
  rw [toBitVec64_wordOfNat, toBitVec64_bitVecToWord, BitVec.ofNat_toNat]
  rfl

private theorem next_state (deferred : Bool) (prior : ℕ) (values : Vector (BitVec 32) 8) (c : CoreSyscallEvent)
    (slot : Fin 8) (index : slot.val = c.arg1.toNat) (spec : CallSpec deferred slot (message c))
    (high : (message c).clk_high = (c.clock / 2 ^ 24 : ℕ)) (low : (message c).clk_low = (c.clock % 2 ^ 24 : ℕ)) :
    (populate deferred (message c) (stateAt prior values)).next slot = stateAt c.clock (bankUpdate values (c.arg1,c.arg2)) := by
  have fits : c.arg2.toNat < 2 ^ 32 := by
    have bounded := spec.2.2.2.2
    rw [arg2_field, ← Word.toBitVec64_toNat (isU64_bitVecToWord _), toBitVec64_bitVecToWord] at bounded
    cases deferred
    · exact bounded
    · exact lt_of_lt_of_le bounded (Nat.min_le_right SP1Prime (2^32))
  have word : (c.arg2.setWidth 32).setWidth 64 = c.arg2 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt fits, Nat.mod_eq_of_lt c.arg2.isLt]
  have bound : c.arg1.toNat < 8 := index ▸ slot.isLt
  simp only [Inputs.next, populate, stateAt, high, low, bankUpdate, dite_eq_left bound, Vector.map_set, word, arg2_field]
  cases slot
  simp_all

private theorem state_bounded (clock : ℕ) (values : Vector (BitVec 32) 8) (fits : clock < 2 ^ 48) :
    HostCommitBoundary.TerminalSpec (stateAt clock values) := by
  have field := pow24_lt_sp1Prime
  change ((clock / 2^24 : ℕ) : F).val < 2^24 ∧ ((clock % 2^24 : ℕ) : F).val < 2^24
  rw [ZMod.val_natCast_of_lt (by omega : clock / 2^24 < SP1Prime), ZMod.val_natCast_of_lt (by omega : clock % 2^24 < SP1Prime)]
  omega

private def argument (c : CoreSyscallEvent) := (c.arg1,c.arg2)

/-- The ordered bank updates retain each checked circuit input and form an exact state chain.
The last bank is the semantic fold over the original arguments. -/
private theorem build_history (deferred : Bool) (calls : List CoreSyscallEvent) (previous : ℕ) (values : Vector (BitVec 32) 8)
    (initial : previous < 2^48) (lower : ∀ c ∈ calls, previous < c.clock)
    (sorted : calls.Pairwise (fun a b => a.clock < b.clock))
    (valid : ∀ c ∈ calls, ∃ slot : Fin 8, slot.val = c.arg1.toNat ∧ CallSpec deferred slot (message c) ∧
      0 < c.clock ∧ c.clock < 2^48 ∧ (message c).clk_high = (c.clock / 2^24 : ℕ) ∧ (message c).clk_low = (c.clock % 2^24 : ℕ)) :
    ∃ rows, rows? deferred previous values calls = some rows ∧
      (∀ row ∈ rows, ProverAssumptions deferred row.1 row.2) ∧
      rows.map (fun r => r.2.call) = calls.map message ∧
      let clock := calls.foldl (fun _ c => c.clock) previous
      let last := stateAt clock ((calls.map argument).foldl bankUpdate values)
      HostCommitBoundary.TerminalSpec last ∧
      stateAt previous values :: rows.map (fun r => r.2.next r.1) = rows.map (fun r => r.2.previous) ++ [last] := by
  induction calls generalizing previous values with
  | nil => exact ⟨[], rfl, by simp, rfl, state_bounded _ _ initial, rfl⟩
  | cons c rest ih =>
    obtain ⟨slot, index, spec, _, fits, high, low⟩ := valid c (by simp)
    let row := populate deferred (message c) (stateAt previous values)
    have enabled : c.arg1.toNat < 8 := index ▸ slot.isLt
    obtain ⟨after, ordered⟩ := List.pairwise_cons.mp sorted
    obtain ⟨rows, emitted, checked, messages, terminal, edges⟩ := ih c.clock (bankUpdate values (argument c)) fits after ordered
      (fun call mem => valid call (List.mem_cons_of_mem _ mem))
    have coordinate : (⟨c.arg1.toNat, enabled⟩ : Fin 8) = slot := Fin.ext index.symm
    have rowValid : ProverAssumptions deferred slot row := by
      apply populate_assumptions _ _ _ _ ⟨spec, ?_⟩
      rw [high, low]
      exact ClockOrder.encode_spec previous c.clock fits (lower c (by simp))
    refine ⟨(slot,row) :: rows, ?_, ?_, ?_, terminal, ?_⟩
    · simp only [rows?, dite_eq_left enabled, coordinate]
      simp only [argument] at emitted
      rw [emitted]
      rfl
    · intro entry member
      rcases List.mem_cons.mp member with rfl | seen
      · exact rowValid
      · exact checked _ seen
    · exact congrArg ((message c) :: ·) messages
    · apply congrArg (stateAt previous values :: ·)
      simp only [List.map_cons, List.foldl_cons]
      rw [show row.next slot = _ from next_state deferred previous values c slot index spec high low]
      exact edges

/-- Compile either bank from the local source to the real target, with no caller-supplied lane,
previous clock, row validity or final bank contents. -/
theorem of_execution {limits : ResourceLimits} {image : ProgramImage} {source target : ExecutionSnapshot}
    {events : List ExecutionEvent} (run : AdmissibleExecution limits SP1Prime image source target events) (deferred : Bool) :
    let selected := calls deferred events
    let clock := selected.foldl (fun _ c => c.clock) 0
    let last := stateAt clock (target.host.bank deferred)
    ∃ rows, rows? deferred 0 (source.host.bank deferred) selected = some rows ∧
      (∀ row ∈ rows, ProverAssumptions deferred row.1 row.2) ∧
      rows.map (fun row => row.2.call) = selected.map message ∧ HostCommitBoundary.TerminalSpec last ∧
      HostCommitBoundary.start (HostCommitEnsemble.sourceValues deferred source.host) :: rows.map (fun r => r.2.next r.1) =
        rows.map (fun row => row.2.previous) ++ [last] := by
  intro selected clock last
  have valid := fun c (mem : c ∈ selected) => call_valid run deferred mem
  have pos (c) (mem : c ∈ selected) : 0 < c.clock := (valid c mem).choose_spec.2.2.1
  obtain ⟨rows, emitted, checked, handoff, terminal, chain⟩ := build_history deferred selected 0 (source.host.bank deferred)
    (by decide) pos (ordered run.1.2 deferred).2 valid
  have endpoint := replayEvents?_bank run.1.2.replay deferred
  change ((events.filterMap (bankEvent? deferred)).foldl bankUpdate (source.host.bank deferred)) = target.host.bank deferred at endpoint
  have installed : (selected.map argument).foldl bankUpdate (source.host.bank deferred) = target.host.bank deferred := by
    rw [← endpoint, ← call_arguments]
    rfl
  rw [installed] at terminal chain
  exact ⟨rows, emitted, checked, handoff, terminal, chain⟩

end SP1Clean.TraceGen.CommitBanks
