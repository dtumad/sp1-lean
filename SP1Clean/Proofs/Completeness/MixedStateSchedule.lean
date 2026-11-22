import SP1Clean.Proofs.Completeness.StateInventory
import SP1Clean.Proofs.Completeness.ExecutionObservationSuccessor
import SP1Clean.Semantics.Execution.ParkedSyscall

/-! # Raw and normalized State messages along mixed execution

The instruction posts its native clock and PC limbs before carrying. StateBump converts those
same coordinates to the public split, including simultaneous crossings at a syscall.
-/

namespace SP1Clean.TraceGen
open Machine Semantics FormalModel.Shard Soundness.Target

namespace StateRecord

/-- The full clock denoted by the physical high and low fields, even before a carry. -/
def clockValue (r : StateRecord) : ℕ := r.clkHigh * 2 ^ 24 + r.clkLow

/-- The PC denoted by all three physical limbs, including a raw fall-through addition. -/
def pcValue (r : StateRecord) : ℕ := r.pc0 + r.pc1 * 2 ^ 16 + r.pc2 * 2 ^ 32

/-- A StateBump row produces precisely the canonical coordinates of the raw row it consumed. -/
theorem normalize_eq_canonical (r : StateRecord) (valid : r.toBumpEvent.WellFormed) :
    r.normalize = canonical r.clockValue r.pcValue := by
  let e := r.toBumpEvent
  have ranges := StateBumpEvent.next_bounds valid
  have relation := StateBumpEvent.pc_cascade (e := e) valid
  have time : e.nextClkHigh * 2^24 + e.nextClkLow = e.clkHigh * 2^24 + e.clkLow := by
    have low := valid.clkLow
    change e.clkLow < 2 ^ 25 at low
    simp only [StateBumpEvent.nextClkLow, StateBumpEvent.nextClkHigh, StateBumpEvent.isClk]
    split <;> omega
  have addr : e.nextPc0 + e.nextPc1 * 2^16 + e.nextPc2 * 2^32 =
      e.pc0 + e.pc1 * 2^16 + e.pc2 * 2^32 := by omega
  change e.nextClkLow < _ ∧ e.nextClkHigh < _ ∧ e.nextPc0 < _ ∧ e.nextPc1 < _ ∧ e.nextPc2 < _ at ranges
  change _ = canonical (e.clkHigh * 2^24 + e.clkLow) (e.pc0 + e.pc1 * 2^16 + e.pc2 * 2^32)
  rw [← time, ← addr]
  unfold normalize canonical
  change StateRecord.mk e.nextClkHigh e.nextClkLow e.nextPc0 e.nextPc1 e.nextPc2 = _
  congr 1 <;> omega

/-- Every fall-through row with a representable successor has an honest optional StateBump.
The row can carry its low clock, either of its low PC limbs, or both kinds at once. -/
theorem fallThrough_valid {clock pc duration : ℕ} (step : duration ≤ 2 ^ 24)
    (phase : (clock + duration) % 8 = 1) (time : clock + duration < 2 ^ 48)
    (destination : pc + 4 < 2 ^ 48) :
    (fallThrough clock pc duration).toBumpEvent.WellFormed ∧
    (fallThrough clock pc duration).normalize = canonical (clock + duration) (pc + 4) := by
  let raw := fallThrough clock pc duration
  have clockEq : raw.clockValue = clock + duration := by unfold raw clockValue fallThrough canonical; dsimp; omega
  have pcEq : raw.pcValue = pc + 4 := by unfold raw pcValue fallThrough canonical; dsimp; omega
  have valid : raw.toBumpEvent.WellFormed := by
    apply StateBumpEvent.wellFormed_iff.mpr
    refine ⟨?_, ?_, clockEq.trans_lt time, ?_, ?_, pcEq.trans_lt destination⟩
    all_goals dsimp [raw, fallThrough, canonical, toBumpEvent, StateBumpEvent.b0]
    all_goals first | omega | (split <;> omega)
  exact ⟨valid, (normalize_eq_canonical raw valid).trans (congrArg₂ canonical clockEq pcEq)⟩

/-- A row with a selected destination preserves its three canonical PC limbs while carrying the clock. -/
theorem selected_valid {clock pc duration : ℕ} (step : duration ≤ 2 ^ 24)
    (phase : (clock + duration) % 8 = 1) (time : clock + duration < 2 ^ 48) (destination : pc < 2 ^ 48) :
    (selected clock pc duration).toBumpEvent.WellFormed ∧
    (selected clock pc duration).normalize = canonical (clock + duration) pc := by
  let raw := selected clock pc duration
  have clockEq : raw.clockValue = clock + duration := by unfold raw clockValue selected canonical; dsimp; omega
  have pcEq : raw.pcValue = pc := by unfold raw pcValue selected canonical; dsimp; omega
  have valid : raw.toBumpEvent.WellFormed := by
    apply StateBumpEvent.wellFormed_iff.mpr
    refine ⟨?_, ?_, clockEq.trans_lt time, ?_, ?_, pcEq.trans_lt destination⟩
    all_goals dsimp [raw, selected, canonical, toBumpEvent, StateBumpEvent.b0]
    all_goals first | omega | (split <;> omega)
  exact ⟨valid, (normalize_eq_canonical raw valid).trans (congrArg₂ canonical clockEq pcEq)⟩

end StateRecord

/-- The exact State edge emitted by an ECALL. HALT parks at one and every continuing call
increments the low PC limb by four, with an uncarried 264-tick low clock in either case. -/
def syscallPushedState (call : CoreSyscallEvent) : StateRecord :=
  if call.syscallId = haltSyscallId then StateRecord.selected call.clock haltPc.toNat 264
  else StateRecord.fallThrough call.clock call.pc.toNat 264

/-- The physical successor normalizes to the event's actual next clock and PC. -/
theorem syscallPushedState_valid {call : CoreSyscallEvent} (pcLaw : call.PcLaw)
    (source : call.pc.toNat < 2 ^ 48) (destination : call.nextPc.toNat < 2 ^ 48)
    (phase : call.clock % 8 = 1) (time : call.clock + 264 < 2 ^ 48) :
    (syscallPushedState call).toBumpEvent.WellFormed ∧
      (syscallPushedState call).normalize = StateRecord.canonical (call.clock + 264) call.nextPc.toNat := by
  unfold CoreSyscallEvent.PcLaw at pcLaw
  unfold syscallPushedState
  split <;> rename_i choice
  · rw [ite_eq_left choice] at pcLaw
    rw [pcLaw]
    exact StateRecord.selected_valid (by decide) (by omega) time (by decide)
  · rw [ite_eq_right choice] at pcLaw
    have natural : call.nextPc.toNat = call.pc.toNat + 4 := by
      rw [pcLaw, BitVec.toNat_add]
      change (call.pc.toNat + 4) % 2 ^ 64 = _
      exact Nat.mod_eq_of_lt (by omega)
    rw [natural] at destination ⊢
    exact StateRecord.fallThrough_valid (by decide) (by omega) time destination

/-- At every actual host cut the execution supplies the phase, width and selected destination
for the same raw State message and the resulting StateBump construction. -/
theorem admissibleExecution_syscallPushedState {limits : ResourceLimits} {p : ℕ}
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events)
    {cut : ℕ} {call : CoreSyscallEvent} (active : events[cut]? = some (.syscall call)) :
    (syscallPushedState call).toBumpEvent.WellFormed ∧
      (syscallPushedState call).normalize = StateRecord.canonical (call.clock + 264) call.nextPc.toNat := by
  obtain ⟨current, next, before, step⟩ := execution.1.2.step_at active
  have after : executionTrajectory (policy p image) image.program source.realize events (cut + 1) = some next := by
    rw [executionTrajectory_succ _ _ _ _ active, before, Option.bind_some, step.replay]
  have phase := (execution.2.1 cut _ _ active before).1
  have time := (execution.1.2.clock_at active before).trans_lt execution.2.2.2.2.2.1
  cases step with
  | syscall ran =>
    obtain ⟨pc, exec, atPc, _, dispatched, _, rfl, rfl⟩ := HostState.step_observations ran
    have law := exec.rowLaw ((current.host.run_eq_some_iff ..).mp dispatched).2.2.2.2.1 current.clock pc
    have registers := exec.matchesStates dispatched atPc current.clock
    exact syscallPushedState_valid law.2.2.1 (Executes.pc_at execution before registers.1)
      (Executes.pc_at execution after registers.2.2.2.2.1) phase time


private theorem ordinary_limbs (r : RoutedEvent) :
    r.rawPushState.clkHigh = r.clock / 2 ^ 24 ∧ r.rawPushState.clkLow = r.clock % 2 ^ 24 + 8 ∧
      r.rawPushState.pc0 < 2 ^ 16 + 4 ∧ r.rawPushState.pc1 < 2 ^ 16 ∧ r.rawPushState.pc2 < 2 ^ 16 := by
  rcases r with ⟨id, event⟩
  cases id <;> simp only [RoutedEvent.rawPushState, RoutedEvent.clock, StateRecord.fallThrough,
    StateRecord.selected, StateRecord.canonical, true_and] <;> omega

private theorem ordinary_decode {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)] (r : RoutedEvent) :
    StateMsg.pcBits (r.rawPushState.toMessage (p := p)) = BitVec.ofNat 64 r.rawPushState.pcValue := by
  obtain ⟨_, _, low, mid, high⟩ := ordinary_limbs r
  have hp := Fact.out (p := 2 ^ 25 < p)
  dsimp only [StateRecord.toMessage, StateMsg.pcBits, pcBits, StateRecord.pcValue]
  rw [ZMod.val_natCast_of_lt (by omega : r.rawPushState.pc0 < p),
      ZMod.val_natCast_of_lt (by omega : r.rawPushState.pc1 < p),
      ZMod.val_natCast_of_lt (by omega : r.rawPushState.pc2 < p)]

private theorem ordinary_raw_valid (row : RoutedEvent) (phase : row.clock % 8 = 1)
    (time : row.clock + 8 < 2 ^ 48) (dest : row.rawPushState.pcValue < 2 ^ 48) :
    row.rawPushState.toBumpEvent.WellFormed ∧
      row.rawPushState.normalize = StateRecord.canonical (row.clock + 8) row.rawPushState.pcValue := by
  obtain ⟨ch, cl, low, mid, _⟩ := ordinary_limbs row
  have encoded : row.rawPushState.clockValue = row.clock + 8 := by
    unfold StateRecord.clockValue
    rw [ch, cl]
    omega
  have valid : row.rawPushState.toBumpEvent.WellFormed := by
    apply StateBumpEvent.wellFormed_iff.mpr
    refine ⟨?_, ?_, encoded.trans_lt time, low.trans_le (by decide), ?_, dest⟩
    · change row.rawPushState.clkLow % 8 = 1
      rw [cl]
      omega
    · change row.rawPushState.clkLow < 2 ^ 25
      rw [cl]
      omega
    · change row.rawPushState.pc1 + (if 2^16 ≤ row.rawPushState.pc0 then 1 else 0) < 2^17
      split <;> omega
  exact ⟨valid, (StateRecord.normalize_eq_canonical row.rawPushState valid).trans
      (congrArg (fun n => StateRecord.canonical n row.rawPushState.pcValue) encoded)⟩

private theorem ordinary_pcValue {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)] (row : RoutedEvent) :
    (StateMsg.pcBits (row.rawPushState.toMessage (p := p))).toNat = row.rawPushState.pcValue := by
  obtain ⟨_, _, low, mid, high⟩ := ordinary_limbs row
  rw [ordinary_decode, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  unfold StateRecord.pcValue
  omega

/-- Every ordinary producer, including a taken branch or a discarded jump link, supplies
a raw State edge that normalizes to the actual next complete state. -/
theorem admissibleExecution_ordinaryPushedState {limits : ResourceLimits} {p : ℕ}
    [Fact p.Prime] [Fact (2 ^ 25 < p)]
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events) {rows : List RoutedEvent}
    (routed : routeObservations? (policy p image) image.program AccessFrontier.initial source.realize events = some rows)
    {cut : ℕ} (active : events[cut]? = some .ordinary) :
    ∃ row next pc, rows[(events.take cut).countP ExecutionEvent.isOrdinary]? = some row ∧
      executionTrajectory (policy p image) image.program source.realize events (cut + 1) = some next ∧
      next.sail.regs.get? LeanRV64D.Register.PC = some pc ∧ row.rawPushState.toBumpEvent.WellFormed ∧
      row.rawPushState.normalize = StateRecord.canonical next.clock pc.toNat := by
  obtain ⟨row, next, atRow, after, nextPC, _⟩ := routed_successor_at execution routed active
  obtain ⟨current, produced, _, result, _, _, before, ran, _, made, same⟩ := routeObservations?_at routed active
  have rowEq := Option.some.inj (same.symm.trans atRow)
  have clk := (compileInstructionEvent?_coordinates made).1
  rw [rowEq] at clk
  have phase : current.clock % 8 = 1 := (execution.2.1 cut _ _ active before).1
  have finalClock : current.clock + 8 < 2 ^ 48 := (execution.1.2.clock_at active before).trans_lt execution.2.2.2.2.2.1
  have reached : executionTrajectory (policy p image) image.program source.realize events (cut+1) = some produced := by
    rw [executionTrajectory_succ _ _ _ _ active, before, Option.bind_some, ran]
  have clock : next.clock = row.clock + 8 :=
    (congrArg ExecutionState.clock (Option.some.inj (after.symm.trans reached))).trans
      ((replayStep?_clock ran).trans (congrArg (· + 8) clk.symm))
  have pcValue := ordinary_pcValue (p := p) row
  have fits := Executes.pc_at execution after nextPC
  have raw := ordinary_raw_valid row (clk ▸ phase) (clk ▸ finalClock) (pcValue ▸ fits)
  exact ⟨row, next, _, atRow, after, nextPC, raw.1,
    raw.2.trans (congrArg₂ StateRecord.canonical clock.symm pcValue.symm)⟩

end SP1Clean.TraceGen
