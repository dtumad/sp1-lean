import SP1Clean.Soundness.ChipContracts
import SP1Clean.Soundness.SyscallGrounding

/-! # Ordinary row facts from incoming Memory currency

An ordinary row's step and frame facts need its `Spec`, whose route through
`Component.weakSoundness` consumes the row's Memory channel guarantees. Those guarantees are a
conclusion of grounding rather than an input to it. The walk's own step antecedent already hands
each row `isU64 ∧ ClkBound` for its pulls before asking for the step fact, so the guarantee is
rebuilt from that antecedent (`DecodedInstructionRow.memoryChannelGuarantees_of_pullCurrency`)
rather than from the walk's output. The operand bounds read currency only through
`localValueAt_stepStart_iff`, so they are stated over the shard's trajectory. -/

open LeanRV64D

namespace SP1Clean.Soundness

open SP1Clean.Machine
open SP1Clean.Semantics
open SP1Clean.Channels (StateMsg MemoryMsg memoryChannel byteChannel programChannel)
open Air.Flat
open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance syscallWiring_fact_24 : Fact (2 ^ 24 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance syscallWiring_fact_17 : Fact (2 ^ 17 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

theorem RowWiring.valueOperandsBound_of_pullCurrency
    {view : Trace.RowView (ZMod p)} {rf : Semantics.RowFacts p}
    (wiring : RowWiring view rf) {traj : Semantics.Trajectory} {initial state : SailState}
    {tl : Semantics.Timeline} {n : ℕ}
    (curr : ∀ mp ∈ rf.memPulls,
      Semantics.LocalValueAt traj initial tl (Semantics.MemoryMsg.locOf mp.1) mp.2 mp.1.value)
    (htraj : traj n = some state)
    (rowTime : StateMsg.timeNat rf.statePull = tl.start n) :
    Target.ValueOperandsBound view state := by
  constructor
  · intro index immediate indexEq
    obtain ⟨mp, hmp, location, value⟩ := wiring.opB_pull index immediate indexEq
    have current := curr mp hmp
    rw [location, value, wiring.readTime mp hmp, rowTime] at current
    exact (TimedGrounding.localValueAt_stepStart_iff htraj).mp current
  · intro index immediate indexEq
    obtain ⟨mp, hmp, location, value⟩ := wiring.opC_pull index immediate indexEq
    have current := curr mp hmp
    rw [location, value, wiring.readTime mp hmp, rowTime] at current
    exact (TimedGrounding.localValueAt_stepStart_iff htraj).mp current

theorem RowWiring.sourceAValueBound_of_pullCurrency
    {view : Trace.RowView (ZMod p)} {rf : Semantics.RowFacts p}
    (wiring : RowWiring view rf) {traj : Semantics.Trajectory} {initial state : SailState}
    {tl : Semantics.Timeline} {n : ℕ}
    (curr : ∀ mp ∈ rf.memPulls,
      Semantics.LocalValueAt traj initial tl (Semantics.MemoryMsg.locOf mp.1) mp.2 mp.1.value)
    (htraj : traj n = some state)
    (rowTime : StateMsg.timeNat rf.statePull = tl.start n) :
    Target.SourceAValueBound view state := by
  intro index indexEq
  obtain ⟨mp, hmp, location, value⟩ := wiring.opA_pull index indexEq
  have current := curr mp hmp
  rw [location, value, wiring.readTime mp hmp, rowTime] at current
  exact (TimedGrounding.localValueAt_stepStart_iff htraj).mp current

theorem RowWiring.memoryPullsBound_of_pullCurrency
    {view : Trace.RowView (ZMod p)} {rf : Semantics.RowFacts p}
    (wiring : RowWiring view rf) {traj : Semantics.Trajectory} {initial state : SailState}
    {tl : Semantics.Timeline} {n : ℕ}
    (curr : ∀ mp ∈ rf.memPulls,
      Semantics.LocalValueAt traj initial tl (Semantics.MemoryMsg.locOf mp.1) mp.2 mp.1.value)
    (htraj : traj n = some state)
    (rowTime : StateMsg.timeNat rf.statePull = tl.start n) :
    MemoryPullsBound rf state := by
  intro mp hmp
  have current := curr mp hmp
  rw [wiring.readTime mp hmp, rowTime] at current
  exact (TimedGrounding.localValueAt_stepStart_iff htraj).mp current

/-- Component-local ordinary execution facts on any trajectory whose successor at this row is
Sail's `stepOnce`. Wiring, chip semantics, and readiness are derived inside incoming Memory
currency; the enclosing assembly supplies only physical evidence, decode, and timeline position. -/
theorem ChipGroundingContracts.engineFactsLocal_of_rowEffect
    {chip : SupportedChip p} (contracts : ChipGroundingContracts chip)
    (proverData : ProverData (ZMod p))
    (decoded : DecodedInstructionRow p) (hchip : decoded.chip = chip)
    (staticInputs : DecodedRowStaticInputs decoded proverData)
    (real : (decoded.toChipRow proverData).is_real = 1)
    (program : Target.GuestProgram)
    (decode : Target.decodedInROM program
      (programAccess (decoded.toChipRow proverData).view).toRow)
    (trajectory : Semantics.Trajectory) (initial : SailState) (tl : Semantics.Timeline)
    (codeMemoryCompatible : ∀ {m : ℕ} {st nx : SailState},
      trajectory m = some st →
        Target.RowEffect program (decoded.toChipRow proverData).view st nx →
          Target.RomLoaded program st → Target.RomLoaded program nx)
    (timeStep : ∀ n, StateMsg.timeNat (decoded.ordinaryRowFacts proverData).statePull = tl.start n →
      tl.start (n + 1) = tl.start n + 8)
    (step : Semantics.LocalStateTruth program trajectory tl
        (decoded.ordinaryRowFacts proverData).statePull →
      ∀ n, StateMsg.timeNat (decoded.ordinaryRowFacts proverData).statePull = tl.start n →
      trajectory (n + 1) = (trajectory n).bind Machine.stepOnce) :
    Semantics.LocalStepFact program
        trajectory initial
        tl (decoded.ordinaryRowFacts proverData) ∧
      Semantics.FrameFact program
        trajectory initial
        tl (decoded.ordinaryRowFacts proverData) := by
  have guard := contracts.routingLocal proverData decoded hchip staticInputs.constraints real program decode
  have migrated : (decoded.toChipRow proverData).kind.advance.isSome = true := by
    show decoded.chip.kind.advance.isSome = true
    rw [hchip]
    exact contracts.migrated
  -- The D0 circularity break, unchanged: the row's open Memory inputs come from the *assumed* pull
  -- currency, never from the walk's own `Grounded` output.
  have mkOpenInputs : (∀ mp ∈ (decoded.ordinaryRowFacts proverData).memPulls,
        MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 ∧
        Semantics.LocalValueAt trajectory initial
          tl
          (Semantics.MemoryMsg.locOf mp.1) mp.2 mp.1.value) →
      DecodedRowOpenSoundnessInputs decoded proverData := fun hcurr => by
    let memory := decoded.memoryChannelGuarantees_of_pullCurrency proverData
      (fun mp hmp => ⟨(hcurr mp hmp).1, (hcurr mp hmp).2.1⟩)
    exact
      { assumptions := contracts.assumptionsLocal proverData decoded hchip staticInputs
          real program decode memory
        memory }
  have advance := ChipKind.advancePayload_of_migrated migrated
  refine ⟨?_, ?_⟩
  · intro hpull hcurr
    have inputs := mkOpenInputs hcurr
    exact ordinaryStepFact_of_rowEffect
      (contracts.wiringLocal proverData decoded hchip staticInputs real program decode inputs)
      advance real (staticInputs.chipSpec inputs) decode
      (contracts.readinessLocal proverData decoded hchip staticInputs real guard program decode inputs)
      trajectory initial tl codeMemoryCompatible timeStep (step hpull) hpull hcurr
  · intro hpull hcurr loc value pushes current
    have inputs := mkOpenInputs hcurr
    exact ordinaryFrameFact_of_advanceOnTrajectory
      (contracts.wiringLocal proverData decoded hchip staticInputs real program decode inputs)
      advance real (staticInputs.chipSpec inputs) decode
      (contracts.readinessLocal proverData decoded hchip staticInputs real guard program decode inputs)
      trajectory initial tl timeStep (step hpull) hpull hcurr loc value pushes current

end SP1Clean.Soundness
