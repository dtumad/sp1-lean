import SP1Clean.Soundness.ChipContracts
import SP1Clean.Soundness.SyscallGrounding
import SP1Clean.Soundness.SyscallInputs

/-! # Wiring a syscall row into the walk

`syscallStepFact_of_advance` needs the row's `Spec`, its `SelectorsValid`, its `PulledFacts` and its
`SyscallRowContext` *before* the walk runs. All four are reachable from the ensemble — but the route
to `Spec` runs through `Component.weakSoundness`, which consumes the row's **Memory** channel
guarantees, and those are a conclusion of grounding rather than an input to it.

That is the same currency circularity the ordinary rows hit, and it has the same resolution: the
walk's own step antecedent already hands each row `isU64 ∧ ClkBound` for its pulls before asking for
the step fact, so the guarantee can be rebuilt from the antecedent rather than from the walk's
output. `DecodedInstructionRow.memoryChannelGuarantees_of_pullCurrency` is the instruction-row
version. `SyscallInputs` provides the component-local syscall implementation; this file keeps
the legacy assembly specializations. The mixed native carrier derives HALT separately through
`HaltGrounding`. -/

open LeanRV64D

namespace SP1Clean.Soundness

open SP1Clean.Machine
open SP1Clean.Semantics
open SP1Clean.Channels (StateMsg MemoryMsg memoryChannel byteChannel programChannel)
open Air.Flat
open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

-- Named rather than anonymous: `SyscallTrail` already declares an anonymous `Fact (2 ^ 17 < p)`
-- instance in this namespace, and `local` scopes the *use* but not the generated declaration name.
local instance syscallWiring_fact_24 : Fact (2 ^ 24 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance syscallWiring_fact_17 : Fact (2 ^ 17 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- **The circularity break at a syscall row.** The row's three pulled priors carry `isU64 ∧
ClkBound` in the walk's currency antecedent; that is exactly the memory channel's `Guarantees`, so
the row's own Memory `ChannelGuarantees` follows without any appeal to the walk's output.

The three *pushes* need nothing: `consumedMessages` keeps only the pull-polarity interactions, and a
boolean gate can never make a push's `signedVal` negative. -/
theorem syscallInstrsRow_memoryGuarantees_of_pullCurrency
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (constraints : witness.Constraints)
    {row : Array (ZMod p)} (rowMem : row ∈ (syscallInstrsTable witness).table)
    (currency : ∀ mp ∈
        (syscallRowFacts (syscallInstrsRow witness.data row)).memPulls,
      MemoryMsg.isU64 (mp : MemoryMsg (ZMod p) × ℕ).1 ∧ MemoryMsg.ClkBound mp.1) :
    (syscallInstrsTable witness).component.operations.ChannelGuarantees memoryChannel.toRaw
      (Environment.fromArray row witness.data) :=
  syscallInstrsRow_memoryGuarantees_of_component _ witness.data (syscallInstrsTable_component witness)
    (constraints _ (List.getElem_mem (syscallInstrsIndex_lt_tablesLength witness))) rowMem currency

/-- **A syscall row's `Spec`, from the walk's currency rather than from grounding.** This is the
statement `SyscallRowWiring` is built on: everything the row's meaning needs is either a finished
channel (Byte, Program) or the antecedent the walk supplies anyway. -/
theorem syscallInstrsRow_spec_of_pullCurrency
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (constraints : witness.Constraints)
    (balanced : witness.BalancedChannels)
    {row : Array (ZMod p)} (rowMem : row ∈ (syscallInstrsTable witness).table)
    (currency : ∀ mp ∈
        (syscallRowFacts (syscallInstrsRow witness.data row)).memPulls,
      MemoryMsg.isU64 (mp : MemoryMsg (ZMod p) × ℕ).1 ∧ MemoryMsg.ClkBound mp.1) :
    SyscallInstrsChip.Spec (syscallInstrsRow witness.data row) := by
  have member := List.getElem_mem (syscallInstrsIndex_lt_tablesLength witness)
  have finished := (sp1_finishedChannel_guarantees witness constraints balanced).2 _ member
  exact (syscallInstrsRow_contract_of_component _ witness.data (syscallInstrsTable_component witness)
    (syscallInstrsTable_data witness)
    (constraints _ member) finished.1 finished.2 rowMem currency).1

/-- **The row's committed `ECALL` fetch satisfies the Program bus's `RowSpec`.** The Program channel
is finished, so the row's single gated pull carries its guarantee outright — the same route
`decodedInstructionRow_programRowSpec` takes for an instruction row. -/
theorem syscallInstrsRow_programRowSpec
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (constraints : witness.Constraints)
    (balanced : witness.BalancedChannels)
    {row : Array (ZMod p)} (rowMem : row ∈ (syscallInstrsTable witness).table)
    (real : (syscallInstrsRow witness.data row).is_real = 1) :
    Channels.ProgramMsg.RowSpec (SyscallInstrsChip.programMessage (syscallInstrsRow witness.data row)) :=
  syscallInstrsRow_programRowSpec_of_component _ witness.data (syscallInstrsTable_component witness)
    (syscallInstrsTable_data witness)
    ((sp1_finishedChannel_guarantees witness constraints balanced).2 _
      (List.getElem_mem (syscallInstrsIndex_lt_tablesLength witness))).2 rowMem real

/-- **The row's `PulledFacts`, assembled from the three buses.** Nothing here is row-local: the
first five conjuncts are the Program bus's `RowSpec` at the committed `ECALL`, the next six are the
walk's own currency at the three register pulls, and the last — the written `t0` word's
`Word.isU64` — is the byte bus's four `Range 16` checks, because no arm of the `Spec` constrains it
(`HINT_LEN` deliberately leaves the result free). -/
theorem syscallInstrsRow_pulledFacts
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (constraints : witness.Constraints)
    (balanced : witness.BalancedChannels)
    {row : Array (ZMod p)} (rowMem : row ∈ (syscallInstrsTable witness).table)
    (currency : ∀ mp ∈ (syscallRowFacts (syscallInstrsRow witness.data row)).memPulls,
      MemoryMsg.isU64 (mp : MemoryMsg (ZMod p) × ℕ).1 ∧ MemoryMsg.ClkBound mp.1) :
    SyscallInstrsChip.PulledFacts (syscallInstrsRow witness.data row) := by
  have member := List.getElem_mem (syscallInstrsIndex_lt_tablesLength witness)
  have finished := (sp1_finishedChannel_guarantees witness constraints balanced).2 _ member
  exact (syscallInstrsRow_contract_of_component _ witness.data (syscallInstrsTable_component witness)
    (syscallInstrsTable_data witness)
    (constraints _ member) finished.1 finished.2 rowMem currency).2

/-! ## The dynamic row consumer

The row consumer reads currency only through `localValueAt_stepStart_iff`, so it is stated over
the shard's trajectory. -/

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

/-- Preserve the public trajectory-wide contract as a specialization of the row-effect interface. -/
theorem ChipGroundingContracts.engineFactsLocal_of_stateStep
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
        Target.SailStep st nx → Target.RomLoaded program st → Target.RomLoaded program nx)
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
  exact contracts.engineFactsLocal_of_rowEffect proverData decoded hchip staticInputs real program decode
    trajectory initial tl (fun present effect => codeMemoryCompatible present effect.normal.sailStep)
    timeStep step

/-- The unguarded successor interface remains a specialization of incoming-state replay. -/
theorem ChipGroundingContracts.engineFactsLocal
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
        Target.SailStep st nx → Target.RomLoaded program st → Target.RomLoaded program nx)
    (timeStep : ∀ n, StateMsg.timeNat (decoded.ordinaryRowFacts proverData).statePull = tl.start n →
      tl.start (n + 1) = tl.start n + 8)
    (step : ∀ n, StateMsg.timeNat (decoded.ordinaryRowFacts proverData).statePull = tl.start n →
      trajectory (n + 1) = (trajectory n).bind Machine.stepOnce) :
    Semantics.LocalStepFact program
        trajectory initial
        tl (decoded.ordinaryRowFacts proverData) ∧
      Semantics.FrameFact program
        trajectory initial
        tl (decoded.ordinaryRowFacts proverData) := by
  exact contracts.engineFactsLocal_of_stateStep proverData decoded hchip staticInputs real program decode
    trajectory initial tl codeMemoryCompatible timeStep (fun _ => step)

/-! ## The canonicity premise, at the native witness

D9's condition lives on the supported profile (`Model.Core.Profile.CanonicalSyscallCodes`) because it is a
fact about SP1's *executor*, not about its AIR: the AIR reads bytes 0 and 1 of `x5`, while
`SyscallCode::from_u32` dispatches on the full word and panics on a non-enumerated value. An
AIR-valid `HALT` row may therefore carry `x5 = 0x00010000`, which no execution produces.

The native side's projection into that predicate is below. It is what a caller must supply for a
syscall row's step fact, which takes `IsInlineCanonical` and cannot derive it — and the reason
`SyscallTableInactive.noActiveRows` cannot simply be dropped: without active syscall rows the
condition is vacuous, and with them it is a genuine, disclosed obligation. -/

/-- The decoded events of a witness's active syscall rows — the native side's projection into
`Model.Core.Profile.CanonicalSyscallCodes`. -/
noncomputable def syscallEventsOf (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    List Machine.CoreSyscallEvent :=
  (realSyscallInstrsRows witness).map fun row => syscallEventOfRow (syscallInstrsRow witness.data row)

/-- Reading the profile condition back at one active row — the form
`syscallStepFact_of_advance` consumes. -/
theorem isInlineCanonical_of_profile
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (canonical : SP1Clean.Model.Core.Profile.CanonicalSyscallCodes (syscallEventsOf witness))
    {row : Array (ZMod p)} (rowMem : row ∈ realSyscallInstrsRows witness) :
    (syscallEventOfRow (syscallInstrsRow witness.data row)).IsInlineCanonical :=
  canonical _ (List.mem_map_of_mem rowMem)

end SP1Clean.Soundness
