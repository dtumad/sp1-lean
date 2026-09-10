import SP1Clean.Soundness.NativeCoreOrder
import SP1Clean.Soundness.NativeCoreRowBalance
import SP1Clean.Soundness.SystemTouches
import SP1Clean.Soundness.ChipContracts
import SP1Clean.Soundness.FetchDiscriminant

/-! # Aligned touches of the authenticated native core

The checked image fixes register operands; the closed Byte channel fixes access windows and
timestamp differences. Every mixed execution row therefore admits paired Memory touches without
changing its State edge, fetch, or complete Memory multiset. Prior-record timestamp bounds remain
conditional here: deriving them and eliminating the actual refresh rows is the next grounding step.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Local touch alignment, with the prior-clock conditions explicitly retained for grounding. -/
structure AlignedFacts (aligned original : RowFacts p) : Prop where
  statePull : aligned.statePull = original.statePull
  statePush : aligned.statePush = original.statePush
  fetch : aligned.fetch = original.fetch
  memory : RowMemoryPermutation aligned original
  touches : List.Forall₂ (TouchOK (StateMsg.timeNat aligned.statePull)) aligned.memPulls aligned.memPushes
  chain : ∀ loc, List.IsChain (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
    (rowTouchesAt aligned loc)
  pushBound : ∀ message ∈ aligned.memPushes, MemoryMsg.ClkBound message
  slot : ∀ touch ∈ aligned.memPulls.zip aligned.memPushes,
    MemoryMsg.ClkBound touch.1.1 → touch.1.1.clk_high.val < 2 ^ 24 →
      MemoryMsg.timeNat touch.1.1 < MemoryMsg.timeNat touch.2

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
/-- Once Memory balance supplies the prior high-clock bounds, the alignment is the timed
engine's complete local core. The remaining low-clock premise is the engine's own received fact. -/
theorem AlignedFacts.rowOKCore {aligned original : RowFacts p} (facts : AlignedFacts aligned original)
    (initialClock : ℕ)
    (gap : StateMsg.timeNat original.statePull + 8 ≤ StateMsg.timeNat original.statePush)
    (align : StateMsg.timeNat original.statePull % 8 = initialClock % 8)
    (priorHigh : ∀ touch ∈ aligned.memPulls.zip aligned.memPushes, touch.1.1.clk_high.val < 2 ^ 24) :
    RowOKCore initialClock aligned where
  timeGap := by rw [facts.statePull, facts.statePush]; exact gap
  align8 := by rw [facts.statePull]; exact align
  touches := facts.touches
  chain_mono := facts.chain
  pushClkBound := facts.pushBound
  slotOfClkBound := fun touch member bound => facts.slot touch member bound (priorHigh touch member)

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
private theorem alignedFacts_of_touches (original : RowFacts p) (touches : List (Touch p))
    (projection : RowMemoryPermutation (alignedOf original touches) original)
    (localOK : ∀ touch ∈ touches, TouchOK (StateMsg.timeNat original.statePull) touch.1 touch.2)
    (chain : ∀ loc, List.IsChain (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
      (touches.filter (fun touch => MemoryMsg.locOf touch.2 = loc)))
    (pushBound : ∀ touch ∈ touches, MemoryMsg.ClkBound touch.2)
    (slot : ∀ touch ∈ touches, MemoryMsg.ClkBound touch.1.1 → touch.1.1.clk_high.val < 2 ^ 24 →
      MemoryMsg.timeNat touch.1.1 < MemoryMsg.timeNat touch.2) :
    AlignedFacts (alignedOf original touches) original where
  statePull := rfl
  statePush := rfl
  fetch := rfl
  memory := projection
  touches := List.forall₂_map_left_iff.mpr
    (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr localOK))
  chain := by intro loc; rw [rowTouchesAt_alignedOf]; exact chain loc
  pushBound := by
    intro message member
    obtain ⟨touch, touchMem, rfl⟩ := List.mem_map.mp member
    exact pushBound touch touchMem
  slot := by
    have zipped : (touches.map Prod.fst).zip (touches.map Prod.snd) = touches := by
      simp [List.zip_map']
    change ∀ touch ∈ (touches.map Prod.fst).zip (touches.map Prod.snd), _
    rw [zipped]
    exact slot

private theorem syscall_operands_of_committed (row : SyscallInstrsChip.Inputs (ZMod p)) (program : Target.GuestProgram)
    (committed : Target.committedInROM program (rowOfMsg (SyscallInstrsChip.programMessage row))) :
    row.op_a = 5 ∧ row.op_b = 10 ∧ row.op_c = 11 := by
  have shape := (committed.ecall_of_opcode rfl).2
  exact ⟨congrArg (fun r : ProgramChip.ProgramRow (ZMod p) => r.op_a) shape,
    congrArg (fun r : ProgramChip.ProgramRow (ZMod p) => r.op_b[0]) shape,
    congrArg (fun r : ProgramChip.ProgramRow (ZMod p) => r.op_c[0]) shape⟩

/-- Every active physical syscall fetch belongs to the checked image. -/
theorem syscall_program_committed {image : ProgramImage} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {physical : Array (ZMod p)} (member : physical ∈ (systemTable witness 3).table)
    (real : (syscallInstrsRow (systemTable witness 3) physical).is_real = 1) :
    Target.committedInROM (image.toGuestProgram valid)
      (rowOfMsg (SyscallInstrsChip.programMessage (syscallInstrsRow (systemTable witness 3) physical))) := by
  let row := syscallInstrsRow (systemTable witness 3) physical
  let message := SyscallInstrsChip.programMessage row
  let interaction := programChannel.pulledIfValue row.is_real message
  have emitted : interaction ∈ witness.interactionsWith programChannel.toRaw := by
    apply EnsembleWitness.mem_interactionsWith.mpr
    refine ⟨systemTable witness 3, systemTable_mem witness 3, List.mem_flatMap.mpr ⟨physical, member, ?_⟩⟩
    rw [← typedInteractionValuesWith_raw,
      syscallInstrsRow_typedProgram_of_component _ (systemTable_component witness 3)]
    exact List.mem_cons_self
  exact program_pull_committed valid witness constraints balanced message interaction emitted
    (by change -row.is_real = -1; rw [real]) rfl

private theorem syscall_operands {image : ProgramImage} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {physical : Array (ZMod p)} (member : physical ∈ (systemTable witness 3).table)
    (real : (syscallInstrsRow (systemTable witness 3) physical).is_real = 1) :
    (syscallInstrsRow (systemTable witness 3) physical).op_a = 5 ∧
      (syscallInstrsRow (systemTable witness 3) physical).op_b = 10 ∧
      (syscallInstrsRow (systemTable witness 3) physical).op_c = 11 :=
  syscall_operands_of_committed _ _ (syscall_program_committed valid witness constraints balanced member real)

private theorem halt_aligned (row : HaltChip.Inputs (ZMod p))
    (clock : ((row.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧ row.state.clk_16_24.val < 2 ^ 8)
    (timestamps : SystemTouches.TimestampBounds row.state row.x5_memory row.x10_memory row.x11_memory) :
    ∃ aligned, AlignedFacts aligned (haltRowFacts row) := by
  let touches := SystemTouches.touches row.state row.x5_memory row.x10_memory row.x11_memory row.x5_memory.prev_value
  have facts := SystemTouches.touches_spec row.state row.x5_memory row.x10_memory row.x11_memory
    row.x5_memory.prev_value clock timestamps
  refine ⟨alignedOf (haltRowFacts row) touches, ?_⟩
  apply alignedFacts_of_touches (haltRowFacts row) touches
  · constructor <;>
      dsimp only [alignedOf, touches, SystemTouches.touches, haltRowFacts, HaltChip.memoryPairs,
        List.map_cons, List.map_nil] <;>
      exact List.Perm.refl _
  · change ∀ touch ∈ touches, TouchOK (SystemTouches.start row.state) touch.1 touch.2
    exact facts.1
  · exact facts.2.1
  · exact facts.2.2.1
  · exact fun touch member bound _ => facts.2.2.2 touch member bound

private theorem syscall_aligned (row : SyscallInstrsChip.Inputs (ZMod p))
    (clock : ((row.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧ row.state.clk_16_24.val < 2 ^ 8)
    (timestamps : SystemTouches.TimestampBounds row.state row.op_a_memory row.op_b_memory row.op_c_memory)
    (operands : row.op_a = 5 ∧ row.op_b = 10 ∧ row.op_c = 11) :
    ∃ aligned, AlignedFacts aligned (syscallRowFacts row) := by
  let touches := SystemTouches.touches row.state row.op_a_memory row.op_b_memory row.op_c_memory row.op_a_value
  have facts := SystemTouches.touches_spec row.state row.op_a_memory row.op_b_memory row.op_c_memory
    row.op_a_value clock timestamps
  refine ⟨alignedOf (syscallRowFacts row) touches, alignedFacts_of_touches (syscallRowFacts row) touches ?_ facts.1 facts.2.1 facts.2.2.1
    (fun touch member bound _ => facts.2.2.2 touch member bound)⟩
  constructor
  · simp only [alignedOf, syscallRowFacts, operands.1, operands.2.1, operands.2.2]
    exact List.Perm.refl _
  · simp only [alignedOf, syscallRowFacts, operands.1, operands.2.1, operands.2.2]
    exact List.Perm.refl _

private theorem ordinaryRows_aligned {image : ProgramImage} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : DecodedInstructionRow p} (member : row ∈ activeInstructionRows witness) :
    ∃ aligned, AlignedFacts aligned ((ExecutionRow.instruction row).facts witness.data) := by
  obtain ⟨decodedMem, real⟩ := List.mem_filter.mp member
  have active := of_decide_eq_true real
  have chipMem := mem_chip_of_mem_decodeInstructionTables decodedMem
  have checked := instructionRows_constraints witness constraints row decodedMem
  have byte := (instructionRows_finished_guarantees witness constraints balanced decodedMem).1
  have committed := instructionRows_program_committed valid witness constraints balanced decodedMem active
  have decode := committed.decoded_of_opcode_ne
    (supportedChip_fetchDiscriminantShape row.chip chipMem witness.data row.physical checked byte active)
  obtain ⟨touches, projection, localOK, chain, pushBound, slot⟩ :=
    (supportedChip_groundingContracts row.chip chipMem).rowAlignedLocal witness.data row rfl active
      checked byte (image.toGuestProgram valid) decode
  exact ⟨alignedOf _ touches, alignedFacts_of_touches _ _ (RowMemoryPermutation.of_alignsWith projection)
    localOK chain pushBound slot⟩

private theorem haltRows_aligned {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : HaltChip.Inputs (ZMod p)} (member : row ∈ activeSystemRows (systemTable witness 2) haltRow (·.is_real)) :
    ∃ aligned, AlignedFacts aligned ((ExecutionRow.halt row).facts witness.data) := by
  obtain ⟨mapped, real⟩ := List.mem_filter.mp member
  obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp mapped
  have byte := (finishedChannel_guarantees image witness constraints balanced _ (systemTable_mem witness 2)).1
  exact halt_aligned _ (haltRow_cpuState_bounds_of_component _ (systemTable_component witness 2)
    byte physicalMem (of_decide_eq_true real))
    (haltRow_accessTimestamp_bounds_of_component _ (systemTable_component witness 2)
      byte physicalMem (of_decide_eq_true real))

private theorem syscallRows_aligned {image : ProgramImage} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : SyscallInstrsChip.Inputs (ZMod p)} (member : row ∈ activeSystemRows (systemTable witness 3) syscallInstrsRow (·.is_real)) :
    ∃ aligned, AlignedFacts aligned ((ExecutionRow.syscall row).facts witness.data) := by
  obtain ⟨mapped, real⟩ := List.mem_filter.mp member
  obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp mapped
  have byte := (finishedChannel_guarantees image witness constraints balanced _ (systemTable_mem witness 3)).1
  exact syscall_aligned _ (syscallInstrsRow_cpuState_bounds_of_component _ (systemTable_component witness 3)
    byte physicalMem (of_decide_eq_true real))
    (syscallInstrsRow_accessTimestamp_bounds_of_component _ (systemTable_component witness 3)
      byte physicalMem (of_decide_eq_true real))
    (syscall_operands valid witness constraints balanced physicalMem (of_decide_eq_true real))

/-- All active event kinds admit aligned touches from raw constraints, balance, and a checked image. -/
theorem executionRows_aligned {image : ProgramImage} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : ExecutionRow p} (member : row ∈ executionRows witness) :
    ∃ aligned, AlignedFacts aligned (row.facts witness.data) := by
  simp only [executionRows, List.mem_append, List.mem_map] at member
  rcases member with (⟨decoded, member, rfl⟩ | ⟨halt, member, rfl⟩) | ⟨syscall, member, rfl⟩
  · exact ordinaryRows_aligned valid witness constraints balanced member
  · exact haltRows_aligned witness constraints balanced member
  · exact syscallRows_aligned valid witness constraints balanced member

private theorem align_rows (data : ProverData (ZMod p)) (ordered : List (ExecutionRow p))
    (available : ∀ row ∈ ordered, ∃ aligned, AlignedFacts aligned (row.facts data)) :
    ∃ rows, List.Forall₂ AlignedFacts rows (ordered.map (ExecutionRow.facts data)) := by
  induction ordered with
  | nil => exact ⟨[], .nil⟩
  | cons head tail ih =>
    obtain ⟨aligned, headOK⟩ := available head List.mem_cons_self
    obtain ⟨rows, tailOK⟩ := ih (fun row member => available row (List.mem_cons_of_mem _ member))
    exact ⟨aligned :: rows, .cons headOK tailOK⟩

/-- One assembly statement: an exhaustive State order and aligned, ledger-preserving Memory rows.
Instruction cases, system-table positions, and per-row touch permutations are internal. -/
theorem ordered_aligned_rows {image : ProgramImage} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∃ (ordered : List (ExecutionRow p)) (rows : List (RowFacts p)),
      ordered.Perm (executionRows witness) ∧
      Walk.IsWalk (ExecutionRow.canonEdge witness.data)
        (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) ordered ∧
      List.Forall₂ AlignedFacts rows (ordered.map (ExecutionRow.facts witness.data)) ∧
      ∀ loc, optMS (memoryInitialFrontier witness loc) + pushesAt rows loc +
          Multiset.filter (fun message => MemoryMsg.locOf message = loc)
            (↑((memoryRefreshes witness).map Prod.snd) : Multiset _) =
        optMS (memoryFinalFrontier witness loc) + pullsAt rows loc +
          Multiset.filter (fun message => MemoryMsg.locOf message = loc)
            (↑((memoryRefreshes witness).map Prod.fst) : Multiset _) := by
  obtain ⟨ordered, exhaustive, walk⟩ := executionRows_ordered witness constraints balanced
  obtain ⟨rows, alignment⟩ := align_rows witness.data ordered
    (fun row member => executionRows_aligned valid witness constraints balanced (exhaustive.mem_iff.mp member))
  exact ⟨ordered, rows, exhaustive, walk, alignment,
    memory_balance_of_row_projection witness constraints balanced ordered exhaustive rows
      (alignment.imp (fun _ _ aligned => aligned.memory))⟩

end SP1Clean.Soundness.NativeCore
