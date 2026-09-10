import SP1Clean.Soundness.NativeCoreMemoryOrder
import SP1Clean.Soundness.MixedRowTransport

/-! # The native mixed carrier after refresh elimination

The carrier passed to grounding keeps every ordinary/HALT/syscall occurrence, rewrites only prior
Memory records, and uses canonical State endpoints. Its complete structural row contract and
semantic step/frame transport are derived from the checked image and raw constraints/balance.
The original rows' actual execution facts remain the next semantic obligation.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

private theorem syscall_readsInWindow (row : SyscallInstrsChip.Inputs (ZMod p))
    (opB : row.op_b = 10) (opC : row.op_c = 11) : ReadsInWindow (syscallRowFacts row) := by
  have bLoc := (syscallRow_locOf_reg row (i := 10#5)
    (by norm_num; exact opB.symm) row.op_b_memory row.op_b_memory.prev_value 3).1
  have cLoc := (syscallRow_locOf_reg row (i := 11#5)
    (by norm_num; exact opC.symm) row.op_c_memory row.op_c_memory.prev_value 2).1
  intro pull member
  simp only [syscallRowFacts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨le_rfl, Nat.le_add_right _ _⟩
  · simpa only [syscallRowFacts, bLoc, readWindow_reg] using
      (show _ ≤ _ + 3 ∧ _ + 3 ≤ _ + 3 from ⟨Nat.le_add_right _ _, le_rfl⟩)
  · simp only [syscallRowFacts, cLoc, readWindow_reg]
    omega

private theorem syscall_readsInWindow_of_committed (row : SyscallInstrsChip.Inputs (ZMod p))
    (program : Target.GuestProgram)
    (committed : Target.committedInROM program (rowOfMsg (SyscallInstrsChip.programMessage row))) :
    ReadsInWindow (syscallRowFacts row) := by
  have shape := (committed.ecall_of_opcode rfl).2
  exact syscall_readsInWindow row
    (congrArg (fun r : ProgramChip.ProgramRow (ZMod p) => r.op_b[0]) shape)
    (congrArg (fun r : ProgramChip.ProgramRow (ZMod p) => r.op_c[0]) shape)

private theorem syscallRows_readsInWindow {image : ProgramImage} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : SyscallInstrsChip.Inputs (ZMod p)}
    (member : row ∈ activeSystemRows (systemTable witness 3) syscallInstrsRow (·.is_real)) :
    ReadsInWindow (syscallRowFacts row) := by
  obtain ⟨mapped, real⟩ := List.mem_filter.mp member
  obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp mapped
  have committed := syscall_program_committed valid witness constraints balanced physicalMem (of_decide_eq_true real)
  exact syscall_readsInWindow_of_committed _ _ committed

/-- All original execution reads lie within their location's pre-effect window, with syscall
read times retained. Operand addresses for system rows come from the checked Program ledger. -/
theorem executionRows_readsInWindow {image : ProgramImage} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {event : ExecutionRow p} (member : event ∈ executionRows witness) :
    ReadsInWindow (event.facts witness.data) := by
  simp only [executionRows, List.mem_append, List.mem_map] at member
  rcases member with (⟨decoded, _, rfl⟩ | ⟨halt, _, rfl⟩) | ⟨syscall, member, rfl⟩
  · intro pull pullMem
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp pullMem
    exact ⟨le_rfl, Nat.le_add_right _ _⟩
  · intro pull pullMem
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp pullMem
    exact ⟨le_rfl, Nat.le_add_right _ _⟩
  · exact syscallRows_readsInWindow valid witness constraints balanced member

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
/-- Local alignment becomes semantic transport once the original reads' windows and prior
low-clock bounds are known. No global Memory truth is required. -/
theorem AlignedFacts.windowAligned {aligned original : RowFacts p}
    (facts : AlignedFacts aligned original) (reads : ReadsInWindow original)
    (prior : ∀ pull ∈ original.memPulls, MemoryMsg.ClkBound pull.1) :
    WindowAligned aligned original where
  pullTime := congrArg StateMsg.timeNat facts.statePull
  pullPc := congrArg StateMsg.pcBits facts.statePull
  pushTime := congrArg StateMsg.timeNat facts.statePush
  pushPc := congrArg StateMsg.pcBits facts.statePush
  fetch := facts.fetch
  pushes := facts.memory.pushes
  pullClk := prior
  originalReads := reads
  match_ := by
    intro pull member
    have mapped := facts.memory.pulls.mem_iff.mpr (List.mem_map_of_mem member)
    obtain ⟨matched, matchedMem, same⟩ := List.mem_map.mp mapped
    obtain ⟨_, _, touch⟩ := forall₂_exists_right facts.touches matched matchedMem
    exact ⟨matched, matchedMem, congrArg MemoryMsg.locOf same, congrArg (·.value) same,
      touch.read_lo, by rw [← same]; exact touch.read_hi⟩

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
private theorem rewritten_core {initialClock : ℕ} {row : RowFacts p} {touches : List (Touch p)}
    (ok : RowOKCore initialClock row)
    (prior : ∀ pull ∈ row.memPulls, MemoryMsg.ClkBound pull.1)
    (rewrite : List.Forall₂ PullRewrite (rowTouches row) touches) :
    RowOKCore initialClock (alignedOf row touches) := by
  refine rowOKCore_alignedOf_pullRewrite initialClock row (rowTouches row) touches rewrite
    ok.timeGap ok.align8 ?_ ok.chain_mono ?_ ?_
  · exact fun touch member => (List.forall₂_iff_zip.mp ok.touches).2 member
  · exact fun touch member => ok.pushClkBound _ (List.of_mem_zip member).2
  · exact fun touch member => ok.slotOfClkBound touch member (prior _ (List.of_mem_zip member).1)

/-- Canonical State messages on a row, independent of its Memory touch representation. -/
noncomputable def canonicalRow (row : RowFacts p) : RowFacts p :=
  stateRespell row (canonState row.statePull) (canonState row.statePush)

private theorem canonical_times {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {event : ExecutionRow p} (member : event ∈ executionRows witness) :
    StateMsg.timeNat (canonState (event.facts witness.data).statePull) = StateMsg.timeNat (event.facts witness.data).statePull ∧
    StateMsg.pcBits (canonState (event.facts witness.data).statePull) = StateMsg.pcBits (event.facts witness.data).statePull ∧
    StateMsg.timeNat (canonState (event.facts witness.data).statePush) = StateMsg.timeNat (event.facts witness.data).statePush ∧
    StateMsg.pcBits (canonState (event.facts witness.data).statePush) = StateMsg.pcBits (event.facts witness.data).statePush := by
  have good := executionRows_good witness constraints balanced member
  rw [ExecutionRow.edge_eq_facts] at good
  exact ⟨timeNat_canonState good.1.1, pcBits_canonState good.1.2.1 good.1.2.2,
    timeNat_canonState good.2.1, pcBits_canonState good.2.2.1 good.2.2.2⟩

/-- Apply each chosen refresh rewrite and normalize the State endpoints, retaining list order. -/
noncomputable def rewrittenRows (rows : List (RowFacts p)) (touches : List (List (Touch p))) :
    List (RowFacts p) :=
  (rows.zip touches).map (fun pair => canonicalRow (alignedOf pair.1 pair.2))

omit [Fact (2 ^ 25 < p)] in
private theorem rewriteRows_forall₂ {R : RowFacts p → RowFacts p → Prop}
    {rows originals : List (RowFacts p)} (alignment : List.Forall₂ AlignedFacts rows originals)
    {touches : List (List (Touch p))}
    (rewrite : List.Forall₂ (List.Forall₂ PullRewrite) (rows.map rowTouches) touches)
    (each : ∀ row ∈ rows, ∀ original ∈ originals, ∀ ts,
      AlignedFacts row original → List.Forall₂ PullRewrite (rowTouches row) ts →
        R (canonicalRow (alignedOf row ts)) original) :
    List.Forall₂ R (rewrittenRows rows touches) originals := by
  induction alignment generalizing touches with
  | nil => cases rewrite; exact .nil
  | @cons row original rows originals aligned rest ih =>
    cases rewrite with
    | cons head tail =>
      exact .cons (each row List.mem_cons_self original List.mem_cons_self _ aligned head)
        (ih tail (fun r rMem o oMem ts => each r (List.mem_cons_of_mem _ rMem)
          o (List.mem_cons_of_mem _ oMem) ts))

omit [Fact (2 ^ 25 < p)] in
private theorem rewritten_memory (rows : List (RowFacts p)) (touches : List (List (Touch p))) (loc : MemLoc) :
    pushesAt (rewrittenRows rows touches) loc =
      pushesAt ((rows.zip touches).map (fun pair => alignedOf pair.1 pair.2)) loc ∧
    pullsAt (rewrittenRows rows touches) loc =
      pullsAt ((rows.zip touches).map (fun pair => alignedOf pair.1 pair.2)) loc := by
  simp only [rewrittenRows, pushesAt, pullsAt, List.map_map, Function.comp_def, rowPushesAt, rowPullsAt,
    canonicalRow, stateRespell_memPushes, stateRespell_memPulls, and_self]

/-- A complete structural carrier for the generic grounding walk. The semantic alignment points
back to the actual event rows, so later step/frame proofs do not depend on refresh implementation. -/
structure GroundingCarrier {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) where
  ordered : List (ExecutionRow p)
  rows : List (RowFacts p)
  final : MemLoc → Option (MemoryMsg (ZMod p))
  exhaustive : ordered.Perm (executionRows witness)
  aligned : List.Forall₂ WindowAligned rows (ordered.map (ExecutionRow.facts witness.data))
  rowOK : ∀ row ∈ rows, RowOKCore (StateMsg.timeNat (initialBoundaryStateMessage witness.publicInput)) row
  stateWalk : Walk.IsWalk (fun row : RowFacts p => (row.statePull, row.statePush))
    (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) rows
  memoryBalance : ∀ loc, optMS (memoryInitialFrontier witness loc) + pushesAt rows loc =
    optMS (final loc) + pullsAt rows loc
  finalRewrite : ∀ loc message, memoryFinalFrontier witness loc = some message →
    ∃ earlier, final loc = some earlier ∧ MemoryMsg.locOf earlier = MemoryMsg.locOf message ∧
      earlier.value = message.value ∧ MemoryMsg.timeNat earlier ≤ MemoryMsg.timeNat message

/-- The checked image and raw AIR construct the final structural carrier. No row order, touch
permutation, prior bounds, refresh order, or semantic boundary is supplied by the caller. -/
theorem grounding_carrier {image : ProgramImage} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    Nonempty (GroundingCarrier witness) := by
  obtain ⟨ordered, rows, touches, final, exhaustive, walk, alignment, chronology,
    rewrite, balance, _, finalRewrite⟩ := memory_refresh_free valid witness constraints balanced
  have paired : List.Forall₂ (fun newer original => WindowAligned newer original ∧
      RowOKCore (StateMsg.timeNat (initialBoundaryStateMessage witness.publicInput)) newer ∧
      newer.statePull = canonState original.statePull ∧ newer.statePush = canonState original.statePush)
      (rewrittenRows rows touches) (ordered.map (ExecutionRow.facts witness.data)) := by
    apply rewriteRows_forall₂ alignment rewrite
    intro row rowMem original originalMem ts localAlignment rewritten
    obtain ⟨event, eventMem, rfl⟩ := List.mem_map.mp originalMem
    have active := exhaustive.mem_iff.mp eventMem
    have ok := chronology.rowOK row rowMem
    have canon := canonical_times witness constraints balanced active
    rw [← localAlignment.statePull, ← localAlignment.statePush] at canon
    have semantic := localAlignment.windowAligned
      (executionRows_readsInWindow valid witness constraints balanced active)
      (fun pull member => (executionRows_prior_bounds valid witness constraints balanced event active pull member).1)
    have transported := semantic.pullRewrite ok.touches.length_eq rewritten
    refine ⟨transported.stateRespell canon.1 canon.2.1 canon.2.2.1 canon.2.2.2,
      rowOKCore_stateRespell canon.1 canon.2.2.1
        (rewritten_core ok (fun pull member => (chronology.priorBounds row rowMem pull member).1) rewritten), ?_, ?_⟩
    · exact congrArg canonState localAlignment.statePull
    · exact congrArg canonState localAlignment.statePush
  refine ⟨⟨ordered, rewrittenRows rows touches, final, exhaustive,
    paired.imp (fun _ _ facts => facts.1), ?_, ?_, ?_, finalRewrite⟩⟩
  · intro row member
    obtain ⟨_, _, facts⟩ := forall₂_exists_right paired row member
    exact facts.2.1
  · have edges := List.forall₂_map_right_iff.mp
      (paired.imp (fun _ _ facts => facts.2.2))
    exact Walk.isWalk_forall₂ (ExecutionRow.canonEdge witness.data)
      (fun row : RowFacts p => (row.statePull, row.statePush))
      (fun event row => row.statePull = canonState (event.facts witness.data).statePull ∧
        row.statePush = canonState (event.facts witness.data).statePush)
      (fun related => by
        dsimp only [ExecutionRow.canonEdge]
        rw [ExecutionRow.edge_eq_facts]
        exact Prod.ext related.1.symm related.2.symm) edges.flip walk
  · intro loc
    rw [(rewritten_memory rows touches loc).1, (rewritten_memory rows touches loc).2]
    exact balance loc

/-- The final carrier supplies exactly the generic engine's State multiset equation. -/
theorem GroundingCarrier.stateBalance {image : ProgramImage}
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness) :
    initialBoundaryStateMessage witness.publicInput ::ₘ
        (↑(carrier.rows.map (·.statePush)) : Multiset (StateMsg (ZMod p))) =
      finalBoundaryStateMessage witness.publicInput ::ₘ ↑(carrier.rows.map (·.statePull)) :=
  endpointBalance_of_stateWalk _ carrier.stateWalk

/-- Per-event step and frame facts transport to the final carrier uniformly, over any trajectory
and timeline. These semantic premises are explicitly separate from carrier construction. -/
theorem GroundingCarrier.engineFacts {image : ProgramImage}
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness)
    (program : Target.GuestProgram) (trajectory : Trajectory) (initial : SailState) (timeline : Timeline)
    (facts : ∀ event ∈ executionRows witness,
      LocalStepFactG program trajectory initial timeline (event.facts witness.data) ∧
      FrameFactG program trajectory initial timeline (event.facts witness.data)) :
    ∀ row ∈ carrier.rows, LocalStepFactG program trajectory initial timeline row ∧
      FrameFactG program trajectory initial timeline row := by
  intro row member
  obtain ⟨original, originalMem, aligned⟩ := forall₂_exists_right carrier.aligned row member
  obtain ⟨event, eventMem, rfl⟩ := List.mem_map.mp originalMem
  have semantic := facts event (carrier.exhaustive.mem_iff.mp eventMem)
  exact ⟨aligned.stepFact semantic.1, aligned.frameFact semantic.2⟩

end SP1Clean.Soundness.NativeCore
