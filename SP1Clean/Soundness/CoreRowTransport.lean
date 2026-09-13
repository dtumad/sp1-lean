import SP1Clean.Soundness.CoreTouches
import SP1Clean.Soundness.MixedRowTransport

/-! # Shared semantic transport through alignment and refresh rewriting

The transformation preserves each event's fetch and semantic State endpoints, and matches its
reads inside their pre-effect windows. Only equal-value prior records at the same location and an
earlier time may replace the original pulls. These lemmas carry arbitrary trajectory step/frame
facts through the structural transformation; they do not assert host execution.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance coreRowTransportField24 : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance coreRowTransportField17 : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

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

theorem syscall_readsInWindow_of_committed (row : SyscallInstrsChip.Inputs (ZMod p))
    (program : Target.GuestProgram)
    (committed : Target.committedInROM program (rowOfMsg (SyscallInstrsChip.programMessage row))) :
    ReadsInWindow (syscallRowFacts row) := by
  have shape := (committed.ecall_of_opcode rfl).2
  exact syscall_readsInWindow row
    (congrArg (fun r : ProgramChip.ProgramRow (ZMod p) => r.op_b[0]) shape)
    (congrArg (fun r : ProgramChip.ProgramRow (ZMod p) => r.op_c[0]) shape)

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
theorem rewritten_core {initialClock : ℕ} {row : RowFacts p} {touches : List (Touch p)}
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

/-- Apply each chosen refresh rewrite and normalize the State endpoints, retaining list order. -/
noncomputable def rewrittenRows (rows : List (RowFacts p)) (touches : List (List (Touch p))) :
    List (RowFacts p) :=
  (rows.zip touches).map (fun pair => canonicalRow (alignedOf pair.1 pair.2))

omit [Fact (2 ^ 25 < p)] in
theorem rewriteRows_forall₂ {R : RowFacts p → RowFacts p → Prop}
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
theorem rewritten_memory (rows : List (RowFacts p)) (touches : List (List (Touch p))) (loc : MemLoc) :
    pushesAt (rewrittenRows rows touches) loc =
      pushesAt ((rows.zip touches).map (fun pair => alignedOf pair.1 pair.2)) loc ∧
    pullsAt (rewrittenRows rows touches) loc =
      pullsAt ((rows.zip touches).map (fun pair => alignedOf pair.1 pair.2)) loc := by
  simp only [rewrittenRows, pushesAt, pullsAt, List.map_map, Function.comp_def, rowPushesAt, rowPullsAt,
    canonicalRow, stateRespell_memPushes, stateRespell_memPulls, and_self]

/-- A structural grounding carrier over opaque event and boundary values. Keeping the concrete
ensemble out of the carrier type avoids normalizing the complete source during structure elaboration. -/
structure ExecutionCarrier (data : ProverData (ZMod p)) (events : List (ExecutionRow p))
    (incoming outgoing : StateMsg (ZMod p))
    (initialFrontier physicalFinal : MemLoc → Option (MemoryMsg (ZMod p))) where
  ordered : List (ExecutionRow p)
  rows : List (RowFacts p)
  final : MemLoc → Option (MemoryMsg (ZMod p))
  exhaustive : ordered.Perm events
  aligned : List.Forall₂ WindowAligned rows (ordered.map (ExecutionRow.facts data))
  rowOK : ∀ row ∈ rows, RowOKCore (StateMsg.timeNat incoming) row
  stateWalk : Walk.IsWalk (fun row : RowFacts p => (row.statePull, row.statePush))
    incoming outgoing rows
  memoryBalance : ∀ loc, optMS (initialFrontier loc) + pushesAt rows loc =
    optMS (final loc) + pullsAt rows loc
  finalRewrite : ∀ loc message, physicalFinal loc = some message →
    ∃ earlier, final loc = some earlier ∧ MemoryMsg.locOf earlier = MemoryMsg.locOf message ∧
      earlier.value = message.value ∧ MemoryMsg.timeNat earlier ≤ MemoryMsg.timeNat message

end SP1Clean.Soundness.NativeCore
