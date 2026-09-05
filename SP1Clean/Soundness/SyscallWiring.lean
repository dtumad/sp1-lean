import SP1Clean.Soundness.ChipContracts
import SP1Clean.Soundness.SyscallGrounding

/-! # Wiring a syscall row into the walk

`syscallStepFact_of_advance` needs the row's `Spec`, its `SelectorsValid`, its `PulledFacts` and its
`SyscallRowContext` *before* the walk runs. All four are reachable from the ensemble — but the route
to `Spec` runs through `Component.weakSoundness`, which consumes the row's **Memory** channel
guarantees, and those are a conclusion of grounding rather than an input to it.

That is the same currency circularity the ordinary rows hit, and it has the same resolution: the
walk's own step antecedent already hands each row `isU64 ∧ ClkBound` for its pulls before asking for
the step fact, so the guarantee can be rebuilt from the antecedent rather than from the walk's
output. `DecodedInstructionRow.memoryChannelGuarantees_of_pullCurrency` is the instruction-row
version; this file is the syscall one, and the halt table needed neither because it is extracted
*after* the walk rather than walked. -/

namespace SP1Clean.Soundness

open SP1Clean.Machine
open SP1Clean.Semantics
open SP1Clean.Channels (StateMsg MemoryMsg memoryChannel byteChannel programChannel)
open Air.Flat
open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- **The circularity break at a syscall row.** The row's three pulled priors carry `isU64 ∧
ClkBound` in the walk's currency antecedent; that is exactly the memory channel's `Guarantees`, so
the row's own Memory `ChannelGuarantees` follows without any appeal to the walk's output.

The three *pushes* need nothing: `consumedMessages` keeps only the pull-polarity interactions, and a
boolean gate can never make a push's `signedVal` negative. -/
theorem syscallInstrsRow_memoryGuarantees_of_pullCurrency
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (constraints : witness.Constraints)
    {row : Array (ZMod p)} (rowMem : row ∈ (syscallInstrsTable witness).table)
    (currency : ∀ mp ∈
        (syscallRowFacts (syscallInstrsRow (syscallInstrsTable witness) row)).memPulls,
      MemoryMsg.isU64 (mp : MemoryMsg (ZMod p) × ℕ).1 ∧ MemoryMsg.ClkBound mp.1) :
    (syscallInstrsTable witness).component.operations.ChannelGuarantees memoryChannel.toRaw
      ((syscallInstrsTable witness).environment row) := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 24 < p); omega
  have hbool := witness_syscallInstrsRows_selectorBinary witness constraints row rowMem
  refine channelGuarantees_of_consumedMessages _ memoryChannel _ hp fun msg msgMem => ?_
  rw [syscallInstrsRow_typedMemory, consumedMessages, List.mem_map] at msgMem
  obtain ⟨i, iMem, rfl⟩ := msgMem
  rw [List.mem_filter, decide_eq_true_eq] at iMem
  obtain ⟨iList, iPull⟩ := iMem
  -- A push can never be on the consumed side: its multiplicity is the boolean gate itself.
  have pushImpossible : ∀ {m : MemoryMsg (ZMod p)},
      signedVal (TypedInteraction.pushedIfValue memoryChannel
        (syscallInstrsRow (syscallInstrsTable witness) row).is_real m).mult = -1 → False := by
    intro m h
    rw [TypedInteraction.pushedIfValue_mult, signedVal_is_real hp hbool] at h
    rcases hbool with h0 | h1
    · rw [h0, ZMod.val_zero] at h; simp at h
    · rw [h1, ZMod.val_one] at h; simp at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at iList
  rcases iList with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [TypedInteraction.pulledIfValue_message]
    refine currency (SyscallInstrsChip.memPulledMessage
      (syscallInstrsRow (syscallInstrsTable witness) row)
      (syscallInstrsRow (syscallInstrsTable witness) row).op_a_memory
      (syscallInstrsRow (syscallInstrsTable witness) row).op_a,
      StateMsg.timeNat (SyscallInstrsChip.statePulledMessage
        (syscallInstrsRow (syscallInstrsTable witness) row))) ?_
    rw [syscallRowFacts_memPulls]
    exact List.mem_cons_self
  · exact absurd iPull pushImpossible
  · rw [TypedInteraction.pulledIfValue_message]
    refine currency (SyscallInstrsChip.memPulledMessage
      (syscallInstrsRow (syscallInstrsTable witness) row)
      (syscallInstrsRow (syscallInstrsTable witness) row).op_b_memory
      (syscallInstrsRow (syscallInstrsTable witness) row).op_b,
      StateMsg.timeNat (SyscallInstrsChip.statePulledMessage
        (syscallInstrsRow (syscallInstrsTable witness) row)) + 3) ?_
    rw [syscallRowFacts_memPulls]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact absurd iPull pushImpossible
  · rw [TypedInteraction.pulledIfValue_message]
    refine currency (SyscallInstrsChip.memPulledMessage
      (syscallInstrsRow (syscallInstrsTable witness) row)
      (syscallInstrsRow (syscallInstrsTable witness) row).op_c_memory
      (syscallInstrsRow (syscallInstrsTable witness) row).op_c,
      StateMsg.timeNat (SyscallInstrsChip.statePulledMessage
        (syscallInstrsRow (syscallInstrsTable witness) row)) + 2) ?_
    rw [syscallRowFacts_memPulls]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact absurd iPull pushImpossible

/-- **A syscall row's `Spec`, from the walk's currency rather than from grounding.** This is the
statement `SyscallRowWiring` is built on: everything the row's meaning needs is either a finished
channel (Byte, Program) or the antecedent the walk supplies anyway. -/
theorem syscallInstrsRow_spec_of_pullCurrency
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (constraints : witness.Constraints)
    (balanced : witness.BalancedChannels)
    {row : Array (ZMod p)} (rowMem : row ∈ (syscallInstrsTable witness).table)
    (currency : ∀ mp ∈
        (syscallRowFacts (syscallInstrsRow (syscallInstrsTable witness) row)).memPulls,
      MemoryMsg.isU64 (mp : MemoryMsg (ZMod p) × ℕ).1 ∧ MemoryMsg.ClkBound mp.1) :
    SyscallInstrsChip.Spec (syscallInstrsRow (syscallInstrsTable witness) row) := by
  have tableMem : syscallInstrsTable witness ∈ witness.tables :=
    List.getElem_mem (syscallInstrsIndex_lt_tablesLength witness)
  have tableConstraints : (syscallInstrsTable witness).Constraints :=
    constraints _ (witness.mem_allTables_of_mem_tables tableMem)
  have finished := sp1_finishedChannel_guarantees witness constraints balanced
    _ (witness.mem_allTables_of_mem_tables tableMem)
  exact syscallInstrsRow_spec_of_facts witness tableConstraints finished.1 finished.2
    (syscallInstrsRow_memoryGuarantees_of_pullCurrency witness constraints rowMem currency) rowMem

end SP1Clean.Soundness
