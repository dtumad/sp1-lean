import SP1Clean.Native.Chips.SyscallInstrsChip.Defs
import Clean.Utils.Tactics

/-! # `SyscallInstrs` soundness and completeness

The chip boundary for SP1's ECALL table. `Assumptions` is `True`: every fact the `Spec` reports is
either asserted by the row or received as a pulled guarantee.

The `Spec`'s halt conjunct is where the interesting content sits. `ExitCodeValid` is a disjunction
because SP1's bound is one: the `U16CompareOperation` decides whether `a0`'s limb 1 is strictly
below `0x7F00`, and when it is not, the two conditionals force limb 1 to *equal* the bound and
limb 0 to vanish. Both branches keep the word's reduction under KoalaBear's modulus, which is what
makes the committed exit code decode back to `a0`. -/

namespace SP1Clean.SyscallInstrsChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel exitChannel
  syscallChannel publicValuesChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

theorem soundness :
    GeneralFormalCircuit.Soundness (Output := unit) (ZMod p) main
      (fun _ _ => True) (fun input _ _ => Spec input) := by
  circuit_proof_start
  simp only [circuit_norm, memoryChannel, programChannel,
    Channels.MemoryMsg.isU64, Channels.MemoryMsg.ClkBound, Channels.ProgramMsg.RowSpec]
    at h_holds ⊢
  obtain ⟨h_gate, h_haltbool, -, h_cbool, -, -, -, -, -, -, -, -, -, h_padhalt, -,
    h_cpu, h_raca, h_racb, h_racc, h_rest⟩ := h_holds
  obtain ⟨-, -, h_memb, h_memc, -, -, -, -, -, -, -, -, -, -, h_np0, h_np1, h_np2, h_b2, h_b3,
    h_cmp, h_cmp1, h_cmp0, h_tail⟩ := h_rest
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, h_ba0, h_ba1, h_ba2, h_ba3, -⟩ := h_tail
  have h_bin := bool_of_mul_pred h_gate
  have h_hbin := bool_of_mul_pred h_haltbool
  have h_cbin := bool_of_mul_pred h_cbool
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec (h_cpu h_bin)
  -- The `Vector`-component eval crossings `h_input` leaves whole.
  have enp : ∀ i (hi : i < 3),
      Expression.eval env input_var_next_pc[i] = input_next_pc[i] := by
    intro i hi
    have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.2.2.2.1
    simpa using this
  have eoa : ∀ i (hi : i < 4),
      Expression.eval env input_var_op_a_value[i] = input_op_a_value[i] := by
    intro i hi
    have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.2.2.2.2.2.1
    simpa using this
  have eob : ∀ i (hi : i < 4),
      Expression.eval env input_var_op_b_memory_prev_value[i]
        = input_op_b_memory_prev_value[i] := by
    intro i hi
    have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.1.1
    simpa using this
  refine ⟨⟨h_bin, h_hbin, h_cpu h_bin, h_raca h_bin, h_racb h_bin, h_racc h_bin, ?_⟩, ?_⟩
  · intro hh
    -- A halting row is real, so its memory pulls delivered their guarantees.
    have hreal : input_is_real = 1 := by
      have := h_padhalt
      rw [hh, mul_one] at this
      linear_combination this
    obtain ⟨hb_u64, -⟩ := h_memb (by rw [hreal])
    have hbound : ((fieldLimbBound : ℕ) : ZMod p).val = fieldLimbBound := by
      have hp : (2 : ℕ) ^ 17 < p := Fact.out
      exact ZMod.val_natCast_of_lt (by simp only [fieldLimbBound]; omega)
    -- `next_pc = haltPc`
    have e0 := h_np0
    have e1 := h_np1
    have e2 := h_np2
    rw [hh, one_mul] at e0 e1 e2
    rw [enp 0 (by norm_num)] at e0
    rw [enp 1 (by norm_num)] at e1
    rw [enp 2 (by norm_num)] at e2
    refine ⟨⟨by linear_combination e0, by linear_combination e1, by linear_combination e2⟩,
      ?_, ?_, ?_⟩
    · have := h_b2; rw [hh, one_mul, eob 2 (by norm_num)] at this; exact this
    · have := h_b3; rw [hh, one_mul, eob 3 (by norm_num)] at this; exact this
    · -- Limb 1 is below the bound, or exactly it with limb 0 zero.
      have hassm : U16CompareOperation.circuit.Assumptions
          { a := Expression.eval env input_var_op_b_memory_prev_value[1],
            b := ((fieldLimbBound : ℕ) : ZMod p),
            cols := { bit := input_op_b_cmp_bit }, is_real := input_is_halt } := by
        refine ⟨fun _ => ⟨?_, ?_⟩, h_hbin⟩
        · rw [eob 1 (by norm_num)]; exact hb_u64 1
        · rw [hbound]; simp only [fieldLimbBound]; omega
      have hspec := (h_cmp hassm).2 hh
      simp only at hspec
      rw [eob 1 (by norm_num), hbound] at hspec
      by_cases hlt : (input_op_b_memory_prev_value[1]).val < fieldLimbBound
      · exact Or.inl hlt
      have hbit : input_op_b_cmp_bit = 0 := by rw [hspec, if_neg hlt]
      refine Or.inr ⟨?_, ?_⟩
      · have h1 := h_cmp1
        rw [hh, one_mul, hbit, eob 1 (by norm_num)] at h1
        have heq : input_op_b_memory_prev_value[1] = ((fieldLimbBound : ℕ) : ZMod p) := by
          linear_combination -h1
        rw [heq, hbound]
      · have h0 := h_cmp0
        rw [hh, one_mul, hbit, eob 0 (by norm_num)] at h0
        linear_combination -h0
  · -- The requirement tail: sub-circuit assumptions, off-gate pulls, push requirements.
    and_intros <;>
      first
        | exact h_bin
        | exact h_hbin
        | exact Or.inl rfl
        | exact Or.inr h_bin
        | exact fun _ _ => trivial
        | exact fun h1 h0 => off_gate_vacuous h_bin h1 h0
        | exact fun h1 h0 => off_gate_vacuous h_cbin h1 h0
        | (intro _ h0
           have hr : input_is_real = 1 := h_bin.resolve_left h0
           have hneg : (-input_is_real : ZMod p) = -1 := by rw [hr]
           have hp : (2 : ℕ) ^ 17 < p := Fact.out
           refine ⟨?_, ?_⟩
           · first
               | exact (h_memb hneg).1
               | exact (h_memc hneg).1
               | exact Word.isU64_of_cases
                   (eoa 0 (by norm_num) ▸ (byteRowSpec_range _ (by omega)).mp (h_ba0 hneg))
                   (eoa 1 (by norm_num) ▸ (byteRowSpec_range _ (by omega)).mp (h_ba1 hneg))
                   (eoa 2 (by norm_num) ▸ (byteRowSpec_range _ (by omega)).mp (h_ba2 hneg))
                   (eoa 3 (by norm_num) ▸ (byteRowSpec_range _ (by omega)).mp (h_ba3 hneg))
           · first
               | exact h_clk.at_four hr
               | exact h_clk.at_three hr
               | exact h_clk.at_two hr)

end SP1Clean.SyscallInstrsChip
