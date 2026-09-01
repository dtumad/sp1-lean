import SP1Clean.Native.Chips.SyscallChip.Defs
import Clean.Utils.Tactics

/-! # `SyscallInstrs` soundness and completeness

The chip boundary for SP1's ECALL table. `Assumptions` is `True`: every fact the `Spec` reports is
either asserted by the row or received as a pulled guarantee.

The `Spec`'s halt conjunct is where the interesting content sits. `ExitCodeValid` is a disjunction
because SP1's bound is one: the `U16CompareOperation` decides whether `a0`'s limb 1 is strictly
below `0x7F00`, and when it is not, the two conditionals force limb 1 to *equal* the bound and
limb 0 to vanish. Both branches keep the word's reduction under KoalaBear's modulus, which is what
makes the committed exit code decode back to `a0`. -/

namespace SP1Clean.SyscallChip

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
  obtain ⟨h_gate, h_haltbool, -, -, -, -, -, -, -, -, -, -, -, h_padhalt, -,
    h_cpu, h_raca, h_racb, h_racc, h_rest⟩ := h_holds
  obtain ⟨-, -, h_memb, -, -, -, -, -, -, -, -, -, -, -, h_np0, h_np1, h_np2, h_b2, h_b3,
    h_cmp, h_cmp1, h_cmp0, -⟩ := h_rest
  have h_bin := bool_of_mul_pred h_gate
  have h_hbin := bool_of_mul_pred h_haltbool
  -- The `Vector`-component eval crossings `h_input` leaves whole.
  have enp : ∀ i (hi : i < 3),
      Expression.eval env input_var_next_pc[i] = input_next_pc[i] := by
    intro i hi
    have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.2.2.2.1
    simpa using this
  refine ⟨⟨h_bin, h_hbin, h_cpu h_bin, h_raca h_bin, h_racb h_bin, h_racc h_bin, ?_⟩, ?_⟩
  swap
  · exact trivial
  intro hh
  -- A halting row is real, so its memory pulls delivered their guarantees.
  have hreal : input_is_real = 1 := by
    have := h_padhalt
    rw [hh, mul_one] at this
    linear_combination this
  obtain ⟨hb_u64, -⟩ := h_memb (by rw [hreal])
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `next_pc = haltPc`
    have e0 := h_np0
    have e1 := h_np1
    have e2 := h_np2
    rw [hh, one_mul] at e0 e1 e2
    rw [enp 0 (by norm_num), enp 1 (by norm_num), enp 2 (by norm_num)] at e0 e1 e2
    have : input_next_pc[0] = 1 := by linear_combination e0
    ext i hi
    interval_cases i <;> simp_all
  · -- `a0`'s limb 2 vanishes
    have := h_b2
    rw [hh, one_mul] at this
    exact this
  · -- `a0`'s limb 3 vanishes
    have := h_b3
    rw [hh, one_mul] at this
    exact this
  · -- Limb 1 is strictly below the bound, or exactly it with limb 0 zero.
    by_cases hlt : (input_op_b_memory_prev_value[1]).val < fieldLimbBound
    · exact Or.inl hlt
    refine Or.inr ⟨?_, ?_⟩
    · have hbit : input_op_b_cmp_bit = 0 := by
        have hspec := h_cmp ⟨fun _ => ⟨hb_u64 1 (by norm_num), by
            simpa [fieldLimbBound] using ZMod.val_natCast_of_lt (by
              have : (2 : ℕ) ^ 17 < p := Fact.out
              omega)⟩, h_hbin⟩
        have := hspec.2 hh
        rw [this]
        simp only [fieldLimbBound] at hlt
        rw [if_neg]
        simpa [fieldLimbBound] using hlt
      have := h_cmp1
      rw [hh, one_mul, hbit] at this
      have : input_op_b_memory_prev_value[1] - (fieldLimbBound : ℕ) = 0 := by
        linear_combination -this
      have heq : input_op_b_memory_prev_value[1] = ((fieldLimbBound : ℕ) : ZMod p) := by
        linear_combination this
      rw [heq]
      simpa [fieldLimbBound] using ZMod.val_natCast_of_lt (by
        have : (2 : ℕ) ^ 17 < p := Fact.out
        omega)
    · have hbit : input_op_b_cmp_bit = 0 := by
        have hspec := h_cmp ⟨fun _ => ⟨hb_u64 1 (by norm_num), by
            simpa [fieldLimbBound] using ZMod.val_natCast_of_lt (by
              have : (2 : ℕ) ^ 17 < p := Fact.out
              omega)⟩, h_hbin⟩
        have := hspec.2 hh
        rw [this]
        rw [if_neg]
        simpa [fieldLimbBound] using hlt
      have := h_cmp0
      rw [hh, one_mul, hbit] at this
      linear_combination -this

end SP1Clean.SyscallChip
