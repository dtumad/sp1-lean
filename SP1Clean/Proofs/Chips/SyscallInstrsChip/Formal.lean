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
  obtain ⟨h_gate, h_cbool, -, h_haltbool, -, -, -, -, -, -, -, -, -, h_padhalt, -,
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

/-- A constraint vanishes when either factor does — the shape used where a gate is not boolean
(the `enter + hint - 1` selector complement takes the values `-1`, `0`). -/
private lemma gated_of_cases {p : ℕ} [Fact p.Prime] {x y : ZMod p}
    (h : x = 0 ∨ y = 0) : x * y = 0 := by
  rcases h with h | h <;> rw [h] <;> ring

private lemma one_sub_bool {p : ℕ} [Fact p.Prime] {x : ZMod p}
    (hx : x = 0 ∨ x = 1) : (1 : ZMod p) - x = 0 ∨ (1 : ZMod p) - x = 1 := by
  rcases hx with h | h <;> rw [h] <;> simp

private lemma eq_zero_of_one_sub {p : ℕ} [Fact p.Prime] {x : ZMod p}
    (h : (1 : ZMod p) - x = 1) : x = 0 := by linear_combination -h

/-- A gated constraint holds when the gate is boolean and the gated fact holds on a live gate. -/
private lemma gate_zero {p : ℕ} [Fact p.Prime] {x y : ZMod p}
    (hx : x = 0 ∨ x = 1) (h : x = 1 → y = 0) : x * y = 0 := by
  rcases hx with h0 | h1
  · rw [h0]; ring
  · rw [h1, one_mul]; exact h h1

/-- The mirror shape: a constraint gated on `is_real - 1`, which vanishes on a live row. -/
private lemma pad_zero {p : ℕ} [Fact p.Prime] {x y : ZMod p}
    (hx : x = 0 ∨ x = 1) (h : x = 0 → y = 0) : (x - 1) * y = 0 := by
  rcases hx with h0 | h1
  · rw [h0, h h0]; ring
  · rw [h1]; ring

theorem completeness :
    GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) main
      (fun input _ _ => RowContract input) (fun _ _ _ => True) := by
  circuit_proof_start
  dsimp only [RowContract, GatesBoolean, SelectorsValid, PcArm, WriteArm, DispatchArm,
    CommitArm, PulledFacts] at h_assumptions
  obtain ⟨⟨h_rbin, h_cbin, h_dbin, h_hbin, h_tbin⟩, h_cpu, h_raca, h_racb, h_racc,
    h_sel, h_pc, h_write, h_disp, h_commit, h_pull, h_a0bin, h_exit⟩ := h_assumptions
  obtain ⟨h_split, h_res, h_inv, h_cmpb, h_cmpc, h_halteq, h_pad⟩ := h_sel
  obtain ⟨h_pchalt, h_pcnext⟩ := h_pc
  obtain ⟨h_wu64, h_wa0, h_ebin, h_ehsum, h_wx0, h_wenter, h_wunch, h_cdsum⟩ := h_write
  obtain ⟨h_cbits, h_cidx, h_csum1, h_csum0, h_cupper, h_cpack, h_cdef, h_cbytes⟩ := h_commit
  simp only [circuit_norm, memoryChannel, programChannel,
    Channels.MemoryMsg.isU64, Channels.MemoryMsg.ClkBound, Channels.ProgramMsg.RowSpec]
  have epc : ∀ i (hi : i < 3),
      Expression.eval env.toEnvironment input_var_state_pc[i] = input_state_pc[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.1.2.2.2; simpa using this
  have enp : ∀ i (hi : i < 3),
      Expression.eval env.toEnvironment input_var_next_pc[i] = input_next_pc[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.2.2.2.1; simpa using this
  have eav : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_op_a_value[i] = input_op_a_value[i] := by
    intro i hi
    have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.2.2.2.2.2.1; simpa using this
  have eob : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_op_b_memory_prev_value[i]
        = input_op_b_memory_prev_value[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.1.1; simpa using this
  have eoc : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_op_c_memory_prev_value[i]
        = input_op_c_memory_prev_value[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.2.2.1.1; simpa using this
  have eoa : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_op_a_memory_prev_value[i]
        = input_op_a_memory_prev_value[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.2.1.1; simpa using this
  have esb : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_syscall_id_bytes_low_bytes[i]
        = input_syscall_id_bytes_low_bytes[i] := by
    intro i hi
    have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.2.2.2.2.2.2.1; simpa using this
  have edb : ∀ i (hi : i < 8),
      Expression.eval env.toEnvironment input_var_digest_index_bits[i]
        = input_digest_index_bits[i] := by
    intro i hi
    have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    simpa using this
  have edw : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_digest_word[i] = input_digest_word[i] := by
    intro i hi
    have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    simpa using this
  simp only [epc, enp, eav, eob, eoc, eoa, esb, edb, edw]
  dsimp only [U16CompareOperation.Spec] at h_cmpb h_cmpc
  have hbound : ((fieldLimbBound : ℕ) : ZMod p).val = fieldLimbBound := by
    have hp : (2 : ℕ) ^ 17 < p := Fact.out
    exact ZMod.val_natCast_of_lt (by simp only [fieldLimbBound]; omega)
  have hrealHalt : input_is_halt = 1 → input_is_real = 1 := by
    intro hh
    rcases h_rbin with h0 | h1
    · exact absurd ((h_pad h0).2.1) (by rw [hh]; exact one_ne_zero)
    · exact h1
  have hrealDef : input_is_commit_deferred_result = 1 → input_is_real = 1 := by
    intro hd
    rcases h_rbin with h0 | h1
    · exact absurd ((h_pad h0).2.2) (by rw [hd]; exact one_ne_zero)
    · exact h1
  have hvalEq : ∀ {x : ZMod p}, x.val = fieldLimbBound → x = ((fieldLimbBound : ℕ) : ZMod p) := by
    intro x hx
    have : ((x.val : ℕ) : ZMod p) = ((fieldLimbBound : ℕ) : ZMod p) := by rw [hx]
    simpa [ZMod.natCast_val, ZMod.cast_id] using this
  and_intros
  · exact gate_zero h_rbin (fun h => by rw [h]; ring)
  · exact gate_zero h_cbin (fun h => by rw [h]; ring)
  · exact gate_zero h_dbin (fun h => by rw [h]; ring)
  · exact gate_zero h_hbin (fun h => by rw [h]; ring)
  · exact gate_zero h_tbin (fun h => by rw [h]; ring)
  · exact h_rbin
  · exact h_split
  · exact h_rbin
  · intro hr
    exact ⟨by rw [(h_res hr).1]; simp [syscallId, sub_eq_zero], (h_inv hr).1⟩
  · exact h_rbin
  · intro hr
    exact ⟨by rw [(h_res hr).2.1]; simp [syscallId, sub_eq_zero], (h_inv hr).2.1⟩
  · exact h_rbin
  · intro hr
    exact ⟨by rw [(h_res hr).2.2.1]; simp [syscallId, sub_eq_zero], (h_inv hr).2.2.1⟩
  · exact h_rbin
  · intro hr
    exact ⟨by rw [(h_res hr).2.2.2.1]; simp [syscallId, sub_eq_zero], (h_inv hr).2.2.2.1⟩
  · exact h_rbin
  · intro hr
    exact ⟨by rw [(h_res hr).2.2.2.2]; simp [syscallId, sub_eq_zero], (h_inv hr).2.2.2.2⟩
  · linear_combination h_halteq
  · exact pad_zero h_rbin (fun h => (h_pad h).1)
  · exact pad_zero h_rbin (fun h => (h_pad h).2.1)
  · exact pad_zero h_rbin (fun h => (h_pad h).2.2)
  · exact h_rbin
  · exact h_cpu
  · exact h_rbin
  · exact h_raca
  · exact h_rbin
  · exact h_racb
  · exact h_rbin
  · exact h_racc
  · intro hneg
    have hr : input_is_real = 1 := neg_inj.mp hneg
    exact ⟨(h_pull hr).1, (h_pull hr).2.1, (h_pull hr).2.2.1, (h_pull hr).2.2.2.1,
      (h_pull hr).2.2.2.2.1⟩
  · intro hneg
    have hr : input_is_real = 1 := neg_inj.mp hneg
    exact ⟨(h_pull hr).2.2.2.2.2.1, (h_pull hr).2.2.2.2.2.2.1⟩
  · intro hneg
    have hr : input_is_real = 1 := neg_inj.mp hneg
    exact ⟨(h_pull hr).2.2.2.2.2.2.2.1, (h_pull hr).2.2.2.2.2.2.2.2.1⟩
  · intro hneg
    have hr : input_is_real = 1 := neg_inj.mp hneg
    exact ⟨(h_pull hr).2.2.2.2.2.2.2.2.2.1, (h_pull hr).2.2.2.2.2.2.2.2.2.2⟩
  · exact gate_zero h_rbin h_wa0
  · exact gate_zero h_a0bin (fun h => h_wx0 h 0)
  · exact gate_zero h_a0bin (fun h => h_wx0 h 1)
  · exact gate_zero h_a0bin (fun h => h_wx0 h 2)
  · exact gate_zero h_a0bin (fun h => h_wx0 h 3)
  · exact gate_zero h_rbin (fun hr => gate_zero (one_sub_bool h_hbin)
      (fun hg => by linear_combination (h_pcnext hr (eq_zero_of_one_sub hg)).1))
  · exact gate_zero h_rbin (fun hr => gate_zero (one_sub_bool h_hbin)
      (fun hg => by linear_combination (h_pcnext hr (eq_zero_of_one_sub hg)).2.1))
  · exact gate_zero h_rbin (fun hr => gate_zero (one_sub_bool h_hbin)
      (fun hg => by linear_combination (h_pcnext hr (eq_zero_of_one_sub hg)).2.2))
  · exact gate_zero h_tbin (fun h => (h_disp h).1)
  · exact gate_zero h_tbin (fun h => (h_disp h).2)
  · exact gate_zero h_hbin (fun h => by linear_combination (h_pchalt h).1)
  · exact gate_zero h_hbin (fun h => (h_pchalt h).2.1)
  · exact gate_zero h_hbin (fun h => (h_pchalt h).2.2)
  · exact gate_zero h_hbin (fun h => (h_exit h).1)
  · exact gate_zero h_hbin (fun h => (h_exit h).2.1)
  · intro hh
    refine ⟨(h_pull (hrealHalt hh)).2.2.2.2.2.2.2.1 1, ?_⟩
    rw [hbound]
    simp only [fieldLimbBound]
    omega
  · exact h_hbin
  · exact h_cmpb.1
  · exact h_cmpb.2
  · exact gate_zero h_hbin (fun hh => gated_of_cases (by
      by_cases hlt : (input_op_b_memory_prev_value[1]).val < fieldLimbBound
      · exact Or.inl (by rw [h_cmpb.2 hh, hbound, if_pos hlt]; ring)
      · exact Or.inr (by
          rcases (h_exit hh).2.2 with h | h
          · exact absurd h hlt
          · rw [hvalEq h.1]; ring)))
  · exact gate_zero h_hbin (fun hh => gated_of_cases (by
      by_cases hlt : (input_op_b_memory_prev_value[1]).val < fieldLimbBound
      · exact Or.inl (by rw [h_cmpb.2 hh, hbound, if_pos hlt]; ring)
      · exact Or.inr (by
          rcases (h_exit hh).2.2 with h | h
          · exact absurd h hlt
          · exact h.2)))
  · exact gate_zero h_dbin (fun h => (h_cdef h).1)
  · exact gate_zero h_dbin (fun h => (h_cdef h).2.1)
  · intro hd
    refine ⟨(h_pull (hrealDef hd)).2.2.2.2.2.2.2.2.2.1 1, ?_⟩
    rw [hbound]
    simp only [fieldLimbBound]
    omega
  · exact h_dbin
  · exact h_cmpc.1
  · exact h_cmpc.2
  · exact gate_zero h_dbin (fun hd => gated_of_cases (by
      by_cases hlt : (input_op_c_memory_prev_value[1]).val < fieldLimbBound
      · exact Or.inl (by rw [h_cmpc.2 hd, hbound, if_pos hlt]; ring)
      · exact Or.inr (by
          rcases (h_cdef hd).2.2 with h | h
          · exact absurd h hlt
          · rw [hvalEq h.1]; ring)))
  · exact gate_zero h_dbin (fun hd => gated_of_cases (by
      by_cases hlt : (input_op_c_memory_prev_value[1]).val < fieldLimbBound
      · exact Or.inl (by rw [h_cmpc.2 hd, hbound, if_pos hlt]; ring)
      · exact Or.inr (by
          rcases (h_cdef hd).2.2 with h | h
          · exact absurd h hlt
          · exact h.2)))
  · exact gate_zero h_rbin (fun hr => gate_zero h_ebin (fun he => h_wenter hr he 0))
  · exact gate_zero h_rbin (fun hr => gate_zero h_ebin (fun he => h_wenter hr he 1))
  · exact gate_zero h_rbin (fun hr => gate_zero h_ebin (fun he => h_wenter hr he 2))
  · exact gate_zero h_rbin (fun hr => gate_zero h_ebin (fun he => h_wenter hr he 3))
  · exact gate_zero h_rbin (fun hr => gated_of_cases (h_ehsum.elim
      (fun h0 => Or.inr (sub_eq_zero_of_eq (h_wunch hr h0 0)))
      (fun h1 => Or.inl (sub_eq_zero_of_eq h1))))
  · exact gate_zero h_rbin (fun hr => gated_of_cases (h_ehsum.elim
      (fun h0 => Or.inr (sub_eq_zero_of_eq (h_wunch hr h0 1)))
      (fun h1 => Or.inl (sub_eq_zero_of_eq h1))))
  · exact gate_zero h_rbin (fun hr => gated_of_cases (h_ehsum.elim
      (fun h0 => Or.inr (sub_eq_zero_of_eq (h_wunch hr h0 2)))
      (fun h1 => Or.inl (sub_eq_zero_of_eq h1))))
  · exact gate_zero h_rbin (fun hr => gated_of_cases (h_ehsum.elim
      (fun h0 => Or.inr (sub_eq_zero_of_eq (h_wunch hr h0 3)))
      (fun h1 => Or.inl (sub_eq_zero_of_eq h1))))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_cbits 0 hr) (fun hb => by rw [hb]; ring))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_cbits 1 hr) (fun hb => by rw [hb]; ring))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_cbits 2 hr) (fun hb => by rw [hb]; ring))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_cbits 3 hr) (fun hb => by rw [hb]; ring))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_cbits 4 hr) (fun hb => by rw [hb]; ring))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_cbits 5 hr) (fun hb => by rw [hb]; ring))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_cbits 6 hr) (fun hb => by rw [hb]; ring))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_cbits 7 hr) (fun hb => by rw [hb]; ring))
  · exact gate_zero h_rbin (fun hr => gate_zero h_cdsum
      (fun hc => by linear_combination h_csum1 hr hc))
  · exact gate_zero h_rbin (fun hr => gate_zero (one_sub_bool h_cdsum)
      (fun hg => h_csum0 hr (eq_zero_of_one_sub hg)))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_cbits 0 hr)
      (fun hb => by have := h_cidx hr 0 hb; norm_num at this; linear_combination this))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_cbits 1 hr)
      (fun hb => by have := h_cidx hr 1 hb; norm_num at this; linear_combination this))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_cbits 2 hr)
      (fun hb => by have := h_cidx hr 2 hb; norm_num at this; linear_combination this))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_cbits 3 hr)
      (fun hb => by have := h_cidx hr 3 hb; norm_num at this; linear_combination this))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_cbits 4 hr)
      (fun hb => by have := h_cidx hr 4 hb; norm_num at this; linear_combination this))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_cbits 5 hr)
      (fun hb => by have := h_cidx hr 5 hb; norm_num at this; linear_combination this))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_cbits 6 hr)
      (fun hb => by have := h_cidx hr 6 hb; norm_num at this; linear_combination this))
  · exact gate_zero h_rbin (fun hr => gate_zero (h_cbits 7 hr)
      (fun hb => by have := h_cidx hr 7 hb; norm_num at this; linear_combination this))
  · exact gate_zero h_rbin (fun hr => gate_zero h_cdsum (fun hc => h_cupper hr hc))
  · exact gate_zero h_rbin (fun hr => gate_zero h_cbin
      (fun hc => by linear_combination -(h_cpack hr hc).1))
  · exact gate_zero h_rbin (fun hr => gate_zero h_cbin
      (fun hc => by linear_combination -(h_cpack hr hc).2.1))
  · exact gate_zero h_rbin (fun hr => gate_zero h_cbin (fun hc => (h_cpack hr hc).2.2.1))
  · exact gate_zero h_rbin (fun hr => gate_zero h_cbin (fun hc => (h_cpack hr hc).2.2.2))
  · intro _
    exact (byteRowSpec_range (n := 16) _ (by have : (2:ℕ)^17 < p := Fact.out; omega)).mpr (h_wu64 0)
  · intro _
    exact (byteRowSpec_range (n := 16) _ (by have : (2:ℕ)^17 < p := Fact.out; omega)).mpr (h_wu64 1)
  · intro _
    exact (byteRowSpec_range (n := 16) _ (by have : (2:ℕ)^17 < p := Fact.out; omega)).mpr (h_wu64 2)
  · intro _
    exact (byteRowSpec_range (n := 16) _ (by have : (2:ℕ)^17 < p := Fact.out; omega)).mpr (h_wu64 3)
  · intro hneg
    exact (byteRowSpec_u8range_pair _ _).mpr
      ⟨h_cbytes (neg_inj.mp hneg) 0, h_cbytes (neg_inj.mp hneg) 1⟩
  · intro hneg
    exact (byteRowSpec_u8range_pair _ _).mpr
      ⟨h_cbytes (neg_inj.mp hneg) 2, h_cbytes (neg_inj.mp hneg) 3⟩
  · exact fun _ => trivial
  · exact fun _ => trivial
  · exact fun _ => trivial
  · exact fun _ => trivial
  · exact fun _ => trivial
  · exact fun _ => trivial
  · exact fun _ => trivial

/-! ## The bundled `circuit`

Not yet assembled. `soundness` and `completeness` are both closed above, but
`GeneralFormalCircuit`'s `requirementsChannelsLawful` field needs the row's leading booleanity
constraints, and reaching any constraint past the first requires `simp only [circuit_norm, main, …]`
to normalise a sixty-assertion do-block — which exceeds the heartbeat budget, and raising it is
gated (`scripts/check_option_escapes.sh`).

The fix is structural and is the same one `localLength_eq` already needed: split the arms into
bundled `FormalAssertion` subcircuits (`HaltArm`, `WriteArm`, `CommitArm`, `DispatchArm`,
`SelectorBlock`), so `main` composes about six subcircuits rather than sixty inline assertions and
each obligation is local. Clean's own guidance says as much — bundle what is a proof boundary — and
each arm is one. The emitted constraint and interaction lists are unchanged by the regrouping, so
the faithfulness anchor is unaffected.
-/


end SP1Clean.SyscallInstrsChip
