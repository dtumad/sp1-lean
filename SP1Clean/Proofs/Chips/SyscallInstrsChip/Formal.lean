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
  obtain ⟨h_gate, h_cbool, h_dbool, h_hbool, h_tbool, -, -, h_ize, h_izl, h_izc, h_izd, -, -,
    h_padh, h_padd,
    h_cpu, h_raca, h_racb, h_racc, h_prog, h_ma, h_mb, h_mc,
    h_write, h_pc, h_disp, h_fbb, h_fbc, h_commit, h_ba0, h_ba1, h_ba2, h_ba3, -⟩ :=
    h_holds
  have h_rbin := bool_of_mul_pred h_gate
  have h_cbin := bool_of_mul_pred h_cbool
  have h_dbin := bool_of_mul_pred h_dbool
  have h_hbin := bool_of_mul_pred h_hbool
  have eoa0 : Expression.eval env input_var_op_a_memory_prev_value[0]
      = input_op_a_memory_prev_value[0] := by
    have := congrArg (fun v => v[0]'(by norm_num)) h_input.2.2.1.1; simpa using this
  have esb0 : Expression.eval env input_var_syscall_id_bytes_low_bytes[0]
      = input_syscall_id_bytes_low_bytes[0] := by
    have := congrArg (fun v => v[0]'(by norm_num)) h_input.2.2.2.2.2.2.2.2.2.2.2.1
    simpa using this
  -- The arm sees the row's own expression; `GatesBoolean` states it over the decoded fields.
  have h_tbinE := bool_of_mul_pred h_tbool
  rw [eoa0, esb0] at h_tbool
  have h_tbin := bool_of_mul_pred h_tbool
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec (h_cpu h_rbin)
  have eav : ∀ i (hi : i < 4),
      Expression.eval env input_var_op_a_value[i] = input_op_a_value[i] := by
    intro i hi
    have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.2.2.2.2.2.1
    simpa using this
  have avU64 : (-input_is_real : ZMod p) = -1 → Word.isU64 input_op_a_value := by
    intro hneg
    have hp : (2 : ℕ) ^ 17 < p := Fact.out
    refine Word.isU64_of_cases ?_ ?_ ?_ ?_
    · have := h_ba0 hneg; rw [eav 0 (by norm_num)] at this
      exact (byteRowSpec_range (n := 16) _ (by omega)).mp this
    · have := h_ba1 hneg; rw [eav 1 (by norm_num)] at this
      exact (byteRowSpec_range (n := 16) _ (by omega)).mp this
    · have := h_ba2 hneg; rw [eav 2 (by norm_num)] at this
      exact (byteRowSpec_range (n := 16) _ (by omega)).mp this
    · have := h_ba3 hneg; rw [eav 3 (by norm_num)] at this
      exact (byteRowSpec_range (n := 16) _ (by omega)).mp this
  have hrealHalt : input_is_halt = 1 → (-input_is_real : ZMod p) = -1 := by
    intro hh
    rw [hh, mul_one] at h_padh
    have hr : input_is_real = 1 := by linear_combination h_padh
    rw [hr]
  have hrealDef : input_is_commit_deferred_result = 1 → (-input_is_real : ZMod p) = -1 := by
    intro hd
    rw [hd, mul_one] at h_padd
    have hr : input_is_real = 1 := by linear_combination h_padd
    rw [hr]
  -- Two selectors cannot both fire: one identifier cannot equal two distinct codes.
  have distinct : ∀ c d : ℕ, c < 2 ^ 17 → d < 2 ^ 17 → c ≠ d →
      Expression.eval env input_var_syscall_id_bytes_low_bytes[0] - ((c : ℕ) : ZMod p) = 0 →
      Expression.eval env input_var_syscall_id_bytes_low_bytes[0] - ((d : ℕ) : ZMod p) = 0 →
      False := by
    intro c d hc hd hne h1 h2
    have hp : (2 : ℕ) ^ 17 < p := Fact.out
    have hcd : ((c : ℕ) : ZMod p) = ((d : ℕ) : ZMod p) := by linear_combination h2 - h1
    have := congrArg ZMod.val hcd
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at this
    exact hne this
  -- Each selector is the indicator of its code, so it is boolean and at most one fires.
  have indicator : ∀ (res : ZMod p) (c : ℕ),
      res = (if Expression.eval env input_var_syscall_id_bytes_low_bytes[0]
              - ((c : ℕ) : ZMod p) = 0 then 1 else 0) →
      (res = 0 ∨ res = 1) := by
    intro res c h
    by_cases hz : Expression.eval env input_var_syscall_id_bytes_low_bytes[0]
        - ((c : ℕ) : ZMod p) = 0
    · exact Or.inr (by rw [h, if_pos hz])
    · exact Or.inl (by rw [h, if_neg hz])
  have pairSum : ∀ (r1 r2 : ZMod p) (c d : ℕ), c < 2 ^ 17 → d < 2 ^ 17 → c ≠ d →
      r1 = (if Expression.eval env input_var_syscall_id_bytes_low_bytes[0]
              - ((c : ℕ) : ZMod p) = 0 then 1 else 0) →
      r2 = (if Expression.eval env input_var_syscall_id_bytes_low_bytes[0]
              - ((d : ℕ) : ZMod p) = 0 then 1 else 0) →
      (r1 + r2 = 0 ∨ r1 + r2 = 1) := by
    intro r1 r2 c d hc hd hne h1 h2
    by_cases hz1 : Expression.eval env input_var_syscall_id_bytes_low_bytes[0]
        - ((c : ℕ) : ZMod p) = 0
    · by_cases hz2 : Expression.eval env input_var_syscall_id_bytes_low_bytes[0]
          - ((d : ℕ) : ZMod p) = 0
      · exact absurd (distinct c d hc hd hne hz1 hz2) not_false
      · exact Or.inr (by rw [h1, h2, if_pos hz1, if_neg hz2]; ring)
    · by_cases hz2 : Expression.eval env input_var_syscall_id_bytes_low_bytes[0]
          - ((d : ℕ) : ZMod p) = 0
      · exact Or.inr (by rw [h1, h2, if_neg hz1, if_pos hz2]; ring)
      · exact Or.inl (by rw [h1, h2, if_neg hz1, if_neg hz2]; ring)
  have h_ebin : input_is_real = 1 →
      (input_is_enter_unconstrained_result = 0 ∨ input_is_enter_unconstrained_result = 1) :=
    fun hr => indicator _ enterUnconstrainedCode ((h_ize h_rbin) hr).1
  have h_ehsum : input_is_real = 1 →
      (input_is_enter_unconstrained_result + input_is_hint_len_result = 0 ∨
        input_is_enter_unconstrained_result + input_is_hint_len_result = 1) :=
    fun hr => pairSum _ _ enterUnconstrainedCode hintLenCode (by norm_num [enterUnconstrainedCode])
      (by norm_num [hintLenCode]) (by norm_num [enterUnconstrainedCode, hintLenCode])
      ((h_ize h_rbin) hr).1 ((h_izl h_rbin) hr).1
  have h_sum : input_is_real = 1 →
      (input_is_commit_result + input_is_commit_deferred_result = 0 ∨
        input_is_commit_result + input_is_commit_deferred_result = 1) :=
    fun hr => pairSum _ _ commitCode commitDeferredCode (by norm_num [commitCode])
      (by norm_num [commitDeferredCode]) (by norm_num [commitCode, commitDeferredCode])
      ((h_izc h_rbin) hr).1 ((h_izd h_rbin) hr).1
  refine ⟨⟨⟨h_rbin, h_cbin, h_dbin, h_hbin, h_tbin⟩, h_cpu h_rbin, h_raca h_rbin,
    h_racb h_rbin, h_racc h_rbin, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro ha0
    exact h_write ⟨h_rbin, ha0, h_ebin, h_ehsum⟩
  · exact h_pc ⟨h_rbin, h_hbin⟩
  · have hd := h_disp h_tbinE
    simp only [eoa0, esb0] at hd
    exact hd
  · exact h_fbb ⟨h_hbin, fun hh => (h_mb (hrealHalt hh)).1 1⟩
  · exact h_fbc ⟨h_dbin, fun hd => (h_mc (hrealDef hd)).1 1⟩
  · exact h_commit ⟨h_rbin, h_cbin, h_dbin, h_sum⟩
  · and_intros <;>
      first
        | exact Or.inl rfl
        | exact Or.inr h_rbin
        | exact fun _ _ => trivial
        | exact fun h1 h0 => off_gate_vacuous h_rbin h1 h0
        | exact fun h1 h0 => off_gate_vacuous h_cbin h1 h0
        | (intro _ h0
           have hr : input_is_real = 1 := h_rbin.resolve_left h0
           have hneg : (-input_is_real : ZMod p) = -1 := by rw [hr]
           refine ⟨?_, ?_⟩
           · first
               | exact (h_ma hneg).1
               | exact (h_mb hneg).1
               | exact (h_mc hneg).1
               | exact avU64 hneg
           · first
               | exact h_clk.at_four hr
               | exact h_clk.at_three hr
               | exact h_clk.at_two hr)

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
