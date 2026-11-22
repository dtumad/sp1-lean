import SP1Clean.Proofs.Completeness.MixedSyscallInstruction
import SP1Clean.Math.SP1Field

/-! # Syscall instruction selectors and host-dependent arms

Successful dispatch supplies the commit slot and operand bounds for the actual active CPU
row. The two field-value arms use KoalaBear's characteristic, including its last legal word.
-/

namespace SP1Clean.TraceGen
open Machine Semantics FormalModel.Shard SyscallInstrsChip

private abbrev row (frontier : AccessFrontier) (call : CoreSyscallEvent) :=
  syscallInstruction (p := SP1Prime) frontier call

private theorem row_a (f : AccessFrontier) (c : CoreSyscallEvent) :
    (row f c).op_a_memory.prev_value = wordOfNat c.rawCode.toNat := rfl

private theorem row_id (f : AccessFrontier) (c : CoreSyscallEvent) :
    syscallId (row f c) = (c.syscallId : ZMod SP1Prime) := by
  change (((wordOfNat (p := SP1Prime) c.rawCode.toNat)[0].val % 256 : ℕ) : ZMod SP1Prime) = _
  rw [wordOfNat_zero_val, Nat.mod_mod_of_dvd _ (by decide : 256 ∣ 2 ^ 16)]
  rfl

private theorem selector_result (id code : ZMod SP1Prime) :
    (IsZeroOperation.populate (id - code)).result = (if id = code then 1 else 0) := by
  by_cases same : id = code <;> simp [IsZeroOperation.populate, sub_eq_zero, same]

private theorem selector_inverse (id code : ZMod SP1Prime) (different : id - code ≠ 0) :
    (IsZeroOperation.populate (id - code)).inverse * (id - code) = 1 := by
  simp [IsZeroOperation.populate, different]

private theorem selector_nat (c : CoreSyscallEvent) (n : ℕ) (hn : n < SP1Prime) :
    (IsZeroOperation.populate ((c.syscallId : ZMod SP1Prime) - (n : ZMod SP1Prime))).result =
      (if c.syscallId = n then 1 else 0) := by
  rw [selector_result]
  have bound : c.syscallId < SP1Prime :=
    (Nat.mod_lt _ (by decide : 0 < 256)).trans (by decide : 256 < SP1Prime)
  have equal : ((c.syscallId : ZMod SP1Prime) = (n : ZMod SP1Prime)) ↔ c.syscallId = n := by
    constructor
    · intro field
      simpa only [ZMod.val_natCast_of_lt bound, ZMod.val_natCast_of_lt hn] using congrArg ZMod.val field
    · exact fun h => congrArg Nat.cast h
  simp only [equal]

/-- Every active CPU row uses the specified five low-byte selectors and their actual inverse witnesses. -/
theorem syscallInstruction_selectors (f : AccessFrontier) (c : CoreSyscallEvent) :
    SelectorsValid (syscallInstruction (p := SP1Prime) f c) := by
  change SelectorsValid (row f c)
  refine ⟨?_, ?_, ?_, ?_, by simp [row, syscallInstruction]⟩
  · rw [row_a]
    have h := wordOfNat_isU64 (p := SP1Prime) c.rawCode.toNat
    exact U16toU8OperationSafe.spec_populate (h 0) (h 1) (h 2) (h 3) 1
  · intro _
    rw [row_id]
    exact ⟨selector_result .., selector_result .., selector_result .., selector_result .., selector_result ..⟩
  · intro _
    rw [row_id]
    exact ⟨selector_inverse _ _, selector_inverse _ _, selector_inverse _ _, selector_inverse _ _, selector_inverse _ _⟩
  · change (if c.syscallId = haltSyscallId then (1 : ZMod SP1Prime) else 0) =
      (IsZeroOperation.populate ((c.syscallId : ZMod SP1Prime) - (haltCode : ZMod SP1Prime))).result * 1
    rw [mul_one, selector_nat c haltCode (by decide)]
    rfl

private theorem word_fieldBound {n : ℕ} (bounded : n < SP1Prime) :
    ExitCodeValid (wordOfNat (p := SP1Prime) n) := by
  have small : n < 2 ^ 32 := bounded.trans (by decide : SP1Prime < 2 ^ 32)
  have small' : n < 2 ^ 48 := by omega
  have limb : n / 2 ^ 16 < 2 ^ 16 := by omega
  refine ⟨?_, wordOfNat_three_eq_zero small', ?_⟩
  · rw [wordOfNat_two, Nat.div_eq_of_lt small]
    rfl
  · rw [wordOfNat_one, Nat.mod_eq_of_lt limb, ZMod.val_natCast_of_lt (limb.trans (by decide)), wordOfNat_zero]
    change _ < 32512 ∨ _ = 32512 ∧ _ = 0
    change n < 2130706433 at bounded
    by_cases lt : n / 2 ^ 16 < 32512
    · exact Or.inl lt
    · refine Or.inr ⟨by omega, ?_⟩
      rw [show n % 2 ^ 16 = 0 by omega]
      rfl

private theorem field_arm (n : ℕ) (selected : Prop) [Decidable selected]
    (active : selected → n < SP1Prime) :
    let w := wordOfNat (p := SP1Prime) n
    let input : FieldBoundArm.Inputs (ZMod SP1Prime) := ⟨w,
      if selected then U16CompareOperation.populate_bit w[1] fieldLimbBound else 0, if selected then 1 else 0⟩
    FieldBoundArm.Assumptions input ∧ FieldBoundArm.Spec input := by
  by_cases live : selected
  · simp only [ite_eq_left live]
    exact ⟨⟨Or.inr rfl, fun _ => wordOfNat_isU64 n 1⟩, U16CompareOperation.populate_bit_bool ..,
      fun _ => ⟨rfl, word_fieldBound (active live)⟩⟩
  · simp only [ite_eq_right live]
    exact ⟨⟨Or.inl rfl, fun h => (zero_ne_one h).elim⟩, Or.inl rfl, fun h => (zero_ne_one h).elim⟩

private theorem small_index {i : ℕ} (bound : i < 8) :
    (wordOfNat (p := SP1Prime) i)[0] = (i : ZMod SP1Prime) ∧
    (wordOfNat (p := SP1Prime) i)[1] + (wordOfNat (p := SP1Prime) i)[2] +
      (wordOfNat (p := SP1Prime) i)[3] = 0 := by
  rw [wordOfNat_zero, Nat.mod_eq_of_lt (by omega), wordOfNat_one, wordOfNat_two, wordOfNat_three,
    Nat.div_eq_of_lt (show i < 2 ^ 16 by omega), Nat.div_eq_of_lt (show i < 2 ^ 32 by omega),
    Nat.div_eq_of_lt (show i < 2 ^ 48 by omega)]
  simp

private theorem packed_commit_word {n : ℕ} (bound : n < 2 ^ 32) :
    let byte (i : ℕ) := ((n / 256 ^ i % 256 : ℕ) : ZMod SP1Prime)
    (wordOfNat (p := SP1Prime) n)[0] = byte 0 + byte 1 * 256 ∧
    (wordOfNat (p := SP1Prime) n)[1] = byte 2 + byte 3 * 256 ∧
    (wordOfNat (p := SP1Prime) n)[2] = 0 ∧ (wordOfNat (p := SP1Prime) n)[3] = 0 := by
  dsimp only
  rw [wordOfNat_zero, wordOfNat_one, wordOfNat_two, Nat.div_eq_of_lt bound]
  refine ⟨?_, ?_, rfl, wordOfNat_three_eq_zero (by omega)⟩
  · have eq : n % 2 ^ 16 = n / 256 ^ 0 % 256 + n / 256 ^ 1 % 256 * 256 := by omega
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using congrArg (fun x : ℕ => (x : ZMod SP1Prime)) eq
  · have eq : n / 2 ^ 16 % 2 ^ 16 = n / 256 ^ 2 % 256 + n / 256 ^ 3 % 256 * 256 := by omega
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using congrArg (fun x : ℕ => (x : ZMod SP1Prime)) eq

private theorem bit_sum (n : ℕ) (bound : n < 8) (r : CommitArm.Inputs (ZMod SP1Prime))
    (bits : ∀ i : Fin 8, r.index_bits[i] = if i.val = n then 1 else 0) : CommitArm.bitSum r = 1 := by
  have shape : r.index_bits = Vector.ofFn (fun i : Fin 8 => if i.val = n then 1 else 0) := by
    apply Vector.ext
    intro i possible
    rw [Vector.getElem_ofFn]; exact bits ⟨i, possible⟩
  rw [CommitArm.bitSum, shape]
  interval_cases n <;> decide

private theorem flag_sum (a b : Prop) [Decidable a] [Decidable b] (exclusive : a → ¬ b) :
    (if a then (1 : ZMod SP1Prime) else 0) + (if b then 1 else 0) = if a ∨ b then 1 else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> simp_all

private theorem flag_bool (a : Prop) [Decidable a] :
    (if a then (1 : ZMod SP1Prime) else 0) = 0 ∨ (if a then (1 : ZMod SP1Prime) else 0) = 1 := by
  split <;> simp

private theorem commit_arm (f : AccessFrontier) (c : CoreSyscallEvent)
    (index : c.syscallId = commitCode ∨ c.syscallId = commitDeferredCode → c.arg1.toNat < 8)
    (value : c.syscallId = commitCode → c.arg2.toNat < 2 ^ 32) :
    let r := toCommitArm (row f c)
    CommitArm.Assumptions r ∧ CommitArm.Spec r ∧
      ((row f c).is_commit.result = 1 → ∀ i : Fin 4, (row f c).digest_word[i].val < 256) := by
  let r := toCommitArm (row f c)
  let active := c.syscallId = commitCode ∨ c.syscallId = commitDeferredCode
  have primary : r.is_commit = (if c.syscallId = commitCode then 1 else 0) := selector_nat c _ (by decide)
  have deferred : r.is_commit_deferred = (if c.syscallId = commitDeferredCode then 1 else 0) := selector_nat c _ (by decide)
  have bits (i : Fin 8) : r.index_bits[i] = (if active ∧ i.val = c.arg1.toNat then 1 else 0) := by
    change (Vector.ofFn _)[i.val] = _
    rw [Vector.getElem_ofFn]
  have on : r.is_commit + r.is_commit_deferred = if active then 1 else 0 := by
    rw [primary, deferred]
    apply flag_sum
    exact fun first second => (by decide : commitCode ≠ commitDeferredCode) (first.symm.trans second)
  have act : r.is_commit + r.is_commit_deferred = 1 ↔ active := by rw [on]; split <;> simp_all
  have pc : r.is_commit = 1 ↔ c.syscallId = commitCode := by rw [primary]; split <;> simp_all
  have getByte (h : c.syscallId = commitCode) (i : Fin 4) : r.digest_word[i] =
      ((c.arg2.toNat / 256 ^ i.val % 256 : ℕ) : ZMod SP1Prime) := by
    change ((if c.syscallId = commitCode then Vector.ofFn _ else _ : Vector (ZMod SP1Prime) 4)[i.val]) = _
    rw [ite_eq_left h, Vector.getElem_ofFn]
  change CommitArm.Assumptions r ∧ CommitArm.Spec r ∧ _
  refine ⟨⟨Or.inr rfl, ?_, ?_, fun _ => ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [primary]; split <;> simp
  · rw [deferred]; split <;> simp
  · rw [on]; split <;> simp
  · intro i _
    rw [bits]; split <;> simp
  · intro _ i selected
    rw [bits] at selected
    split at selected
    · rename_i chosen
      exact (small_index (index chosen.1)).1.trans (congrArg Nat.cast chosen.2.symm)
    · contradiction
  · intro _ enabled
    have yes := act.mp enabled
    exact bit_sum _ (index yes) r (fun i => by rw [bits]; simp [yes])
  · intro _ disabled
    have no : ¬ active := fun yes => zero_ne_one (disabled.symm.trans (act.mpr yes))
    have allZero : r.index_bits = 0 := by
      apply Vector.ext
      intro i h
      simpa [no] using bits ⟨i, h⟩
    rw [CommitArm.bitSum, allZero]
    rfl
  · intro _ enabled
    exact (small_index (index (act.mp enabled))).2
  · intro _ selected
    change r.is_commit = 1 at selected
    have selected' := pc.mp selected
    have digest : r.digest_word = Vector.ofFn (fun i : Fin 4 =>
        ((c.arg2.toNat / 256 ^ i.val % 256 : ℕ) : ZMod SP1Prime)) := by
      apply Vector.ext
      intro i h
      rw [Vector.getElem_ofFn]; exact getByte selected' ⟨i, h⟩
    rw [digest]
    exact packed_commit_word (value selected')
  · intro selected i
    change r.is_commit = 1 at selected
    change r.digest_word[i].val < 256
    have byte := Nat.mod_lt (c.arg2.toNat / 256 ^ i.val) (by decide : 0 < 256)
    rw [getByte (pc.mp selected) i, ZMod.val_natCast_of_lt (byte.trans (by decide))]
    exact byte

private theorem zero_table (f : AccessFrontier) (c : CoreSyscallEvent) (short : c.rawCode.toNat < 256) :
    tableByte (row f c) = 0 := by
  change ((row f c).op_a_memory.prev_value[0] - syscallId (row f c)) * _ = _
  rw [row_a, wordOfNat_zero, row_id, show c.syscallId = c.rawCode.toNat from Nat.mod_eq_of_lt short,
    Nat.mod_eq_of_lt (show c.rawCode.toNat < 2 ^ 16 by omega), sub_self, zero_mul]

private theorem register_arms (f : AccessFrontier) (c : CoreSyscallEvent) (short : c.rawCode.toNat < 256)
    (result : c.ResultLaw) :
    let r := row f c
    GatesBoolean r ∧
      WriteArm.Assumptions (toWriteArm r) ∧ WriteArm.Spec (toWriteArm r) ∧
      DispatchArm.Assumptions (toDispatchArm r) ∧ DispatchArm.Spec (toDispatchArm r) := by
  let r := row f c
  have enter : r.is_enter_unconstrained.result = (if c.syscallId = enterUnconstrainedCode then 1 else 0) :=
    selector_nat c _ (by decide)
  have hint : r.is_hint_len.result = (if c.syscallId = hintLenCode then 1 else 0) := selector_nat c _ (by decide)
  have sum : r.is_enter_unconstrained.result + r.is_hint_len.result =
      if c.syscallId = enterUnconstrainedCode ∨ c.syscallId = hintLenCode then 1 else 0 := by
    rw [enter, hint]
    apply flag_sum
    exact fun first second => (by decide : enterUnconstrainedCode ≠ hintLenCode) (first.symm.trans second)
  have primary : r.is_commit.result = (if c.syscallId = commitCode then 1 else 0) := selector_nat c _ (by decide)
  have deferred : r.is_commit_deferred.result = (if c.syscallId = commitDeferredCode then 1 else 0) :=
    selector_nat c _ (by decide)
  have noTable := zero_table f c short
  have enterBool : r.is_enter_unconstrained.result = 0 ∨ r.is_enter_unconstrained.result = 1 := by
    rw [enter]; exact flag_bool _
  have sumBool : r.is_enter_unconstrained.result + r.is_hint_len.result = 0 ∨
      r.is_enter_unconstrained.result + r.is_hint_len.result = 1 := by rw [sum]; exact flag_bool _
  change (if c.syscallId = enterUnconstrainedCode then c.result = 0
    else if c.syscallId = hintLenCode then True else c.result = c.rawCode) at result
  refine ⟨⟨Or.inr rfl, primary ▸ flag_bool _, deferred ▸ flag_bool _, flag_bool _, Or.inl noTable⟩,
    ⟨Or.inr rfl, Or.inl rfl, fun _ => enterBool, fun _ => sumBool⟩,
    ⟨fun _ => rfl, fun impossible => (zero_ne_one impossible).elim, ?_, ?_⟩,
    Or.inl noTable, fun impossible => (zero_ne_one (noTable.symm.trans impossible)).elim⟩
  · intro _ selected i
    change r.is_enter_unconstrained.result = 1 at selected
    rw [enter] at selected
    split at selected
    · rename_i yes
      have zero : c.result = 0 := by simpa only [ite_eq_left yes] using result
      change (wordOfNat (p := SP1Prime) c.result.toNat)[i] = 0
      rw [zero]
      fin_cases i <;> rfl
    · contradiction
  · intro _ other i
    change r.is_enter_unconstrained.result + r.is_hint_len.result = 0 at other
    rw [sum] at other
    split at other
    · contradiction
    · rename_i neither
      have same : c.result = c.rawCode := by
        simpa only [ite_eq_right (fun h => neither (Or.inl h)),
          ite_eq_right (fun h => neither (Or.inr h))] using result
      change (wordOfNat (p := SP1Prime) c.result.toNat)[i] = (wordOfNat c.rawCode.toNat)[i]
      rw [same]

private theorem host_limits {host : HostState} {context : HostReadContext} {execution : HostExecution}
    {image : ProgramImage} (ran : host.run (policy SP1Prime image) context = some execution)
    (clock : ℕ) (pc : BitVec 64) :
    let c := execution.toEvent clock pc
    c.rawCode.toNat < 256 ∧
      (c.syscallId = haltCode → c.arg1.toNat < SP1Prime) ∧
      (c.syscallId = commitCode ∨ c.syscallId = commitDeferredCode → c.arg1.toNat < 8) ∧
      (c.syscallId = commitCode → c.arg2.toNat < 2 ^ 32) ∧
      (c.syscallId = commitDeferredCode → c.arg2.toNat < SP1Prime) := by
  have performed := ((host.run_eq_some_iff ..).mp ran).2.2.2.2.2
  rcases execution with ⟨kind, arg1, arg2, value, effect⟩
  dsimp only at performed
  cases kind <;> simp [HostExecution.toEvent, CoreSyscallEvent.syscallId, SyscallKind.code,
    haltCode, commitCode, commitDeferredCode]
  all_goals
    simp only [HostState.executeKind] at performed
    split_ifs at performed
    all_goals simp_all [policy]

/-- A successful host execution supplies every selector and host-dependent arm obligation of
its CPU instruction row, including both checked public field words. -/
theorem syscallInstruction_arms_of_run {host : HostState} {context : HostReadContext} {execution : HostExecution}
    {image : ProgramImage} (ran : host.run (policy SP1Prime image) context = some execution)
    (clock : ℕ) (pc : BitVec 64) (frontier : AccessFrontier) :
    let r := syscallInstruction (p := SP1Prime) frontier (execution.toEvent clock pc)
    GatesBoolean r ∧ SelectorsValid r ∧
      WriteArm.Assumptions (toWriteArm r) ∧ WriteArm.Spec (toWriteArm r) ∧
      DispatchArm.Assumptions (toDispatchArm r) ∧ DispatchArm.Spec (toDispatchArm r) ∧
      FieldBoundArm.Assumptions (toFieldBoundB r) ∧ FieldBoundArm.Spec (toFieldBoundB r) ∧
      FieldBoundArm.Assumptions (toFieldBoundC r) ∧ FieldBoundArm.Spec (toFieldBoundC r) ∧
      CommitArm.Assumptions (toCommitArm r) ∧ CommitArm.Spec (toCommitArm r) ∧
      (r.is_commit.result = 1 → ∀ i : Fin 4, r.digest_word[i].val < 256) := by
  let c := execution.toEvent clock pc
  obtain ⟨short, halt, index, primary, deferred⟩ := host_limits ran clock pc
  have result := (execution.rowLaw ((host.run_eq_some_iff ..).mp ran).2.2.2.2.1 clock pc).2.1
  obtain ⟨gates, writeA, writeS, dispatchA, dispatchS⟩ := register_arms frontier c short result
  obtain ⟨commitA, commitS, bytes⟩ := commit_arm frontier c index primary
  have h := field_arm c.arg1.toNat (c.syscallId = haltCode) halt
  have d := field_arm c.arg2.toNat (c.syscallId = commitDeferredCode) deferred
  have dflag : (row frontier c).is_commit_deferred.result = (if c.syscallId = commitDeferredCode then 1 else 0) :=
    selector_nat c _ (by decide)
  refine ⟨gates, syscallInstruction_selectors .., writeA, writeS, dispatchA, dispatchS, h.1, h.2, ?_, ?_, commitA, commitS, bytes⟩
  · change FieldBoundArm.Assumptions (toFieldBoundC (row frontier c))
    unfold toFieldBoundC
    rw [dflag]
    exact d.1
  · change FieldBoundArm.Spec (toFieldBoundC (row frontier c))
    unfold toFieldBoundC
    rw [dflag]
    exact d.2

end SP1Clean.TraceGen
