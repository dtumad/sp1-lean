import SP1Clean.Proofs.Operations.OrdinaryObservation
import SP1Clean.Soundness.RankedGrounding
import SP1Clean.Soundness.OrdinaryStateReceipt
import SP1Clean.Semantics.Execution.SailBookkeeping
import ToClean.Air.TransitionView
import SP1Clean.Soundness.OrdinaryObservationResources
import SP1Clean.Soundness.StateCanon

/-! # Exhaustive ordinary observation histories

The existing ranked grounding theorem orders the actual consumer rows. It excludes detached
cycles and derives the complete retirement count and final raw successor PC. These are subsystem
results: the mixed ensemble must derive Byte guarantees, balance the producer receipts and
authenticate the initial/final observation states. No second execution relation is introduced.
-/

namespace SP1Clean.Soundness.OrdinaryObservation

open Circuit Air.Flat SP1Clean.OrdinaryObservation RankedGrounding
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- Binding a terminal to canonical PC limbs authenticates the numerical raw successor.
The two upper raw-limb bounds come from the State ledger. The low raw limb may carry. -/
theorem terminal_pc {input : TerminalInputs (ZMod p)} {mode : Mode}
    (valid : input.Valid mode)
    (middle : input.previous.pc[1].val < 65536) (high : input.previous.pc[2].val < 65536)
    (lowOut : input.pc[0].val < 65536) (middleOut : input.pc[1].val < 65536) :
    Semantics.pcBits input.previous.pc[0] input.previous.pc[1] input.previous.pc[2] =
      Semantics.pcBits input.pc[0] input.pc[1] input.pc[2] := by
  have primeBound := Fact.out (p := 2 ^ 25 < p)
  have one : Fact (1 < p) := ⟨by omega⟩
  have bit (x : ZMod p) (binary : IsBool x) : x.val ≤ 1 := by
    rcases binary with zero | one
    · rw [zero, ZMod.val_zero]; omega
    · rw [one, ZMod.val_one]
  have c0 := bit _ valid.1
  have c1 := bit _ valid.2.1
  have radix : (65536 : ZMod p).val = 65536 :=
    ZMod.val_natCast_of_lt (a := 65536) (by omega)
  have lowEq : input.previous.pc[0] = input.pc[0] + input.carryLow * 65536 := by
    simp [TerminalInputs.pc]
  have middleEq : input.previous.pc[1] + input.carryLow = input.pc[1] + input.carryMiddle * 65536 := by
    simp [TerminalInputs.pc]
  have low := congrArg ZMod.val lowEq
  rw [val_recombine radix (by omega)] at low
  have mid := congrArg ZMod.val middleEq
  rw [ZMod.val_add_of_lt (by omega), val_recombine radix (by omega)] at mid
  have hi : input.pc[2].val = input.previous.pc[2].val + input.carryMiddle.val :=
    ZMod.val_add_of_lt (by omega)
  unfold Semantics.pcBits
  congr 1
  omega

omit [Fact (2 ^ 25 < p)] in
/-- A canonical successor or a straight-line successor with an unpropagated low carry has
a valid terminal row. The two computed carries produce its exact canonical fields. -/
theorem terminalInput_canonical {previous : State (ZMod p)} {mode : Mode}
    (clock : TerminalSpec mode previous) (low : previous.pc[0].val < 2 * 65536)
    (middle : previous.pc[1].val < 65536) :
    (terminalInput previous).Valid mode ∧
      (terminalInput previous).pc =
        #v[((previous.pc[0].val % 65536 : ℕ) : ZMod p),
          (((previous.pc[1].val + previous.pc[0].val / 65536) % 65536 : ℕ) : ZMod p),
          ((previous.pc[2].val + (previous.pc[1].val + previous.pc[0].val / 65536) / 65536 : ℕ) : ZMod p)] := by
  let a := previous.pc[0].val
  let b := previous.pc[1].val
  let c := previous.pc[2].val
  change a < 2 * 65536 at low
  change b < 65536 at middle
  have carry (n : ℕ) (bounded : n < 2 * 65536) : IsBool ((n / 65536 : ℕ) : ZMod p) := by
    rcases (show n / 65536 = 0 ∨ n / 65536 = 1 by omega) with h | h <;> simp [h, IsBool]
  refine ⟨⟨carry a low, carry (b + a / 65536) (by omega), clock⟩, ?_⟩
  have split (n : ℕ) : (n : ZMod p) - (n / 65536 : ℕ) * 65536 = (n % 65536 : ℕ) := by
    have sum := congrArg (fun k : ℕ => (k : ZMod p)) (Nat.mod_add_div n 65536)
    push_cast at sum
    linear_combination -sum
  change #v[previous.pc[0] - (a / 65536 : ℕ) * 65536,
    previous.pc[1] + (a / 65536 : ℕ) - ((b + a / 65536) / 65536 : ℕ) * 65536,
    previous.pc[2] + ((b + a / 65536) / 65536 : ℕ)] = _
  conv_lhs =>
    rw [← ZMod.natCast_zmod_val previous.pc[0], ← ZMod.natCast_zmod_val previous.pc[1],
      ← ZMod.natCast_zmod_val previous.pc[2]]
  change #v[(a : ZMod p) - (a / 65536 : ℕ) * 65536,
    (b : ZMod p) + (a / 65536 : ℕ) - ((b + a / 65536) / 65536 : ℕ) * 65536,
    (c : ZMod p) + ((b + a / 65536) / 65536 : ℕ)] =
    #v[((a % 65536 : ℕ) : ZMod p), (((b + a / 65536) % 65536 : ℕ) : ZMod p),
      ((c + (b + a / 65536) / 65536 : ℕ) : ZMod p)]
  rw [split, ← Nat.cast_add, split, Nat.cast_add]

section

open Semantics Target

private theorem natural_digits (a b c n : ℕ) (low : a < 2 * 65536) (mid : b < 65536) (high : c < 65536)
    (bounded : n < 2 ^ 48) (numeric : (a + b * 2 ^ 16 + c * 2 ^ 32) % 2 ^ 64 = n) :
    a % 65536 = n % 65536 ∧ (b + a / 65536) % 65536 = n / 65536 % 65536 ∧
      c + (b + a / 65536) / 65536 = n / 4294967296 % 65536 := by
  rw [Nat.mod_eq_of_lt (by omega)] at numeric
  have first : n = a + (b + c * 65536) * 65536 := by omega
  have second : n / 65536 = b + a / 65536 + c * 65536 := by
    rw [first, Nat.add_mul_div_right _ _ (by decide)]
    omega
  have third : n / 4294967296 = c + (b + a / 65536) / 65536 := by
    change n / (65536 * 65536) = _
    rw [← Nat.div_div_eq_div_mul, second, Nat.add_mul_div_right _ _ (by decide), Nat.add_comm]
  refine ⟨?_, ?_, ?_⟩
  · rw [first, Nat.add_mul_mod_self_right]
  · rw [second, Nat.add_mul_mod_self_right]
  · rw [← third, Nat.mod_eq_of_lt (by omega)]

omit [Fact (2 ^ 25 < p)] in
/-- The populated terminal agrees with all three canonical target limbs whenever its raw
SP1 successor and the bounded Sail nextPC have the same numerical value. -/
theorem terminalInput_pcLimbs {previous : State (ZMod p)} {mode : Mode} {pc : BitVec 64}
    (clock : TerminalSpec mode previous)
    (low : previous.pc[0].val < 2 * 65536) (middle : previous.pc[1].val < 65536)
    (high : previous.pc[2].val < 65536) (bounded : pc.toNat < 2 ^ 48)
    (numeric : pcBits previous.pc[0] previous.pc[1] previous.pc[2] = pc) :
    (terminalInput previous).Valid mode ∧ (terminalInput previous).pc = pcLimbs pc := by
  obtain ⟨valid, normalized⟩ := terminalInput_canonical clock low middle
  refine ⟨valid, normalized.trans ?_⟩
  have total := congrArg BitVec.toNat numeric
  simp only [pcBits, BitVec.toNat_ofNat] at total
  obtain ⟨d0, d1, d2⟩ := natural_digits previous.pc[0].val previous.pc[1].val previous.pc[2].val pc.toNat
    low middle high bounded total
  unfold pcLimbs bitVecToWord
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  change #v[((previous.pc[0].val % 65536 : ℕ) : ZMod p),
    (((previous.pc[1].val + previous.pc[0].val / 65536) % 65536 : ℕ) : ZMod p),
    ((previous.pc[2].val + (previous.pc[1].val + previous.pc[0].val / 65536) / 65536 : ℕ) : ZMod p)] =
    #v[((pc.toNat % 65536 : ℕ) : ZMod p), ((pc.toNat / 65536 % 65536 : ℕ) : ZMod p),
      ((pc.toNat / 4294967296 % 65536 : ℕ) : ZMod p)]
  rw [d0, d1, d2]

/-- A present bounded Sail nextPC is determined by the three canonical State-bus limbs. -/
theorem pcLimbs_bits (pc : BitVec 64) (bounded : pc.toNat < 2 ^ 48) :
    let limbs := pcLimbs (p := p) pc
    pcBits limbs[0] limbs[1] limbs[2] = pc := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  have fits (shift : ℕ) : (BitVec.extractLsb' shift 16 pc).toNat < p :=
    lt_trans (BitVec.extractLsb' shift 16 pc).isLt (by omega)
  apply BitVec.toNat_inj.mp
  dsimp only [pcLimbs, bitVecToWord, pcBits, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, BitVec.toNat_ofNat]
  rw [ZMod.val_natCast_of_lt (fits 0), ZMod.val_natCast_of_lt (fits 16), ZMod.val_natCast_of_lt (fits 32)]
  simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  omega

/-- Normalized terminal limbs at a bounded target bind the raw successor as a 64-bit PC. -/
theorem terminal_nextPC {input : TerminalInputs (ZMod p)} {mode : Mode} {pc : BitVec 64}
    (valid : input.Valid mode)
    (middle : input.previous.pc[1].val < 65536) (high : input.previous.pc[2].val < 65536)
    (bounded : pc.toNat < 2 ^ 48) (outgoing : input.pc = pcLimbs pc) :
    pcBits input.previous.pc[0] input.previous.pc[1] input.previous.pc[2] = pc := by
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
  have limbs := isU64_bitVecToWord (p := p) pc
  have same := terminal_pc valid middle high (by rw [outgoing]; exact limbs 0) (by rw [outgoing]; exact limbs 1)
  rw [outgoing] at same
  exact same.trans (pcLimbs_bits pc bounded)

omit [Fact (2 ^ 25 < p)] in
/-- The terminal clock selects the source-preserving or refreshed target checks. -/
theorem terminal_bookkeeping {source target : SailSnapshot} {input : TerminalInputs (ZMod p)}
    (accepted : quiet source target = true ∨ refreshed source target = true)
    (valid : input.Valid (Mode.of source target)) :
    (input.previous.clkHigh = 0 ∧ input.previous.clkLow = 0 → quiet source target = true) ∧
    (¬ (input.previous.clkHigh = 0 ∧ input.previous.clkLow = 0) → refreshed source target = true) := by
  have selected := valid.2.2.2.2
  cases q : quiet source target <;> cases r : refreshed source target <;>
    simp_all only [Mode.of, Bool.false_eq_true, true_or, or_true, false_or, imp_false, not_not,
      implies_true, and_true]


/-- The full target nextPC is the incoming register on an empty chain, or the numerical
successor of the last ordinary receipt on a nonempty chain. -/
theorem terminal_nextPC_entry {source target : SailSnapshot} {input : TerminalInputs (ZMod p)}
    (accepted : quiet source target = true ∨ refreshed source target = true)
    (valid : input.Valid (Mode.of source target))
    (middle : input.previous.pc[1].val < 65536) (high : input.previous.pc[2].val < 65536)
    (outgoing : input.pc = (finalFor source target).pc) :
    target.registers.get? LeanRV64D.Register.nextPC =
      if input.previous.clkHigh = 0 ∧ input.previous.clkLow = 0 then
        source.registers.get? LeanRV64D.Register.nextPC
      else some (pcBits input.previous.pc[0] input.previous.pc[1] input.previous.pc[2]) := by
  obtain ⟨empty, nonempty⟩ := terminal_bookkeeping accepted valid
  split
  next zero => exact ((quiet_iff ..).mp (empty zero)).2.2.2
  next active =>
    obtain ⟨pc, present, bounded⟩ := ((refreshed_iff ..).mp (nonempty active)).2.2.2
    have limbs : input.pc = pcLimbs pc := by
      simpa only [finalFor, final, present, Option.getD_some] using outgoing
    exact present.trans (congrArg some (terminal_nextPC valid middle high bounded limbs).symm)

omit [Fact (2 ^ 25 < p)] in
/-- The selected terminal clock also determines the three Sail retirement bookkeeping entries
that do not ride as field cells on the observation channel. -/
theorem terminal_retirement_entries {source target : SailSnapshot} {input : TerminalInputs (ZMod p)}
    (accepted : quiet source target = true ∨ refreshed source target = true)
    (valid : input.Valid (Mode.of source target)) :
    let zero := input.previous.clkHigh = 0 ∧ input.previous.clkLow = 0
    target.registers.get? LeanRV64D.Register.minstret_increment =
      (if zero then source.registers.get? LeanRV64D.Register.minstret_increment else some (retirementEnabled source.realize)) ∧
    target.registers.get? LeanRV64D.Register.mip =
      (if zero then source.registers.get? LeanRV64D.Register.mip else some (TryStepReduction.refreshedMip source.realize)) ∧
    target.registers.get? LeanRV64D.Register.written_event_index =
      (if zero then source.registers.get? LeanRV64D.Register.written_event_index else some none) := by
  obtain ⟨empty, nonempty⟩ := terminal_bookkeeping accepted valid
  by_cases zero : input.previous.clkHigh = 0 ∧ input.previous.clkLow = 0
  · obtain ⟨flag, interrupts, index, _⟩ := (quiet_iff ..).mp (empty zero)
    simpa only [ite_eq_left zero] using And.intro flag (And.intro interrupts index)
  · obtain ⟨flag, interrupts, index, _⟩ := (refreshed_iff ..).mp (nonempty zero)
    have sameFlag : retirementEnabled source.skeleton = retirementEnabled source.realize := by unfold retirementEnabled; rfl
    have sameMip : TryStepReduction.refreshedMip source.skeleton = TryStepReduction.refreshedMip source.realize := by
      unfold TryStepReduction.refreshedMip; rfl
    rw [sameFlag] at flag
    rw [sameMip] at interrupts
    simpa only [ite_eq_right zero] using And.intro flag (And.intro interrupts index)

end

/-- Match the field equality used by Clean's gated balance filters. -/
local instance cleanBalanceDecidableEq : DecidableEq (ZMod p) := FiniteField.instDecidableEq

/-- The installed component exposes its actual row activity and physical transition. -/
def view : TransitionView (stateChannel (p := p)) where
  component := consumer
  activity := (varFromOffset RowInput 0).2
  edge env :=
    let input := (valueFromOffset RowInput 0 env).1
    (input.previous, input.next)
  activity_binary := by
    intro env valid
    rw [Guarded.eval_activity, eval_varFromOffset_valueFromOffset]
    exact valid.1
  activity_of_constraints := by
    intro env valid
    rw [Component.constraintsHold_iff] at valid
    exact Guarded.activity_of_constraints circuit guardSupported (varFromOffset RowInput 0) (size RowInput) env valid
  interactions := by
    intro env
    rw [Guarded.eval_activity, eval_varFromOffset_valueFromOffset]
    exact guarded_state_values env

/-- Decode every physical input, including its activity. -/
def rows (table : Table (ZMod p)) (data : ProverData (ZMod p)) : List (RowInput (ZMod p)) :=
  table.table.map (fun physical => valueFromOffset RowInput 0 (Environment.fromArray physical data))

/-- Only live observation inputs participate in the chronological execution history. -/
def activeRows (table : Table (ZMod p)) (data : ProverData (ZMod p)) : List (Inputs (ZMod p)) :=
  ((rows table data).filter fun row => decide (row.2 = 1)).map Prod.fst

/-- A row links the previous observation to the exact receipt and computed counter. -/
def edge (input : Inputs (ZMod p)) : State (ZMod p) × State (ZMod p) :=
  (input.previous, input.next)

/-- The natural source clock ranks the observation history. -/
def rank (state : State (ZMod p)) : ℕ := Semantics.clkNat state.clkHigh state.clkLow

omit [Fact (2 ^ 25 < p)] in
private theorem row_data (table : Table (ZMod p)) (data : ProverData (ZMod p)) (physical : Array (ZMod p)) :
    valueFromOffset RowInput 0 (table.environment physical) =
      valueFromOffset RowInput 0 (Environment.fromArray physical data) :=
  ProvableType.valueFromOffset_congr _ _ (fun _ _ => rfl)

/-- Every physical consumer, including padding, retains its weighted receipt occurrence. -/
theorem receipt_ledger (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (registered : table.component = consumer) :
    table.interactionsWith InstructionReceipt.channel.toRaw =
      (rows table data).map (fun row => InstructionReceipt.channel.pulledIfValue row.2 row.1.receipt) := by
  simp only [Table.interactionsWith, registered, consumer, guarded_receipt_values, rows, List.map_map,
    row_data table data]
  exact List.map_eq_flatMap.symm

/-- The physical observation ledger retains both link occurrences even on a padding row. -/
theorem state_ledger (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (registered : table.component = consumer) :
    table.interactionsWith stateChannel.toRaw = (rows table data).flatMap (fun row =>
      [stateChannel.pulledIfValue row.2 row.1.previous, stateChannel.pushedIfValue row.2 row.1.next]) := by
  simp only [Table.interactionsWith, registered, consumer, guarded_state_values, rows, List.flatMap_map,
    row_data table data]

/-- Each physical row contributes to the receipt count bound. -/
theorem receipt_count (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (registered : table.component = consumer) :
    (table.interactionsWith InstructionReceipt.channel.toRaw).length = table.length := by
  rw [receipt_ledger table data registered]
  simp only [rows, List.length_map]

/-- Every consumer contributes two physical observation-channel occurrences. -/
theorem state_count (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (registered : table.component = consumer) :
    (table.interactionsWith stateChannel.toRaw).length = 2 * table.length := by
  rw [state_ledger table data registered, List.length_flatMap]
  simp [rows, Function.comp_def, List.sum_replicate, Nat.mul_comm]

/-- The raw table specification gives Boolean activity and the meaning of each live input. -/
theorem rows_spec (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (registered : table.component = consumer) (valid : table.Spec) :
    ∀ row ∈ rows table data, IsBool row.2 ∧ (row.2 = 1 → Spec row.1) := by
  intro row member
  change row ∈ table.table.map (fun physical => valueFromOffset RowInput 0 (Environment.fromArray physical data)) at member
  obtain ⟨physical, inTable, rfl⟩ := List.mem_map.mp member
  rw [← row_data table data physical]
  have result := valid physical inTable
  rw [registered] at result
  exact result

/-- Balanced gated producers and consumers agree exactly on their active messages. -/
theorem receipts_exact (id : InstructionChipId) (original observed : Table (ZMod p))
    (data : ProverData (ZMod p))
    (source : original.component = (supportedChipFor id).table)
    (registered : observed.component = consumer) (valid : observed.Spec)
    (binary : ∀ physical ∈ original.table,
      ((supportedChipFor (p := p) id).decodeRow data physical).is_real = 0 ∨
        ((supportedChipFor (p := p) id).decodeRow data physical).is_real = 1)
    (balanced : BalancedInteractions
      ((OrdinaryStateReceipt.construct id original source).interactionsWith InstructionReceipt.channel.toRaw ++
        observed.interactionsWith InstructionReceipt.channel.toRaw)) :
    ((original.table.filter (fun physical => decide
      (((supportedChipFor (p := p) id).decodeRow data physical).is_real = 1))).map
        (fun physical => statePushMessage ((supportedChipFor (p := p) id).decodeRow data physical))).Perm
      ((activeRows observed data).map Inputs.receipt) := by
  rw [OrdinaryStateReceipt.construct_receipts, receipt_ledger observed data registered] at balanced
  simpa only [activeRows, List.map_map, Function.comp_def] using
    InstructionReceipt.channel.gated_perm_of_balanced original.table
      (fun physical => ((supportedChipFor (p := p) id).decodeRow data physical).is_real)
      (fun physical => statePushMessage ((supportedChipFor (p := p) id).decodeRow data physical))
      (rows observed data) Prod.snd (fun row => row.1.receipt) binary
      (fun row member => (rows_spec observed data registered valid row member).1) balanced

omit [Fact (2 ^ 25 < p)] in
private theorem counter_of_walk (initial final : State (ZMod p))
    (path : List (Inputs (ZMod p))) (valid : ∀ input ∈ path, Spec input)
    (walk : Walk.IsWalk edge initial final path) :
    final.enabled = initial.enabled ∧
      Word.toBitVec64 final.counter =
        Word.toBitVec64 initial.counter + BitVec.ofNat 64 (path.length * initial.enabled.val) := by
  induction path generalizing initial with
  | nil =>
    change initial = final at walk
    subst final
    simp
  | cons input rest ih =>
    obtain ⟨source, tail⟩ := walk
    change input.previous = initial at source
    subst source
    have step := (valid input (List.mem_cons_self ..)).2.2.2.2
    obtain ⟨flag, counter⟩ := ih input.next (fun row member => valid row (List.mem_cons_of_mem _ member)) tail
    refine ⟨flag, ?_⟩
    rw [counter]
    change Word.toBitVec64 input.counter + BitVec.ofNat 64 (rest.length * input.previous.enabled.val) = _
    rw [step, BitVec.add_assoc, ← BitVec.ofNat_add, List.length_cons, Nat.succ_mul, Nat.add_comm]

omit [Fact (2 ^ 25 < p)] in
private theorem pc_of_walk (initial final : State (ZMod p)) (path : List (Inputs (ZMod p)))
    (walk : Walk.IsWalk edge initial final path) :
    final.pc = path.foldl (fun _ input => input.next.pc) initial.pc := by
  induction path generalizing initial with
  | nil => exact congrArg State.pc walk.symm
  | cons input rest ih =>
    exact ih input.next walk.2

/-- Raw observation balance and local table meaning force one exhaustive ordered history.
The endpoint parameters are an installation boundary, not capstone caller premises. -/
theorem ordered_history (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (registered : table.component = consumer) (valid : table.Spec)
    (initial final : State (ZMod p))
    (balanced : BalancedInteractions
      ([stateChannel.pushedValue initial, stateChannel.pulledValue final] ++
        table.interactionsWith stateChannel.toRaw)) :
    ∃ path : List (Inputs (ZMod p)), path.Perm (activeRows table data) ∧
      Walk.IsWalk edge initial final path ∧
      (path.map (fun input => rank input.next)).Pairwise (· < ·) ∧
      final.enabled = initial.enabled ∧
      Word.toBitVec64 final.counter =
        Word.toBitVec64 initial.counter + BitVec.ofNat 64 ((activeRows table data).length * initial.enabled.val) ∧
      final.pc = path.foldl (fun _ input => input.next.pc) initial.pc := by
  rw [state_ledger table data registered] at balanced
  have physical := rows_spec table data registered valid
  have endpoints := (stateChannel.gatedTransitionLedger_balanced_iff initial final
    (rows table data) Prod.snd (fun row => edge row.1)
    (fun row member => (physical row member).1)).mp balanced
  have endpointBalance : EndpointBalanced (↑(activeRows table data)) edge initial final := by
    simpa only [EndpointBalanced, activeRows, Multiset.map_coe, Multiset.cons_coe,
      Multiset.coe_eq_coe, List.map_map, Function.comp_def] using endpoints
  have specs (input) (member : input ∈ activeRows table data) : Spec input := by
    obtain ⟨row, included, rfl⟩ := List.mem_map.mp member
    obtain ⟨actual, active⟩ := List.mem_filter.mp included
    exact (physical row actual).2 (of_decide_eq_true active)
  have strict : ∀ input ∈ activeRows table data, rank input.previous < rank input.next :=
    fun input member => (specs input member).1.2.2.2.2
  obtain ⟨path, walk, exhaustive⟩ := exists_exhaustiveTrail_of_endpointBalanced
    (↑(activeRows table data)) edge rank initial final endpointBalance
    (fun input member => strict input (Multiset.mem_coe.mp member))
  have perm := Multiset.coe_eq_coe.mp exhaustive
  have pathSpecs := fun input member => specs input (perm.mem_iff.mp member)
  obtain ⟨flag, counter⟩ := counter_of_walk initial final path pathSpecs walk
  refine ⟨path, perm, walk, ?_, flag, by rwa [← perm.length_eq], pc_of_walk initial final path walk⟩
  exact targetRanks_pairwise_of_isWalk edge rank walk
    (fun input member => strict input (perm.mem_iff.mp member))

omit [Fact (2 ^ 25 < p)] in
/-- Counter observations agree with the existing semantic retirement fold, including inhibition,
when the chain's flag denotes the semantic retirement flag. An empty ordinary history leaves the
supplied incoming increment flag untouched. -/
theorem retirement_fold (initial final : State (ZMod p)) (path : List (Inputs (ZMod p)))
    (flag : Option Bool) (valid : ∀ input ∈ path, Spec input) (walk : Walk.IsWalk edge initial final path)
    (enabled : Bool) (denotes : initial.enabled.val = if enabled then 1 else 0) :
    path.foldl (fun values _ => Semantics.retirementTick values true)
      (enabled, flag, some (Word.toBitVec64 initial.counter)) =
        (enabled, if path.length = 0 then flag else some enabled, some (Word.toBitVec64 final.counter)) := by
  rw [Semantics.retirementTick_fold (fun _ : Inputs (ZMod p) => true)]
  simp only [List.countP_true, Option.map_some]
  rw [(counter_of_walk initial final path valid walk).2, denotes]
  cases enabled <;> simp

end SP1Clean.Soundness.OrdinaryObservation
