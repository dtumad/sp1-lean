import SP1Clean.Export.WriteGeneratedRegisterSources

/-! # Split clocks on generated ordinary instruction receipts

The original exposed pull expressions select their register timestamp columns or the actual
RAM predecessor. Their four clock limbs fit the counted supply on both active and padded rows.
-/

namespace SP1Clean.Export.WriteSourceRegistry

open Circuit Air.Flat Channels Soundness Machine Semantics TraceGen FormalModel.Shard
open WriteProbe WriteProbe.AccessInventory

private abbrev F := ZMod SP1Prime
private abbrev installed := ProtectedOrdinaryReceipt.component (p := SP1Prime)

private theorem small_cast {n : ℕ} (fits : n < 2 ^ 24) : (n : F).val < 2 ^ 24 := by
  have prime := Fact.out (p := 2 ^ 24 < SP1Prime)
  rwa [ZMod.val_natCast_of_lt (by omega)]

private theorem cpu_high (clock pc : ℕ) (fits : clock < 2 ^ 48) :
    (cpuStateCols (p := SP1Prime) clock pc).clk_high.val < 2 ^ 24 := by
  rw [cpuStateCols_clk_high, Nat.shiftRight_eq_div_pow]
  exact small_cast (by omega)

private theorem cpu_low (clock pc : ℕ) :
    let s := cpuStateCols (p := SP1Prime) clock pc
    (s.clk_0_16 + s.clk_16_24 * 65536).val < 2 ^ 24 := by
  dsimp only
  rw [clkLow_eq]
  exact small_cast (Nat.mod_lt _ (by decide))

private theorem register_low (value prev curr : ℕ) :
    (registerAccessCols (p := SP1Prime) value prev curr).access_timestamp.prev_low.val < 2 ^ 24 := by
  change ((prevLowOf prev curr : ℕ) : F).val < _
  apply small_cast
  unfold prevLowOf
  split <;> omega

private theorem alu_c_low (e : ALUTypeEvent) :
    (aluTypeOpCCols (p := SP1Prime) e).access_timestamp.prev_low.val < 2 ^ 24 := by
  unfold aluTypeOpCCols
  split
  · exact small_cast (n := 0) (by decide)
  · exact register_low _ _ _

private theorem ram_high (value prev curr : ℕ) (fits : prev < 2 ^ 48) :
    (memoryAccessCols (p := SP1Prime) value prev curr).access_timestamp.prev_high.val < 2 ^ 24 := by
  rw [memoryAccessCols_prev_high, Nat.shiftRight_eq_div_pow]
  exact small_cast (by omega)

private theorem ram_low (value prev curr : ℕ) :
    (memoryAccessCols (p := SP1Prime) value prev curr).access_timestamp.prev_low.val < 2 ^ 24 := by
  rw [memoryAccessCols_prev_low]
  exact small_cast (Nat.mod_lt _ (by decide))

/-- Normalize only the four clocks of each original Memory pull. The chip's actual declarations
determine which timestamp columns occur and in what order, including inactive sites. -/
local macro "exposeClocks " chip:ident : tactic => do
  let name := chip.getId
  let ty := Lean.mkIdent (name ++ `Inputs)
  let exposure := Lean.mkIdent (name ++ `exposedMemoryInteractions)
  let env := Lean.mkIdent `env
  let decoded := Lean.mkIdent `decoded
  let native := Lean.mkIdent `native
  `(tactic| (
    let sym := varFromOffset (F := F) $ty 0
    let layout : AccessSupply.Layout SP1Prime $ty := ⟨$exposure, fun v => cpuStatePullMessage v.state⟩
    change ∀ pair ∈ (layout.pulls sym (size $ty)).map (fun i =>
      ($env i.mult, AccessSupply.readback (eval $env (cpuStatePullMessage sym.state)) (eval $env i.msg))), Counted.Bounded pair.2
    first
    | change ∀ pair : F × Readback F, pair ∈ [_, _, _] → Counted.Bounded pair.2
    | change ∀ pair : F × Readback F, pair ∈ [_, _] → Counted.Bounded pair.2
    | change ∀ pair : F × Readback F, pair ∈ [_] → Counted.Bounded pair.2
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    simp only [Counted.Bounded, AccessSupply.readback, AccessSupply.atClock, cpuStatePullMessage, Channel.pulledIf, circuit_norm]
    have full : ProvableStruct.eval $env (varFromOffset (F := F) $ty 0) = $native :=
      (ProvableStruct.eval_eq_eval ..).symm.trans ((eval_varFromOffset_valueFromOffset $ty 0 $env).trans $decoded)
    simp only [sym, full]
    ))

/-- The actual physically built input carries all source bounds, including disabled sites whose
register-immediate slots are explicitly zeroed by the released compiler. -/
private def InputBounded (id : InstructionChipId) : Prop :=
  ∀ (env : Environment F) (native : (installed id).Input F),
    (installed id).rowInput env = native →
    (native = InstalledInstructionTables.paddingInput id ∨ ∃ e : id.Event,
      id.Valid e ∧ (RoutedEvent.mk id e).clock < 2 ^ 48 ∧ native = InstalledInstructionTables.activeInput id e) →
    ∀ pair ∈ rowRecords (.ordinary id) env, Counted.Bounded pair.2

/-- Discharge each actual encoded limb after projecting the installed row to its native input. -/
local macro "checkInputClocks " chip:ident : tactic => do
  let env := Lean.mkIdent `env
  let native := Lean.mkIdent `native
  let decoded := Lean.mkIdent `decoded
  `(tactic| (
    intro $env $native $decoded origin
    exposeClocks $chip
    rcases origin with disabled | ⟨e, valid, fits, built⟩
    · rw [disabled]
      repeat' apply And.intro
      all_goals decide +kernel
    · rw [built]
      repeat' apply And.intro
      all_goals first
      | exact cpu_high e.clk e.pc fits
      | exact cpu_low e.clk e.pc
      | exact alu_c_low e
      | exact register_low e.prevA e.prevTsA (e.clk + 4)
      | exact register_low e.b e.prevTsB (e.clk + 3)
      | exact register_low e.c e.prevTsC (e.clk + 2)
      | exact ram_low e.prevMem e.prevTsMem (e.clk + 1)
      | exact ram_high e.prevMem e.prevTsMem (e.clk + 1) ((Nat.le_of_lt_succ valid.1.prevTsMem_lt).trans_lt fits)
      | exact ram_high e.prevMem e.prevTsMem (e.clk + 1) ((Nat.le_of_lt_succ valid.prevTsMem_lt).trans_lt fits)
    ))

private theorem addBounded : InputBounded .add := by checkInputClocks AddChip
private theorem addiBounded : InputBounded .addi := by checkInputClocks AddiChip
private theorem addwBounded : InputBounded .addw := by checkInputClocks AddwChip
private theorem subBounded : InputBounded .sub := by checkInputClocks SubChip
private theorem subwBounded : InputBounded .subw := by checkInputClocks SubwChip
private theorem bitwiseBounded : InputBounded .bitwise := by checkInputClocks BitwiseChip
private theorem ltBounded : InputBounded .lt := by checkInputClocks LtChip
private theorem shiftLeftBounded : InputBounded .shiftLeft := by checkInputClocks ShiftLeftChip
private theorem shiftRightBounded : InputBounded .shiftRight := by checkInputClocks ShiftRightChip
private theorem jalBounded : InputBounded .jal := by checkInputClocks JalChip
private theorem jalrBounded : InputBounded .jalr := by checkInputClocks JalrChip
private theorem branchBounded : InputBounded .branch := by checkInputClocks BranchChip
private theorem uTypeBounded : InputBounded .uType := by checkInputClocks UTypeChip
private theorem loadByteBounded : InputBounded .loadByte := by checkInputClocks LoadByteChip
private theorem loadHalfBounded : InputBounded .loadHalf := by checkInputClocks LoadHalfChip
private theorem loadWordBounded : InputBounded .loadWord := by checkInputClocks LoadWordChip
private theorem loadDoubleBounded : InputBounded .loadDouble := by checkInputClocks LoadDoubleChip
private theorem loadX0Bounded : InputBounded .loadX0 := by checkInputClocks LoadX0Chip
private theorem storeByteBounded : InputBounded .storeByte := by checkInputClocks StoreByteChip
private theorem storeHalfBounded : InputBounded .storeHalf := by checkInputClocks StoreHalfChip
private theorem storeWordBounded : InputBounded .storeWord := by checkInputClocks StoreWordChip
private theorem storeDoubleBounded : InputBounded .storeDouble := by checkInputClocks StoreDoubleChip
private theorem mulBounded : InputBounded .mul := by checkInputClocks MulChip
private theorem divRemBounded : InputBounded .divRem := by checkInputClocks DivRemChip
private theorem aluX0Bounded : InputBounded .aluX0 := by checkInputClocks AluX0Chip

private theorem input_bounded (id : InstructionChipId) : InputBounded id := by
  cases id with
  | add => exact addBounded
  | addi => exact addiBounded
  | addw => exact addwBounded
  | sub => exact subBounded
  | subw => exact subwBounded
  | bitwise => exact bitwiseBounded
  | lt => exact ltBounded
  | shiftLeft => exact shiftLeftBounded
  | shiftRight => exact shiftRightBounded
  | jal => exact jalBounded
  | jalr => exact jalrBounded
  | branch => exact branchBounded
  | uType => exact uTypeBounded
  | loadByte => exact loadByteBounded
  | loadHalf => exact loadHalfBounded
  | loadWord => exact loadWordBounded
  | loadDouble => exact loadDoubleBounded
  | loadX0 => exact loadX0Bounded
  | storeByte => exact storeByteBounded
  | storeHalf => exact storeHalfBounded
  | storeWord => exact storeWordBounded
  | storeDouble => exact storeDoubleBounded
  | mul => exact mulBounded
  | divRem => exact divRemBounded
  | aluX0 => exact aluX0Bounded

private theorem input_origin {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : ReleaseAdmissibleExecution (.native SP1Prime) SP1Prime image source target events) {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (id : InstructionChipId) (data evaluation : ProverData F) (hint : ProverHint F) (fit)
    {cells : Array F} (position : cells ∈ (InstalledInstructionTables.table id
      (EventBuckets.ofChronological (rows.filterMap MixedCompiledRow.ordinaryObservation?) id) data hint fit).table) :
    ∃ input, (installed id).rowInput (Environment.fromArray cells evaluation) = input ∧
      (input = InstalledInstructionTables.paddingInput id ∨ ∃ e : id.Event,
        id.Valid e ∧ (RoutedEvent.mk id e).clock < 2 ^ 48 ∧ input = InstalledInstructionTables.activeInput id e) := by
  let observations := rows.filterMap MixedCompiledRow.ordinaryObservation?
  let bucket := EventBuckets.ofChronological observations id
  let block := InstalledInstructionTables.table id bucket data hint fit
  change cells ∈ (InstalledInstructionTables.inputs id bucket).map (fun x => (installed id).buildRow x block.data hint) at position
  obtain ⟨input, present, rfl⟩ := List.mem_map.mp position
  refine ⟨input, (installed id).rowInput_buildRow input block.data evaluation hint, ?_⟩
  rcases List.mem_append.mp present with live | padding
  · obtain ⟨event, inBucket, rfl⟩ := List.mem_map.mp live
    obtain ⟨checked, collected, _, valid⟩ := releaseAdmissibleExecution_instructionBuckets run
    obtain ⟨ordered, chronology, _, bounds, _⟩ := admissibleExecution_routeObservations run.1
    have same : routeObservations? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some observations := by
      rw [routeObservations?, routed, Option.map_some]
    obtain rfl := Option.some.inj (same.symm.trans collected)
    obtain rfl := Option.some.inj (same.symm.trans chronology)
    obtain ⟨actual, listed, sameId, payload⟩ := EventBuckets.exists_chronological_of_mem inBucket
    obtain ⟨actualId, actualEvent⟩ := actual
    cases sameId
    cases payload
    exact Or.inr ⟨_, (valid _).2 _ inBucket, (bounds _ listed).2, rfl⟩
  · exact Or.inl (List.eq_of_mem_replicate padding)

/-- Every counted predecessor on each of the 25 generated ordinary tables retains all four
bounded timestamp limbs at arbitrary evaluation data. Both event validity and the incoming
clock bound are derived from the actual released execution at the chosen bucket. -/
theorem generated_ordinary_bounded {image : ProgramImage} {source target : ExecutionSnapshot} {tape : List ExecutionEvent}
    (run : ReleaseAdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target tape)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize tape = some rows)
    (id : InstructionChipId) (data evaluation : ProverData F) (hint : ProverHint F) (fit) {cells : Array F}
    (position : cells ∈ (InstalledInstructionTables.table id
      (EventBuckets.ofChronological (rows.filterMap MixedCompiledRow.ordinaryObservation?) id) data hint fit).table)
    {receipt : Readback F} (paid : (1, receipt) ∈ rowRecords (.ordinary id) (Environment.fromArray cells evaluation)) :
    Counted.Bounded receipt := by
  obtain ⟨input, decoded, origin⟩ := input_origin run routed id data evaluation hint fit position
  exact input_bounded id _ input decoded origin (1, receipt) paid

end SP1Clean.Export.WriteSourceRegistry
