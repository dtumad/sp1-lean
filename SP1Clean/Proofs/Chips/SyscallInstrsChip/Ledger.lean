module

public import SP1Clean.Proofs.Chips.SyscallInstrsChip.Formal

/-! # Syscall row interactions

The native circuit's complete interaction list and its channel projections. Semantic consumers
use these lemmas without depending on extracted Rust column types or faithfulness proofs.
-/

@[expose] public section

namespace SP1Clean.SyscallInstrsChip.Ledger

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel exitChannel
  syscallChannel publicValuesChannel MemoryMsg ProgramMsg PublicValueMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The row's complete emitted interaction list, split into its sixteen composed blocks and its own
three groups: the Program fetch with the three register Memory pairs, the six byte checks, and the
public-value hand-off followed by the generic syscall send. -/
theorem syscallInstrsInteractionBlocks (r : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactions ((SyscallInstrsChip.main r).operations offset) =
      Operations.interactions
        ((SP1Clean.U16toU8OperationSafe.circuit.main
          ⟨r.op_a_memory.prev_value, r.syscall_id_bytes, r.is_real⟩).operations offset) ++
      Operations.interactions
        ((SP1Clean.IsZeroOperation.circuit.main
          ⟨syscallIdVar r - natConst haltCode, r.is_halt_zero, r.is_real⟩).operations offset) ++
      Operations.interactions
        ((SP1Clean.IsZeroOperation.circuit.main
          ⟨syscallIdVar r - natConst enterUnconstrainedCode, r.is_enter_unconstrained,
           r.is_real⟩).operations offset) ++
      Operations.interactions
        ((SP1Clean.IsZeroOperation.circuit.main
          ⟨syscallIdVar r - natConst hintLenCode, r.is_hint_len, r.is_real⟩).operations offset) ++
      Operations.interactions
        ((SP1Clean.IsZeroOperation.circuit.main
          ⟨syscallIdVar r - natConst commitCode, r.is_commit, r.is_real⟩).operations offset) ++
      Operations.interactions
        ((SP1Clean.IsZeroOperation.circuit.main
          ⟨syscallIdVar r - natConst commitDeferredCode, r.is_commit_deferred, r.is_real⟩).operations offset) ++
      Operations.interactions
        ((Readers.CPUState.circuit.main ⟨r.state, r.next_pc, 264, r.is_real⟩).operations offset) ++
      Operations.interactions
        ((Readers.RegisterAccessCols.circuit.main ⟨r.op_a_memory, r.is_real, clkLowVar r + 4⟩).operations offset) ++
      Operations.interactions
        ((Readers.RegisterAccessCols.circuit.main ⟨r.op_b_memory, r.is_real, clkLowVar r + 3⟩).operations offset) ++
      Operations.interactions
        ((Readers.RegisterAccessCols.circuit.main ⟨r.op_c_memory, r.is_real, clkLowVar r + 2⟩).operations offset) ++
      [({ mult := -r.is_real, msg := programMsg r,
          assumeGuarantees := true } :
         ChannelInteraction (programChannel (p := p))).toRaw,
       ({ mult := -r.is_real, msg := memPullMsg r r.op_a_memory r.op_a,
          assumeGuarantees := true } :
         ChannelInteraction (memoryChannel (p := p))).toRaw,
       ({ mult := r.is_real, msg := memPushMsg r r.op_a 4 r.op_a_value,
          assumeGuarantees := false } :
         ChannelInteraction (memoryChannel (p := p))).toRaw,
       ({ mult := -r.is_real, msg := memPullMsg r r.op_b_memory r.op_b,
          assumeGuarantees := true } :
         ChannelInteraction (memoryChannel (p := p))).toRaw,
       ({ mult := r.is_real, msg := memPushMsg r r.op_b 3 r.op_b_memory.prev_value,
          assumeGuarantees := false } :
         ChannelInteraction (memoryChannel (p := p))).toRaw,
       ({ mult := -r.is_real, msg := memPullMsg r r.op_c_memory r.op_c,
          assumeGuarantees := true } :
         ChannelInteraction (memoryChannel (p := p))).toRaw,
       ({ mult := r.is_real, msg := memPushMsg r r.op_c 2 r.op_c_memory.prev_value,
          assumeGuarantees := false } :
         ChannelInteraction (memoryChannel (p := p))).toRaw] ++
      Operations.interactions
        ((SyscallInstrsChip.WriteArm.circuit.main
          ⟨r.op_a_memory.prev_value, r.op_a_value, r.op_a_0,
           r.is_enter_unconstrained.result, r.is_hint_len.result, r.is_real⟩).operations offset) ++
      Operations.interactions
        ((SyscallInstrsChip.PcArm.circuit.main ⟨r.state.pc, r.next_pc, r.is_real, r.is_halt⟩).operations offset) ++
      Operations.interactions
        ((SyscallInstrsChip.DispatchArm.circuit.main
          ⟨r.op_b_memory.prev_value, r.op_c_memory.prev_value, tableByteVar r⟩).operations offset) ++
      Operations.interactions
        ((SyscallInstrsChip.FieldBoundArm.circuit.main
          ⟨r.op_b_memory.prev_value, r.op_b_cmp.bit, r.is_halt⟩).operations offset) ++
      Operations.interactions
        ((SyscallInstrsChip.FieldBoundArm.circuit.main
          ⟨r.op_c_memory.prev_value, r.op_c_cmp.bit, r.is_commit_deferred.result⟩).operations offset) ++
      Operations.interactions
        ((SyscallInstrsChip.CommitArm.circuit.main
          ⟨r.digest_index_bits, r.digest_word, r.op_b_memory.prev_value,
           r.op_c_memory.prev_value, r.is_commit.result, r.is_commit_deferred.result,
           r.is_real⟩).operations offset) ++
      [({ mult := -r.is_real, msg := (⟨6, r.op_a_value[0], natConst 16, 0⟩ : ByteRow (Expression (ZMod p))),
          assumeGuarantees := true } :
         ChannelInteraction (byteChannel (p := p))).toRaw,
       ({ mult := -r.is_real, msg := (⟨6, r.op_a_value[1], natConst 16, 0⟩ : ByteRow (Expression (ZMod p))),
          assumeGuarantees := true } :
         ChannelInteraction (byteChannel (p := p))).toRaw,
       ({ mult := -r.is_real, msg := (⟨6, r.op_a_value[2], natConst 16, 0⟩ : ByteRow (Expression (ZMod p))),
          assumeGuarantees := true } :
         ChannelInteraction (byteChannel (p := p))).toRaw,
       ({ mult := -r.is_real, msg := (⟨6, r.op_a_value[3], natConst 16, 0⟩ : ByteRow (Expression (ZMod p))),
          assumeGuarantees := true } :
         ChannelInteraction (byteChannel (p := p))).toRaw,
       ({ mult := -r.is_commit.result, msg := (⟨3, 0, r.digest_word[0], r.digest_word[1]⟩ :
            ByteRow (Expression (ZMod p))),
          assumeGuarantees := true } :
         ChannelInteraction (byteChannel (p := p))).toRaw,
       ({ mult := -r.is_commit.result, msg := (⟨3, 0, r.digest_word[2], r.digest_word[3]⟩ :
            ByteRow (Expression (ZMod p))),
          assumeGuarantees := true } :
         ChannelInteraction (byteChannel (p := p))).toRaw] ++
      [({ mult := r.is_halt, msg := exitMsg r,
          assumeGuarantees := false } :
         ChannelInteraction (exitChannel (p := p))).toRaw,
       ({ mult := -r.is_commit.result, msg := (PublicValueMsg.scalar (natConst 145) 1),
          assumeGuarantees := true } :
         ChannelInteraction (publicValuesChannel (p := p))).toRaw,
       ({ mult := -r.is_commit_deferred.result, msg := (PublicValueMsg.scalar (natConst 147) 1),
          assumeGuarantees := true } :
         ChannelInteraction (publicValuesChannel (p := p))).toRaw,
       ({ mult := -r.is_commit.result, msg := ⟨natConst 32, natConst 4, r.digest_index_bits, r.digest_word[0]⟩,
          assumeGuarantees := true } :
         ChannelInteraction (publicValuesChannel (p := p))).toRaw,
       ({ mult := -r.is_commit.result, msg := ⟨natConst 33, natConst 4, r.digest_index_bits, r.digest_word[1]⟩,
          assumeGuarantees := true } :
         ChannelInteraction (publicValuesChannel (p := p))).toRaw,
       ({ mult := -r.is_commit.result, msg := ⟨natConst 34, natConst 4, r.digest_index_bits, r.digest_word[2]⟩,
          assumeGuarantees := true } :
         ChannelInteraction (publicValuesChannel (p := p))).toRaw,
       ({ mult := -r.is_commit.result, msg := ⟨natConst 35, natConst 4, r.digest_index_bits, r.digest_word[3]⟩,
          assumeGuarantees := true } :
         ChannelInteraction (publicValuesChannel (p := p))).toRaw,
       ({ mult := -(r.is_real * r.is_commit_deferred.result), msg := ⟨natConst 72, natConst 1, r.digest_index_bits, reduceWord r.op_c_memory.prev_value⟩,
          assumeGuarantees := true } :
         ChannelInteraction (publicValuesChannel (p := p))).toRaw,
       ({ mult := tableByteVar r, msg := syscallMsg r,
          assumeGuarantees := false } :
         ChannelInteraction (syscallChannel (p := p))).toRaw] := by
  simp only [SyscallInstrsChip.main, Circuit.operations, Circuit.bind_def,
    assertZero, subcircuitWithAssertion, assertion, Channel.pullIf, Channel.pushIf,
    Operations.interactions_assert,
    Operations.interactions_interact, Operations.interactions_nil,
    Operations.interactions_subcircuit,
    FormalAssertion.toSubcircuit_interactions, GeneralFormalCircuit.toSubcircuit_interactions,
    FormalAssertion.toSubcircuit_localLength, GeneralFormalCircuit.toSubcircuit_localLength,
    Readers.CPUState.circuit_localLength, Readers.RegisterAccessCols.circuit_localLength,
    SP1Clean.IsZeroOperation.circuit_localLength,
    SyscallInstrsChip.PcArm.circuit_localLength,
    SyscallInstrsChip.WriteArm.circuit_localLength,
    SyscallInstrsChip.FieldBoundArm.circuit_localLength,
    SyscallInstrsChip.DispatchArm.circuit_localLength,
    SP1Clean.U16toU8OperationSafe.circuit_localLength,
    Operations.localLength, Nat.add_zero,
    List.append_assoc, List.cons_append, List.nil_append]

/-! ## Each composed block's interaction list

Each composed circuit is inspected at an opaque input. Four of the sixteen blocks emit nothing:
`IsZeroOperation` and three of the five arms are pure `assertZero` gadgets. -/

omit [Fact (2 ^ 17 < p)] in
/-- The five arm selectors emit nothing: `IsZeroOperation` is a pure `assertZero` gadget, and so is
the scalar equality gadget it composes. -/
theorem isZeroInteractions (input : Var SP1Clean.IsZeroOperation.Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactions
      ((SP1Clean.IsZeroOperation.circuit.main input).operations offset) = [] := by
  simp only [SP1Clean.IsZeroOperation.circuit, SP1Clean.IsZeroOperation.main, circuit_norm,
    FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.main]

omit [Fact (2 ^ 17 < p)] in
/-- `PcArm`, `WriteArm`, `DispatchArm` and `CommitArm` are pure `assertZero` blocks. -/
theorem pcArmInteractions (input : Var SyscallInstrsChip.PcArm.Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactions
      ((SyscallInstrsChip.PcArm.circuit.main input).operations offset) = [] := rfl

omit [Fact (2 ^ 17 < p)] in
theorem writeArmInteractions (input : Var SyscallInstrsChip.WriteArm.Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactions
      ((SyscallInstrsChip.WriteArm.circuit.main input).operations offset) = [] := rfl

omit [Fact (2 ^ 17 < p)] in
theorem dispatchArmInteractions (input : Var SyscallInstrsChip.DispatchArm.Inputs (ZMod p))
    (offset : ℕ) :
    Operations.interactions
      ((SyscallInstrsChip.DispatchArm.circuit.main input).operations offset) = [] := rfl

omit [Fact (2 ^ 17 < p)] in
theorem commitArmInteractions (input : Var SyscallInstrsChip.CommitArm.Inputs (ZMod p))
    (offset : ℕ) :
    Operations.interactions
      ((SyscallInstrsChip.CommitArm.circuit.main input).operations offset) = [] := rfl

/-- SP1's `slice_range_check_u8` on the four split bytes. -/
theorem u16toU8SafeInteractions (input : Var SP1Clean.U16toU8OperationSafe.Inputs (ZMod p))
    (offset : ℕ) :
    Operations.interactions
        ((SP1Clean.U16toU8OperationSafe.circuit.main input).operations offset) =
      [(byteChannel.pulledIf input.is_real
          (⟨3, 0, input.cols.low_bytes[0],
            (input.u16_values[0] - input.cols.low_bytes[0]) *
              Expression.const (256 : ZMod p)⁻¹⟩ : ByteRow (Expression (ZMod p)))).toRaw,
       (byteChannel.pulledIf input.is_real
          (⟨3, 0, input.cols.low_bytes[1],
            (input.u16_values[1] - input.cols.low_bytes[1]) *
              Expression.const (256 : ZMod p)⁻¹⟩ : ByteRow (Expression (ZMod p)))).toRaw,
       (byteChannel.pulledIf input.is_real
          (⟨3, 0, input.cols.low_bytes[2],
            (input.u16_values[2] - input.cols.low_bytes[2]) *
              Expression.const (256 : ZMod p)⁻¹⟩ : ByteRow (Expression (ZMod p)))).toRaw,
       (byteChannel.pulledIf input.is_real
          (⟨3, 0, input.cols.low_bytes[3],
            (input.u16_values[3] - input.cols.low_bytes[3]) *
              Expression.const (256 : ZMod p)⁻¹⟩ : ByteRow (Expression (ZMod p)))).toRaw] := by
  simp only [SP1Clean.U16toU8OperationSafe.circuit, SP1Clean.U16toU8OperationSafe.main, circuit_norm]

/-- The `U16Compare` bound: one range check, then a pure equality. -/
theorem u16CompareInteractions (input : Var SP1Clean.U16CompareOperation.Inputs (ZMod p))
    (offset : ℕ) :
    Operations.interactions
        ((SP1Clean.U16CompareOperation.circuit.main input).operations offset) =
      [(byteChannel.pulledIf input.is_real
          (⟨6, input.a - input.b + input.cols.bit * 65536, Expression.const ((16 : ℕ) : ZMod p),
            0⟩ : ByteRow (Expression (ZMod p)))).toRaw] := by
  simp only [SP1Clean.U16CompareOperation.circuit, SP1Clean.U16CompareOperation.main, circuit_norm,
    FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.main]

/-- The `FieldBoundArm`'s only bus traffic is its `U16Compare` fragment's. -/
theorem fieldBoundArmInteractions (input : Var SyscallInstrsChip.FieldBoundArm.Inputs (ZMod p))
    (offset : ℕ) :
    Operations.interactions
        ((SyscallInstrsChip.FieldBoundArm.circuit.main input).operations offset) =
      Operations.interactions
        ((SP1Clean.U16CompareOperation.circuit.main
            ⟨input.word[1], Expression.const ((fieldLimbBound : ℕ) : ZMod p), ⟨input.bit⟩,
             input.is_real⟩).operations offset) := by
  simp only [SyscallInstrsChip.FieldBoundArm.circuit, SyscallInstrsChip.FieldBoundArm.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions]

/-- The state reader's two clock range checks and its State edge. -/
theorem cpuStateInteractions (input : Var Readers.CPUState.Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactions ((Readers.CPUState.circuit.main input).operations offset) =
      [(byteChannel.pulledIf input.is_real
          (⟨6, (input.cols.clk_0_16 - 1) * Expression.const (8 : ZMod p)⁻¹,
            Expression.const ((13 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))).toRaw,
       (byteChannel.pulledIf input.is_real
          (⟨3, 0, input.cols.clk_16_24, 0⟩ : ByteRow (Expression (ZMod p)))).toRaw,
       (stateChannel.pulledIf input.is_real (Readers.CPUState.currentMsg input)).toRaw,
       (stateChannel.pushedIf input.is_real (Readers.CPUState.nextMsg input)).toRaw] := by
  simp only [Readers.CPUState.circuit, Readers.CPUState.main, circuit_norm]

/-- The register reader's two timestamp range checks. -/
theorem registerAccessTimestampInteractions
    (input : Var Readers.RegisterAccessTimestamp.Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactions
        ((Readers.RegisterAccessTimestamp.circuit.main input).operations offset) =
      [(byteChannel.pulledIf input.is_real
          (⟨6, input.cols.diff_low_limb, Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
            ByteRow (Expression (ZMod p)))).toRaw,
       (byteChannel.pulledIf input.is_real
          (⟨3, 0, (input.clk_target - input.cols.prev_low - 1 - input.cols.diff_low_limb) *
            Expression.const (65536 : ZMod p)⁻¹, 0⟩ : ByteRow (Expression (ZMod p)))).toRaw] := by
  simp only [Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    circuit_norm]

theorem registerAccessColsInteractions (input : Var Readers.RegisterAccessCols.Inputs (ZMod p))
    (offset : ℕ) :
    Operations.interactions
        ((Readers.RegisterAccessCols.circuit.main input).operations offset) =
      Operations.interactions
        ((Readers.RegisterAccessTimestamp.circuit.main
            ⟨input.cols.access_timestamp, input.is_real, input.clk_target⟩).operations offset) := by
  simp only [Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main, circuit_norm,
    FormalAssertion.toSubcircuit_interactions]

/-! ## The row's traffic, one bus at a time

Filtering the composed interaction list preserves physical occurrences, including zero
multiplicities and repeated keys. -/

/-- The State edge: pull `(clk, pc)`, push `(clk + 264, next_pc)`. -/
theorem syscallInstrsInteractionsWith_state (r : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ) :
    ((SyscallInstrsChip.main r).operations offset).interactionsWith (stateChannel (p := p)).toRaw =
    [(stateChannel.pulledIf r.is_real
        (Readers.CPUState.currentMsg ⟨r.state, r.next_pc, 264, r.is_real⟩)).toRaw,
     (stateChannel.pushedIf r.is_real
        (Readers.CPUState.nextMsg ⟨r.state, r.next_pc, 264, r.is_real⟩)).toRaw] := by
  simp only [Operations.interactionsWith, syscallInstrsInteractionBlocks, isZeroInteractions,
    pcArmInteractions, writeArmInteractions, dispatchArmInteractions, commitArmInteractions,
    u16toU8SafeInteractions, u16CompareInteractions, fieldBoundArmInteractions,
    cpuStateInteractions, registerAccessColsInteractions, registerAccessTimestampInteractions,
    ChannelInteraction.toRaw_channel,
    List.filter_cons, List.filter_nil, List.append_nil, List.nil_append,
    List.cons_append, decide_eq_true_eq, if_true, if_false,
    Channels.byteChannel_eq_stateChannel_false,
    Channels.memoryChannel_eq_stateChannel_false,
    Channels.programChannel_eq_stateChannel_false,
    Channels.exitChannel_eq_stateChannel_false,
    Channels.syscallChannel_eq_stateChannel_false,
    Channels.publicValuesChannel_eq_stateChannel_false]

/-- The single committed `ECALL` fetch. -/
theorem syscallInstrsInteractionsWith_program (r : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ) :
    ((SyscallInstrsChip.main r).operations offset).interactionsWith (programChannel (p := p)).toRaw =
    [
      ({ mult := -r.is_real, msg := programMsg r,
         assumeGuarantees := true } :
        ChannelInteraction (programChannel (p := p))).toRaw] := by
  simp only [Operations.interactionsWith, syscallInstrsInteractionBlocks, isZeroInteractions,
    pcArmInteractions, writeArmInteractions, dispatchArmInteractions, commitArmInteractions,
    u16toU8SafeInteractions, u16CompareInteractions, fieldBoundArmInteractions,
    cpuStateInteractions, registerAccessColsInteractions, registerAccessTimestampInteractions,
    ChannelInteraction.toRaw_channel,
    List.filter_cons, List.filter_nil, List.append_nil, List.nil_append,
    List.cons_append, decide_eq_true_eq, if_true, if_false,
    Channels.byteChannel_eq_programChannel_false,
    Channels.stateChannel_eq_programChannel_false,
    Channels.memoryChannel_eq_programChannel_false,
    Channels.exitChannel_eq_programChannel_false,
    Channels.syscallChannel_eq_programChannel_false,
    Channels.publicValuesChannel_eq_programChannel_false]

/-- The three register access pairs, read-prior pulled and read-back pushed. -/
theorem syscallInstrsInteractionsWith_memory (r : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ) :
    ((SyscallInstrsChip.main r).operations offset).interactionsWith (memoryChannel (p := p)).toRaw =
    [
      ({ mult := -r.is_real, msg := memPullMsg r r.op_a_memory r.op_a,
         assumeGuarantees := true } :
        ChannelInteraction (memoryChannel (p := p))).toRaw,
      ({ mult := r.is_real, msg := memPushMsg r r.op_a 4 r.op_a_value,
         assumeGuarantees := false } :
        ChannelInteraction (memoryChannel (p := p))).toRaw,
      ({ mult := -r.is_real, msg := memPullMsg r r.op_b_memory r.op_b,
         assumeGuarantees := true } :
        ChannelInteraction (memoryChannel (p := p))).toRaw,
      ({ mult := r.is_real, msg := memPushMsg r r.op_b 3 r.op_b_memory.prev_value,
         assumeGuarantees := false } :
        ChannelInteraction (memoryChannel (p := p))).toRaw,
      ({ mult := -r.is_real, msg := memPullMsg r r.op_c_memory r.op_c,
         assumeGuarantees := true } :
        ChannelInteraction (memoryChannel (p := p))).toRaw,
      ({ mult := r.is_real, msg := memPushMsg r r.op_c 2 r.op_c_memory.prev_value,
         assumeGuarantees := false } :
        ChannelInteraction (memoryChannel (p := p))).toRaw] := by
  simp only [Operations.interactionsWith, syscallInstrsInteractionBlocks, isZeroInteractions,
    pcArmInteractions, writeArmInteractions, dispatchArmInteractions, commitArmInteractions,
    u16toU8SafeInteractions, u16CompareInteractions, fieldBoundArmInteractions,
    cpuStateInteractions, registerAccessColsInteractions, registerAccessTimestampInteractions,
    ChannelInteraction.toRaw_channel,
    List.filter_cons, List.filter_nil, List.append_nil, List.nil_append,
    List.cons_append, decide_eq_true_eq, if_true, if_false,
    Channels.byteChannel_eq_memoryChannel_false,
    Channels.stateChannel_eq_memoryChannel_false,
    Channels.programChannel_eq_memoryChannel_false,
    Channels.exitChannel_eq_memoryChannel_false,
    Channels.syscallChannel_eq_memoryChannel_false,
    Channels.publicValuesChannel_eq_memoryChannel_false]

/-- The `Exit` hand-off: a single `is_halt`-gated push of the reduced exit code. Unlike the halt
table's, there is no anti-gated companion push — a many-row table cannot use that trick. -/
theorem syscallInstrsInteractionsWith_exit (r : Var SyscallInstrsChip.Inputs (ZMod p))
    (offset : ℕ) :
    ((SyscallInstrsChip.main r).operations offset).interactionsWith (exitChannel (p := p)).toRaw =
    [({ mult := r.is_halt, msg := SyscallInstrsChip.exitMsg r, assumeGuarantees := false } :
        ChannelInteraction (exitChannel (p := p))).toRaw] := by
  simp only [Operations.interactionsWith, syscallInstrsInteractionBlocks, isZeroInteractions,
    pcArmInteractions, writeArmInteractions, dispatchArmInteractions, commitArmInteractions,
    u16toU8SafeInteractions, u16CompareInteractions, fieldBoundArmInteractions,
    cpuStateInteractions, registerAccessColsInteractions, registerAccessTimestampInteractions,
    ChannelInteraction.toRaw_channel,
    List.filter_cons, List.filter_nil, List.append_nil, List.nil_append,
    List.cons_append, decide_eq_true_eq, if_true, if_false,
    Channels.byteChannel_eq_exitChannel_false,
    Channels.stateChannel_eq_exitChannel_false,
    Channels.programChannel_eq_exitChannel_false,
    Channels.memoryChannel_eq_exitChannel_false,
    Channels.syscallChannel_eq_exitChannel_false,
    Channels.publicValuesChannel_eq_exitChannel_false]

/-- Twenty byte checks: the four identifier-split bytes, the state reader's two clock bounds, two timestamp bounds per register, one field-element compare per bounded operand, the four `op_a_value` range checks, and the two digest byte pairs. -/
theorem syscallInstrsInteractionsWith_byte (r : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ) :
    ((SyscallInstrsChip.main r).operations offset).interactionsWith (byteChannel (p := p)).toRaw =
    [
      (byteChannel.pulledIf r.is_real
        (⟨3, 0, r.syscall_id_bytes.low_bytes[0],
          (r.op_a_memory.prev_value[0] - r.syscall_id_bytes.low_bytes[0]) *
            Expression.const (256 : ZMod p)⁻¹⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      (byteChannel.pulledIf r.is_real
        (⟨3, 0, r.syscall_id_bytes.low_bytes[1],
          (r.op_a_memory.prev_value[1] - r.syscall_id_bytes.low_bytes[1]) *
            Expression.const (256 : ZMod p)⁻¹⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      (byteChannel.pulledIf r.is_real
        (⟨3, 0, r.syscall_id_bytes.low_bytes[2],
          (r.op_a_memory.prev_value[2] - r.syscall_id_bytes.low_bytes[2]) *
            Expression.const (256 : ZMod p)⁻¹⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      (byteChannel.pulledIf r.is_real
        (⟨3, 0, r.syscall_id_bytes.low_bytes[3],
          (r.op_a_memory.prev_value[3] - r.syscall_id_bytes.low_bytes[3]) *
            Expression.const (256 : ZMod p)⁻¹⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      (byteChannel.pulledIf r.is_real
        (⟨6, (r.state.clk_0_16 - 1) * Expression.const (8 : ZMod p)⁻¹,
          Expression.const ((13 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      (byteChannel.pulledIf r.is_real
        (⟨3, 0, r.state.clk_16_24, 0⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      (byteChannel.pulledIf r.is_real
        (⟨6, r.op_a_memory.access_timestamp.diff_low_limb, Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      (byteChannel.pulledIf r.is_real
        (⟨3, 0,
          (clkLowVar r + 4 - r.op_a_memory.access_timestamp.prev_low - 1 -
            r.op_a_memory.access_timestamp.diff_low_limb) * Expression.const (65536 : ZMod p)⁻¹, 0⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      (byteChannel.pulledIf r.is_real
        (⟨6, r.op_b_memory.access_timestamp.diff_low_limb, Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      (byteChannel.pulledIf r.is_real
        (⟨3, 0,
          (clkLowVar r + 3 - r.op_b_memory.access_timestamp.prev_low - 1 -
            r.op_b_memory.access_timestamp.diff_low_limb) * Expression.const (65536 : ZMod p)⁻¹, 0⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      (byteChannel.pulledIf r.is_real
        (⟨6, r.op_c_memory.access_timestamp.diff_low_limb, Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      (byteChannel.pulledIf r.is_real
        (⟨3, 0,
          (clkLowVar r + 2 - r.op_c_memory.access_timestamp.prev_low - 1 -
            r.op_c_memory.access_timestamp.diff_low_limb) * Expression.const (65536 : ZMod p)⁻¹, 0⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      (byteChannel.pulledIf r.is_halt
        (⟨6, r.op_b_memory.prev_value[1] - Expression.const ((fieldLimbBound : ℕ) : ZMod p) +
          r.op_b_cmp.bit * 65536, Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      (byteChannel.pulledIf r.is_commit_deferred.result
        (⟨6, r.op_c_memory.prev_value[1] - Expression.const ((fieldLimbBound : ℕ) : ZMod p) +
          r.op_c_cmp.bit * 65536, Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      ({ mult := -r.is_real, msg := (⟨6, r.op_a_value[0], natConst 16, 0⟩ :
          ByteRow (Expression (ZMod p))), assumeGuarantees := true } :
        ChannelInteraction (byteChannel (p := p))).toRaw,
      ({ mult := -r.is_real, msg := (⟨6, r.op_a_value[1], natConst 16, 0⟩ :
          ByteRow (Expression (ZMod p))), assumeGuarantees := true } :
        ChannelInteraction (byteChannel (p := p))).toRaw,
      ({ mult := -r.is_real, msg := (⟨6, r.op_a_value[2], natConst 16, 0⟩ :
          ByteRow (Expression (ZMod p))), assumeGuarantees := true } :
        ChannelInteraction (byteChannel (p := p))).toRaw,
      ({ mult := -r.is_real, msg := (⟨6, r.op_a_value[3], natConst 16, 0⟩ :
          ByteRow (Expression (ZMod p))), assumeGuarantees := true } :
        ChannelInteraction (byteChannel (p := p))).toRaw,
      ({ mult := -r.is_commit.result,
         msg := (⟨3, 0, r.digest_word[0], r.digest_word[1]⟩ :
           ByteRow (Expression (ZMod p))), assumeGuarantees := true } :
        ChannelInteraction (byteChannel (p := p))).toRaw,
      ({ mult := -r.is_commit.result,
         msg := (⟨3, 0, r.digest_word[2], r.digest_word[3]⟩ :
           ByteRow (Expression (ZMod p))), assumeGuarantees := true } :
        ChannelInteraction (byteChannel (p := p))).toRaw] := by
  simp only [Operations.interactionsWith, syscallInstrsInteractionBlocks, isZeroInteractions,
    pcArmInteractions, writeArmInteractions, dispatchArmInteractions, commitArmInteractions,
    u16toU8SafeInteractions, u16CompareInteractions, fieldBoundArmInteractions,
    cpuStateInteractions, registerAccessColsInteractions, registerAccessTimestampInteractions,
    ChannelInteraction.toRaw_channel,
    List.filter_cons, List.filter_nil, List.append_nil, List.nil_append,
    List.cons_append, decide_eq_true_eq, if_true, if_false,
    Channels.stateChannel_eq_byteChannel_false,
    Channels.memoryChannel_eq_byteChannel_false,
    Channels.programChannel_eq_byteChannel_false,
    Channels.exitChannel_eq_byteChannel_false,
    Channels.syscallChannel_eq_byteChannel_false,
    Channels.publicValuesChannel_eq_byteChannel_false]

end SP1Clean.SyscallInstrsChip.Ledger
