import SP1Clean.Soundness.HostCallLedger
import ToClean.Circuit.SubcircuitProjection
import ToClean.Air.EnsembleProjection
import ToClean.Air.ExpressionScope

/-! # The host wrapper retains instruction constraints and State chronology

The wrapper uses the exact released instruction input type. Its full-code guard adds local
constraint witnesses and its single host receipt extends the channel inventory.
Every original channel occurrence remains in order, including on padding rows.
-/

namespace SP1Clean.Soundness.HostCallProjection

open Circuit Air.Flat Channels HostCallLedger

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def original : Component (ZMod p) := { circuit := SyscallInstrsChip.circuit, Assumptions := (SyscallInstrsChip.circuit).Assumptions, generation := SyscallInstrsChip.generation }

/-- The wrapper and released instruction decode the same physical input. -/
theorem input_original (env : Environment (ZMod p)) :
    HostCallLedger.input env = original.rowInput env := rfl

/-- Every released assertion and lookup follows from the wrapper's raw constraints. -/
theorem constraints_original (env : Environment (ZMod p))
    (constraints : producer.operations.ConstraintsHold env) : original.operations.ConstraintsHold env := by
  have core := HostCallChip.instruction_of_constraints (varFromOffset SyscallInstrsChip.Inputs 0)
    (size SyscallInstrsChip.Inputs) env ((Component.constraintsHold_iff env).mp constraints)
  exact (Component.constraintsHold_iff env).mpr (CoreSyscallChip.main_constraints_original _ _ env core)

/-- Removing the private host receipt recovers all original channel occurrences. -/
theorem other_interactions (channel : RawChannel (ZMod p)) (host : channel ≠ HostCallChip.channel.toRaw) :
    (original (p := p)).operations.interactionsWith channel =
      producer.operations.interactionsWith channel := by
  simp only [original, producer, Component.interactionsWith_eq, Component.rowOperations,
    HostCallChip.circuit, SyscallInstrsChip.circuit]
  rw [HostCallChip.main_other_interactions channel host]
  simp only [CoreSyscallChip.circuit, CoreSyscallChip.main, circuit_norm,
    GeneralFormalCircuit.toSubcircuit_interactions, FormalAssertion.toSubcircuit_interactions,
    SyscallCodeGuard.circuit, SyscallCodeGuard.main_interactions, SyscallInstrsChip.circuit,
    Operations.interactionsWith]

/-- Every released Byte requirement uses the same physical interaction in the wrapper. -/
theorem byte_guarantees (env : Environment (ZMod p))
    (guarantees : producer.operations.ChannelGuarantees byteChannel.toRaw env) :
    original.operations.ChannelGuarantees byteChannel.toRaw env := by
  apply Operations.channelGuarantees_of_interactionsWith_subset _ _ _ _ env guarantees
  rw [other_interactions byteChannel.toRaw (by simp [byteChannel, HostCallChip.channel, Channel.toRaw])]

/-- Original Memory accesses are preserved exactly for all codes, including WRITE. -/
theorem memory_values (env : Environment (ZMod p)) :
    producer.operations.interactionValuesWith memoryChannel.toRaw env =
      original.operations.interactionValuesWith memoryChannel.toRaw env := by
  simp only [Operations.interactionValuesWith, other_interactions memoryChannel.toRaw
    (by simp [memoryChannel, HostCallChip.channel, Channel.toRaw])]

/-- The complete State ledger determines the authentic incoming instruction clock. -/
theorem state_interactions : (original (p := p)).operations.interactionsWith stateChannel.toRaw =
    producer.operations.interactionsWith stateChannel.toRaw :=
  other_interactions stateChannel.toRaw (by simp [stateChannel, HostCallChip.channel, Channel.toRaw])

section Scope

attribute [local circuit_norm]
  original Component.constraints_eq Component.interactions_eq Component.rowOperations
  SyscallInstrsChip.circuit SyscallInstrsChip.main Circuit.forEach.operations_eq
  FlatOperation.constraints_append FlatOperation.interactions_append
  GeneralFormalCircuit.toSubcircuit_toFlat FormalAssertion.toSubcircuit_toFlat
  Readers.CPUState.circuit Readers.CPUState.main Readers.RegisterAccessCols.circuit
  Readers.RegisterAccessCols.main Readers.RegisterAccessTimestamp.circuit
  Readers.RegisterAccessTimestamp.main IsZeroOperation.circuit IsZeroOperation.main
  Gadgets.Equality.circuit Gadgets.Equality.main
  U16toU8OperationSafe.circuit U16toU8OperationSafe.main
  SyscallInstrsChip.PcArm.circuit SyscallInstrsChip.PcArm.main
  SyscallInstrsChip.WriteArm.circuit SyscallInstrsChip.WriteArm.main
  SyscallInstrsChip.DispatchArm.circuit SyscallInstrsChip.DispatchArm.main
  SyscallInstrsChip.CommitArm.circuit SyscallInstrsChip.CommitArm.main
  SyscallInstrsChip.FieldBoundArm.circuit SyscallInstrsChip.FieldBoundArm.main
  U16CompareOperation.circuit U16CompareOperation.main

/-- Clean's scope checker bounds every original assertion, multiplicity and message by the
instruction's own width, independent of the wider host wrapper. -/
theorem original_scope :
    Backends.expressionsBadVariable (original (p := p)).width
      (original (p := p)).operations.constraints = none ∧
    Backends.expressionsBadVariable (original (p := p)).width
      ((original (p := p)).operations.interactions.flatMap fun interaction =>
        interaction.mult :: interaction.msg.toList) = none := by
  have width : (original (p := p)).width = 65 := rfl
  rw [width]
  constructor
  · simp only [circuit_norm]
    cbv
  · simp only [circuit_norm]
    -- Check each expression separately so a larger message does not deepen one reduction.
    simp only [Backends.expressionsBadVariable, List.findSome?_eq_none_iff,
      List.forall_mem_flatMap, FlatOperation.interactions, List.forall_mem_append,
      List.forall_mem_cons]
    repeat' apply And.intro
    all_goals solve
      | exact List.forall_mem_nil _
      | (apply List.findSome?_eq_none_iff.mp; cbv)
      | cbv

end Scope

/-- Truncating an actual host row retains the original instruction constraints at canonical data. -/
theorem constraints_prefix (row : Array (ZMod p)) (data data' : ProverData (ZMod p))
    (checked : producer.operations.ConstraintsHold (Environment.fromArray row data)) :
    original.operations.ConstraintsHold
      (Environment.fromArray (row.extract 0 (original (p := p)).width) data') := by
  apply Backends.constraints_extract row data data' SyscallInstrsChip.lookups_empty ?_
    (constraints_original _ checked)
  exact (original_scope (p := p)).1

/-- The original Byte checks survive truncation even when canonical data changes. -/
theorem byte_guarantees_prefix (row : Array (ZMod p)) (data data' : ProverData (ZMod p))
    (guarantees : producer.operations.ChannelGuarantees byteChannel.toRaw (Environment.fromArray row data)) :
    original.operations.ChannelGuarantees byteChannel.toRaw
      (Environment.fromArray (row.extract 0 (original (p := p)).width) data') := by
  intro interaction member channel
  have scope : Backends.expressionsBadVariable (original (p := p)).width
      (interaction.mult :: interaction.msg.toList) = none :=
    List.findSome?_eq_none_iff.mpr fun expression used =>
      List.findSome?_eq_none_iff.mp (original_scope (p := p)).2 expression
        (List.mem_flatMap.mpr ⟨interaction, member, used⟩)
  rw [← AbstractInteraction.eval_guarantees, Backends.interaction_eval_extract row data data' _ scope]
  have kept := byte_guarantees (Environment.fromArray row data) guarantees interaction member channel
  rcases interaction with ⟨declared, mult, msg, assume⟩
  cases channel
  simpa only [Interaction.Guarantees, AbstractInteraction.eval, AbstractInteraction.Guarantees,
    Interaction.msgVector, byteChannel, Channel.toRaw] using kept

/-- Physical prefix decoding recovers the same original instruction from a host row. -/
theorem input_prefix (row : Array (ZMod p)) (data data' : ProverData (ZMod p)) :
    original.rowInput (Environment.fromArray (row.extract 0 (original (p := p)).width) data') =
      HostCallLedger.input (Environment.fromArray row data) := by
  rw [input_original]
  apply ProvableType.valueFromOffset_congr
  intro index bound
  have within : index < (original (p := p)).width := by
    change index < 65 at bound ⊢
    exact bound
  by_cases inside : index < row.size <;> simp [within, inside]

/-- The original instruction's complete ledger depends only on its physical prefix. -/
theorem original_values_prefix (row : Array (ZMod p)) (data data' : ProverData (ZMod p))
    (channel : RawChannel (ZMod p)) :
    original.operations.interactionValuesWith channel
        (Environment.fromArray (row.extract 0 (original (p := p)).width) data') =
      original.operations.interactionValuesWith channel (Environment.fromArray row data) := by
  simp only [Operations.interactionValuesWith]
  apply List.map_congr_left
  intro interaction member
  apply Backends.interaction_eval_extract
  apply List.findSome?_eq_none_iff.mpr
  intro expression used
  exact List.findSome?_eq_none_iff.mp (original_scope (p := p)).2 expression
    (List.mem_flatMap.mpr ⟨interaction, (List.mem_filter.mp member).1, used⟩)

/-- Prefix projection retains every occurrence on channels unchanged by the host wrapper. -/
theorem other_values_prefix (row : Array (ZMod p)) (data data' : ProverData (ZMod p))
    (channel : RawChannel (ZMod p)) (host : channel ≠ HostCallChip.channel.toRaw) :
    original.operations.interactionValuesWith channel
        (Environment.fromArray (row.extract 0 (original (p := p)).width) data') =
      producer.operations.interactionValuesWith channel (Environment.fromArray row data) := by
  rw [original_values_prefix, Operations.interactionValuesWith, Operations.interactionValuesWith,
    other_interactions channel host]

end SP1Clean.Soundness.HostCallProjection
