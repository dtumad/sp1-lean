import SP1Clean.Proofs.Chips.HostCommitChip.Interactions
import ToClean.Circuit.Guarded

/-! # Soundness and completeness of native commitment-bank transitions

The selected call and value bound are checked locally. Strict clock order and the exact state
pair support a subsequent bank-history proof; no final-bank or fixed-public-digest equality is
assumed by this component.
-/

namespace SP1Clean.HostCommitChip

open Circuit Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def ProverAssumptions (deferred : Bool) (slot : Fin 8) (input : Inputs (ZMod p)) : Prop :=
  Spec deferred slot input ∧ input.comparison =
    LtOperationUnsigned.populate input.call.arg2 (BoundedWord.limit (bound p deferred))

omit [Fact (2 ^ 25 < p)] in
private theorem eval_zero (env : Environment (ZMod p)) :
    Vector.map (Expression.eval env) (Vector.map Expression.const (0 : Word (ZMod p))) = 0 := by
  simp only [Vector.map_map, Function.comp_def, Expression.eval]
  exact Vector.map_id _

theorem soundness (deferred : Bool) (slot : Fin 8) :
    GeneralFormalCircuit.Soundness (Output := unit) (ZMod p) (main deferred slot)
      (fun _ _ => True) (fun input _ _ => Spec deferred slot input) := by
  circuit_proof_start [Gadgets.Equality.circuit, ClockOrder.circuit, BoundedWord.circuit,
    U16toU8OperationSafe.circuit, U16toU8OperationSafe.Assumptions, U16toU8OperationSafe.Spec,
    codeWord, slotWord, Inputs.clock, HostCallChip.channel, stateChannel, publicValuesChannel, CommitmentDeclaration.channel]
  cases deferred <;> simp only [Bool.false_eq_true, ↓reduceIte, circuit_norm] at h_holds ⊢
  all_goals
    obtain ⟨code, index, result, length, clock, value, bytes⟩ := h_holds
    refine ⟨⟨?_, ?_, ?_, ?_, value⟩, clock, bytes⟩
    · simpa only [codeWord, circuit_norm] using code
    · simpa only [slotWord, circuit_norm] using index
    · simpa only [codeWord, circuit_norm] using result
    · simpa only [eval_zero] using length

theorem completeness (deferred : Bool) (slot : Fin 8) :
    GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) (main deferred slot)
      (fun input _ _ => ProverAssumptions deferred slot input) (fun _ _ _ => True) := by
  circuit_proof_start [Gadgets.Equality.circuit, ClockOrder.circuit, BoundedWord.circuit,
    U16toU8OperationSafe.circuit, U16toU8OperationSafe.Assumptions, U16toU8OperationSafe.Spec,
    codeWord, slotWord, Inputs.clock, HostCallChip.channel, stateChannel, publicValuesChannel, CommitmentDeclaration.channel]
  cases deferred <;> simp only [Bool.false_eq_true, ↓reduceIte, circuit_norm] at h_assumptions ⊢
  all_goals
    obtain ⟨⟨⟨code, index, result, length, value⟩, clock, bytes⟩, comparison⟩ := h_assumptions
    refine ⟨?_, ?_, ?_, ?_, clock, ⟨value, comparison⟩, bytes⟩
    · simpa only [codeWord, circuit_norm] using code
    · simpa only [slotWord, circuit_norm] using index
    · simpa only [codeWord, circuit_norm] using result
    · simpa only [eval_zero] using length

/-- The semantic transition performed by an active commitment row. -/
def activeCircuit (deferred : Bool) (slot : Fin 8) : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := s!"sp1.native.{if deferred then "commit_deferred" else "commit"}.{slot.val}"
  main := main deferred slot
  elaborated := elaborated deferred slot
  Spec input _ _ := Spec deferred slot input
  ProverAssumptions input _ _ := ProverAssumptions deferred slot input
  soundness := soundness deferred slot
  completeness := completeness deferred slot
  requirementsChannelsLawful := by
    preserve_tactic_target
    cases deferred
    all_goals
      intro input offset
      refine ⟨?_, ?_, ?_⟩
      · simp only [main, circuit_norm, publicValuesChannel, stateChannel, HostCallChip.channel, CommitmentDeclaration.channel,
          ClockOrder.circuit, BoundedWord.circuit, U16toU8OperationSafe.circuit, Gadgets.Equality.circuit]
      · simp only [main, circuit_norm, publicValuesChannel, stateChannel, HostCallChip.channel, CommitmentDeclaration.channel,
          ClockOrder.circuit, BoundedWord.circuit, U16toU8OperationSafe.circuit, Gadgets.Equality.circuit]
        tauto
      · intro env _
        simp only [main, circuit_norm, publicValuesChannel, stateChannel, HostCallChip.channel, CommitmentDeclaration.channel,
          ClockOrder.circuit, BoundedWord.circuit, U16toU8OperationSafe.circuit, Gadgets.Equality.circuit]
  channelsWithRequirements := [CommitmentDeclaration.channel.toRaw, HostCallChip.channel.toRaw, (stateChannel deferred).toRaw, publicValuesChannel.toRaw]

/-- Commitment handlers use only channel interactions, with no legacy lookups. -/
@[circuit_norm] theorem main_lookups (deferred : Bool) (slot : Fin 8)
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main deferred slot input).operations offset).lookups = [] := by
  cases deferred <;>
    simp [main, ClockOrder.circuit, ClockOrder.main, BoundedWord.circuit, BoundedWord.main,
      WordRangeCheck.circuit, WordRangeCheck.main, LtOperationUnsigned.circuit,
      LtOperationUnsigned.main, U16toU8OperationSafe.circuit, U16toU8OperationSafe.main,
      Gadgets.ToBits.rangeCheck, Gadgets.toBits, Gadgets.ToBits.main,
      Gadgets.IsZeroField.circuit, U16CompareOperation.circuit, U16CompareOperation.main, Gadgets.Equality.main, circuit_norm]

/-- All incoming guarantees and emitted requirements support Boolean guarding. -/
instance guardSupported (deferred : Bool) (slot : Fin 8) :
    Guarded.Supported (activeCircuit (p := p) deferred slot) :=
  Guarded.Supported.of_emitted_requirements _
    (fun input offset => main_lookups deferred slot input offset)
    (by
      intro selected member
      have registered : selected = Channels.byteChannel.toRaw ∨
          selected = CommitmentDeclaration.channel.toRaw ∨ selected = HostCallChip.channel.toRaw ∨
          selected = (stateChannel deferred).toRaw ∨ selected = publicValuesChannel.toRaw := by
        cases deferred <;> simpa [GeneralFormalCircuit.channels, activeCircuit, elaborated, circuit_norm,
          or_assoc, or_left_comm, or_comm] using member
      rcases registered with rfl | rfl | rfl | rfl | rfl <;> infer_instance)
    (by
      intro input offset selected required outside interaction member
      have selectedPublic : selected = publicValuesChannel.toRaw := by
        cases deferred <;> simp_all [activeCircuit, elaborated, circuit_norm]
      subst selected
      change interaction ∈ ((main deferred slot input).operations offset).interactionsWith _ at member
      rw [main_public_interactions] at member
      cases deferred <;>
        simp only [publicInteractions, Bool.false_eq_true, if_false, if_true,
          List.mem_cons, List.mem_ofFn, List.not_mem_nil, or_false] at member
      · rcases member with rfl | ⟨index, rfl⟩ <;> rfl
      · rcases member with rfl | rfl <;> rfl)

/-- Inactive padding keeps every physical occurrence and emits only zero multiplicities. -/
def circuit (deferred : Bool) (slot : Fin 8) : GeneralFormalCircuit (ZMod p) RowInput unit :=
  Guarded.circuit (activeCircuit deferred slot) inferInstance

end SP1Clean.HostCommitChip
