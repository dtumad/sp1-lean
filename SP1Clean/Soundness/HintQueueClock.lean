import SP1Clean.Soundness.HostQueueOrder
import SP1Clean.Math.SP1Field
import ToClean.Circuit.SubcircuitProjection

/-! # Strict queue timestamps before authenticating immutable reads

The clock comparison of HINT_READ and both HINT_LEN variants uses only local range
checks. It can order the persistent queue before the node and word providers are known.
-/

namespace SP1Clean.Soundness.HostQueueOrder
open Circuit Air.Flat
private abbrev F := ZMod SP1Prime

private theorem clock_of_constraints (input : Var ClockOrder.Inputs F) (offset : Nat) (env : Environment F)
    (assertions : ∀ e ∈ ((ClockOrder.main input).operations offset).constraints, env e = 0) :
    ClockOrder.Spec (eval env input) := by
  apply (ClockOrder.circuit.original_full_soundness offset env input trivial ⟨assertions,?_⟩ ?_).1
  · simp [ClockOrder.circuit,ClockOrder.main,Gadgets.IsZeroField.circuit,Gadgets.Equality.circuit,Gadgets.Equality.main,
      Gadgets.ToBits.rangeCheck,Gadgets.toBits,Gadgets.ToBits.main,Operations.lookups,circuit_norm]
  · rw [Operations.guarantees_iff _ _ _ (ClockOrder.circuit.in_channels_or_guarantees_full input offset env)]
    intro ch member
    change ch ∈ [] at member
    contradiction

private theorem read_clock (input : Var HostHintReadChip.Inputs F) (env : Environment F) (offset : Nat)
    (checked : ((HostHintReadChip.main input).operations offset).ConstraintsHold env) :
    ClockOrder.Spec (eval env input.clock) := by
  apply clock_of_constraints input.clock offset env
  intro e member
  apply checked.1 e
  simp only [HostHintReadChip.main, circuit_norm, Gadgets.Equality.circuit, List.mem_append]
  tauto

private theorem length_clock (empty : Bool) (input : Var HostHintLengthChip.Inputs F) (env : Environment F) (offset : Nat)
    (checked : ((HostHintLengthChip.main empty input).operations offset).ConstraintsHold env) :
    ClockOrder.Spec (eval env input.clock) := by
  apply clock_of_constraints input.clock offset env
  intro e member
  apply checked.1 e
  cases empty <;> simp only [HostHintLengthChip.main,circuit_norm,Gadgets.Equality.circuit,List.mem_append] <;> tauto

/-- Old queue handlers strictly advance time and preserve the permanent allocation frontier,
from their own actual assertions alone. -/
theorem checked_edge (index : Index) (env : Environment F) (checked : (view index).component.operations.ConstraintsHold env) :
    time (edge (index,env)).1 < time (edge (index,env)).2 ∧
    (edge (index,env)).2.allocated = (edge (index,env)).1.allocated := by
  cases index with
  | none =>
    let input := varFromOffset HostHintReadChip.Inputs (F := F) 0
    have valid := read_clock input env _ ((Component.constraintsHold_iff _).mp checked)
    have cells := eval_varFromOffset_valueFromOffset (M := HostHintReadChip.Inputs) (F := F) (offset := 0) (env := env)
    have evaluated (x : Var HostHintReadChip.Inputs F) : eval env x.clock = (eval env x).clock := by
      rcases x with ⟨⟨_,_,_,_,_,_⟩,⟨_,_,_,_⟩,_,_,_,_⟩
      simp only [HostHintReadChip.Inputs.clock,circuit_norm]
    rw [evaluated,show eval env input = _ from cells] at valid
    exact ⟨valid.2.2.2.2,rfl⟩
  | some empty =>
    let input := varFromOffset HostHintLengthChip.Inputs (F := F) 0
    have valid := length_clock empty input env _ ((Component.constraintsHold_iff _).mp checked)
    have cells := eval_varFromOffset_valueFromOffset (M := HostHintLengthChip.Inputs) (F := F) (offset := 0) (env := env)
    have evaluated (x : Var HostHintLengthChip.Inputs F) : eval env x.clock = (eval env x).clock := by
      rcases x with ⟨⟨_,_,_,_,_,_⟩,⟨_,_,_,_⟩,_⟩
      simp only [HostHintLengthChip.Inputs.clock,circuit_norm]
    rw [evaluated,show eval env input = _ from cells] at valid
    exact ⟨valid.2.2.2.2,rfl⟩

end SP1Clean.Soundness.HostQueueOrder
