import SP1Clean.FormalModel.Contracts.WriteGroup
import Clean.Utils.Tactics.CircuitProofStart
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ComputableWitnesses

/-! # Compare a complete guest word with its destination block window

The fixed slice supplies the two alignment selectors and a mask for each relative byte. All
eight comparisons share the two destination payloads, including the four-limb carry boundary
between them. Ignored WRITE calls still require their genuine input word.
-/

namespace SP1Clean.WriteEffects
open Circuit

variable {p : Nat} [Fact p.Prime]

private theorem one_hot (atLane : Fin 8) (values : Fin 8 → ZMod p) :
    selectLane (Vector.ofFn fun i : Fin 8 => if i.val = atLane.val then 1 else 0) values = values atLane := by
  fin_cases atLane <;> simp [selectLane]

theorem guestByte_ofNat {first size offset : Nat} (small : first < 8) (word : fields 8 (ZMod p)) (slot : Fin 8) :
    (SlicePlan.ofNat first size offset).guestByte word slot = word[(first + slot.val) % 8] :=
  one_hot ⟨first,small⟩ _

theorem streamByte_ofNat {first size offset : Nat} (small : offset < 8) (left right : fields 8 (ZMod p)) (slot : Fin 8) :
    (SlicePlan.ofNat first size offset).streamByte left right slot =
      (if offset + slot.val < 8 then left[(offset + slot.val)%8] else right[(offset + slot.val)%8]) :=
  one_hot ⟨offset,small⟩ _

/-- One selected output byte equals the corresponding authenticated guest byte. -/
def Group.BytesMatch (r : Group (ZMod p)) : Prop :=
  ∀ slot : Fin 8, r.ignored ≠ 1 → r.plan.used[slot] ≠ 0 →
    r.plan.guestByte r.octets.bytes slot = r.plan.streamByte r.left r.right slot

/-- A checked row with the source table's actual plan yields the ordinary byte comparison. -/
theorem Group.BytesMatch.atLane {r : Group (ZMod p)} (matchBytes : r.BytesMatch) {first size offset : Nat}
    (shape : r.plan = .ofNat first size offset) (f : first < 8) (o : offset < 8)
    (slot : Fin 8) (active : slot.val < size) (output : r.ignored ≠ 1) :
    r.octets.bytes[(first+slot.val)%8] =
      (if offset + slot.val < 8 then r.left[(offset+slot.val)%8] else r.right[(offset+slot.val)%8]) := by
  have valid : r.plan.used[slot] ≠ 0 := by simp [shape,SlicePlan.ofNat,active]
  simpa only [shape, guestByte_ofNat f, streamByte_ofNat o] using matchBytes slot output valid

def groupBytesMain (r : Var Group (ZMod p)) : Circuit (ZMod p) Unit := do
  forEach (Vector.ofFn fun i : Fin 8 => i) fun i => do
    let selected <== (1-r.ignored) * r.plan.used[i]
    assertZero (selected * (r.plan.guestByte r.octets.bytes i - r.plan.streamByte r.left r.right i))

instance groupBytesElaborated : ElaboratedCircuit (ZMod p) Group unit groupBytesMain := by elaborate_circuit

private theorem eval_select (env : Environment (ZMod p)) (m : fields 8 (Expression (ZMod p))) (f : Fin 8 → Expression (ZMod p)) :
    (selectLane m f).eval env = selectLane (eval env m) (fun i => (f i).eval env) := by
  simp only [selectLane,circuit_norm]

private theorem eval_guest (env : Environment (ZMod p)) (plan : Var SlicePlan (ZMod p)) (bytes : fields 8 (Expression (ZMod p))) (slot : Fin 8) :
    (plan.guestByte bytes slot).eval env = selectLane (eval env plan.guestSelect) (fun j => (eval env bytes)[(j.val + slot.val) % 8]) := by
  simp only [SlicePlan.guestByte,eval_select,circuit_norm]

private theorem eval_stream (env : Environment (ZMod p)) (plan : Var SlicePlan (ZMod p)) (left right : fields 8 (Expression (ZMod p))) (slot : Fin 8) :
    (plan.streamByte left right slot).eval env = selectLane (eval env plan.streamSelect)
      (fun j => if j.val + slot.val < 8 then (eval env left)[(j.val + slot.val) % 8] else (eval env right)[(j.val + slot.val) % 8]) := by
  simp only [SlicePlan.streamByte,eval_select]
  congr 1
  funext j
  split <;> simp only [circuit_norm]

def groupBytesCircuit : FormalAssertion (ZMod p) Group where
  main := groupBytesMain
  elaborated := groupBytesElaborated
  computableWitnesses := by computable_witnesses
  Spec r := r.BytesMatch
  soundness := by
    circuit_proof_start [groupBytesMain,eval_guest,eval_stream]
    intro slot output used
    obtain ⟨mask,eq⟩ := h_holds slot
    rw [mask] at eq
    simp only [mul_eq_zero, sub_eq_zero] at eq
    rcases eq with (inactive | unselected) | equal
    · exact (output inactive.symm).elim
    · exact (used unselected).elim
    · exact equal
  completeness := by
    circuit_proof_start [groupBytesMain,eval_guest,eval_stream]
    intro slot
    have mask := h_env slot
    refine ⟨mask,?_⟩
    rw [mask]
    simp only [mul_eq_zero, sub_eq_zero]
    by_cases output : input_ignored = 1
    · exact Or.inl (Or.inl output.symm)
    by_cases used : input_plan_used[slot.val] = 0
    · exact Or.inl (Or.inr used)
    exact Or.inr (h_spec slot output used)

end SP1Clean.WriteEffects
