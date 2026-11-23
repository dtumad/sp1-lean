module

public import Clean.Circuit.Basic
public import Clean.Utils.Field
public import Mathlib.Tactic.IntervalCases

/-! # `vec4_eval` — folding a length-4 `#v` of pointwise evaluations to whole-vector evaluation

A four-limb witness hint can evaluate each field of its operand, while the bundled circuit
assumption evaluates the vector as a whole. This lemma identifies the two evaluations for
word operations, instruction chips and their witness proofs. -/

@[expose] public section

namespace SP1Clean

variable {p : ℕ} [Fact p.Prime]

lemma vec4_eval (e : Environment (ZMod p)) (v : Vector (Expression (ZMod p)) 4) :
    (#v[Expression.eval e v[0], Expression.eval e v[1], Expression.eval e v[2],
        Expression.eval e v[3]] : Vector (ZMod p) 4) = Eval.eval e v := by
  ext k hk
  interval_cases k <;> simp [← ProvableType.getElem_eval_fields]

end SP1Clean
