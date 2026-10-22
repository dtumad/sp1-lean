module

public import Clean.Circuit.Expression
public import Clean.Utils.Fin

/-! # Sums of circuit expressions

Missing upstream capability: an expression-vector sum with an evaluation normalization rule.
Expressions are syntax, so their sum cannot use the field's additive-monoid instance directly.
Move this helper into Clean's expression API when upstream accepts it.
-/

@[expose] public section

namespace Expression

variable {F : Type} [Field F]

/-- Sum expressions without introducing witness cells. -/
def sum {n : ℕ} (xs : Vector (Expression F) n) : Expression F :=
  Fin.foldl n (fun acc i => acc + xs[i]) 0

/-- Evaluating an expression sum gives the sum of the evaluated vector. -/
@[circuit_norm] theorem eval_sum {n : ℕ} (env : Environment F)
    (xs : Vector (Expression F) n) :
    eval env (sum xs) = ∑ i : Fin n, eval env xs[i] := by
  rw [sum, eval_foldl _ _ _ _ (by intros; simp [circuit_norm])]
  simp only [circuit_norm, Fin.foldl_to_sum]

end Expression
