import SP1Clean.Model.BusMessages
import SP1Clean.Circuits.Types.BitwiseChip
import SP1Clean.Circuits.Types.LtChip
import SP1Clean.Proofs.Chips.DivRemChip.Defs
import Clean.Utils.Tactics

/-! Regression proofs for Clean's vector evaluation normal form at SP1 message boundaries.
Opaque input vectors stay whole, constructed vectors evaluate inward, and computed outputs
retain the elementwise statements used by witness readback proofs. -/

namespace SP1CleanTest.VectorEvaluation

open SP1Clean SP1Clean.Channels

variable {F : Type} [FiniteField F] {n m : ℕ}

example (env : Environment F) (xs : fields n (Expression F)) (ys : fields n F)
    (input : Eval.eval env xs = ys) (i : ℕ) (bound : i < n) :
    Expression.eval env xs[i] = ys[i] := by
  simp only [circuit_norm, input]

example (env : Environment F) (xs : ProvableVector fieldPair n (Expression F))
    (ys : ProvableVector fieldPair n F) (input : Eval.eval env xs = ys) (i : ℕ) (bound : i < n) :
    Expression.eval env xs[i].1 = ys[i].1 ∧ Expression.eval env xs[i].2 = ys[i].2 := by
  simp only [circuit_norm, input, and_self]

example (env : Environment F) (message : Var MemoryMsg F) (record : MemoryMsg F)
    (input : ProvableStruct.eval env message = record) (i : ℕ) (bound : i < 4) :
    Expression.eval env message.value[i] = record.value[i] := by
  simp only [circuit_norm, input]

example (env : Environment F) (messages : Vector (Var MemoryMsg F) n)
    (records : Vector (MemoryMsg F) n) (input : Eval.eval env messages = records)
    (i : ℕ) (bound : i < n) :
    ProvableStruct.eval env messages[i] = records[i] := by
  simp only [circuit_norm, input]

example (env : Environment F) (xs : fields n (Expression F)) (ys : fields n F)
    (input : Eval.eval env xs = ys) (constant : F) :
    Eval.eval env (Vector.ofFn fun i : Fin n => xs[i] + Expression.const constant) =
      Vector.ofFn (fun i : Fin n => ys[i] + constant) := by
  simp only [circuit_norm, input]

example (env : Environment F) (xs : fields n (Expression F)) (ys : fields m (Expression F)) :
    Eval.eval env ((xs ++ ys).cast (Nat.add_comm n m)) =
      ((Eval.eval env xs) ++ (Eval.eval env ys)).cast (Nat.add_comm n m) := by
  simp only [circuit_norm]

example (env : Environment F) (xs : fields n (Expression F)) :
    Eval.eval env (xs.take m) = (Eval.eval env xs).take m := by
  simp only [circuit_norm]

example (env : ProverEnvironment F) (xs : fields n (Expression F)) (ys : fields n F)
    (input : Eval.eval env.toEnvironment xs = ys) (i : ℕ) (bound : i < n) :
    Eval.eval env xs[i] = ys[i] := by
  simp only [circuit_norm, input]

example (env : Environment F) (make : ℕ → fields n (Expression F)) (offset : ℕ)
    (values : fields n F)
    (readback : ∀ (i : ℕ) (bound : i < n), Expression.eval env (make offset)[i] = values[i])
    (i : ℕ) (bound : i < n) : Eval.eval env (make offset)[i] = values[i] := by
  simp only [circuit_norm]
  guard_target =ₛ Expression.eval env (make offset)[i] = values[i]
  exact readback i bound

end SP1CleanTest.VectorEvaluation

namespace SP1CleanTest.BundledComputability

open SP1Clean

variable {F : Type} [FiniteField F]

-- Derived selectors must normalize in the same direction as upstream struct projections.
example (env : Environment F) (input : Var BitwiseChip.Inputs F)
    (value : BitwiseChip.Inputs F) (h : ProvableStruct.eval env input = value) :
    Expression.eval env input.is_real = value.is_real := by
  simp only [circuit_norm, h]

example (env : Environment F) (input : Var LtChip.Inputs F)
    (value : LtChip.Inputs F) (h : ProvableStruct.eval env input = value) :
    Expression.eval env input.is_real = value.is_real := by
  simp only [circuit_norm, h]

-- A large output's unchanged state can be read without expanding its complete layout.
example {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]
    (env : Environment (ZMod p)) (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ) :
    (ProvableStruct.eval env (DivRemChip.elaborated.output input offset)).state =
      (ProvableStruct.eval env input).state := by
  rw [DivRemChip.Columns.eval_state, DivRemChip.output_state_eq]
  simp only [circuit_norm]

end SP1CleanTest.BundledComputability
