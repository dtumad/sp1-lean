module

public import Clean.Circuit.Subcircuit

/-! # Computability of subcircuits with no local cells

Missing upstream capability: a subcircuit with zero local length has no witness values to
transport. Its computability is independent of input agreement, including zero-width witness
operations. This avoids normalizing large assertion inputs solely to establish a vacuous
witness obligation. Intended for `Clean/Circuit/Basic`.
-/

@[expose] public section

variable {F : Type} [FiniteField F]

/-- Compare a vector as a value before expanding symbolic access into a literal vector. -/
@[computable_witnesses ↓] theorem forall_eval_getElem_iff {n : ℕ}
    (env env' : Environment F) (xs : Vector (Expression F) n) :
    (∀ i (hi : i < n), Expression.eval env xs[i] = Expression.eval env' xs[i]) ↔
      Eval.eval env xs = Eval.eval env' xs := by
  rw [Vector.ext_iff]
  simp only [ProvableType.getElem_eval_fields]

private theorem FlatOperation.computable_of_localLength_zero
    (ops : List (FlatOperation F)) (empty : FlatOperation.localLength ops = 0)
    (n : ℕ) (env env' : ProverEnvironment F) :
    FlatOperation.forAll n {
      witness n' _ compute := env.AgreesBelow n' env' → compute.eval env = compute.eval env'
    } ops := by
  induction ops generalizing n with
  | nil => trivial
  | cons op ops ih =>
    cases op with
    | witness m compute =>
      simp only [FlatOperation.localLength, Nat.add_eq_zero_iff] at empty
      obtain ⟨rfl, empty⟩ := empty
      refine ⟨?_, ih empty (n + 0)⟩
      intro _
      apply Vector.ext
      intro i hi
      omega
    | assert e => exact ⟨trivial, ih empty n⟩
    | lookup l => exact ⟨trivial, ih empty n⟩
    | interact i => exact ⟨trivial, ih empty n⟩

/-- No local cells means no witness values, independently of the input and environments. -/
@[computable_witnesses ↓ high] theorem Subcircuit.computableWitnesses_of_localLength_zero
    {m : ℕ} (s : Subcircuit F m) (n : ℕ) (env env' : ProverEnvironment F)
    (empty : s.localLength = 0) : s.ComputableWitnesses n env env' :=
  FlatOperation.computable_of_localLength_zero s.ops.toFlat
    (s.localLength_eq.symm.trans empty) n env env'

/-- Zero local length also discharges the nested operation formulation. -/
theorem Operations.computableWitnesses_of_localLength_zero
    (ops : Operations F) (empty : ops.localLength = 0)
    (n : ℕ) (env env' : ProverEnvironment F) : ops.ComputableWitnesses n env env' := by
  have flat := FlatOperation.computable_of_localLength_zero ops.toFlat
    (FlatOperation.localLength_toFlat.trans empty) n env env'
  rw [Operations.forAll_toFlat_iff] at flat
  exact flat

/-- A zero-cell assertion's bundled computability follows directly from its checked metadata. -/
theorem FormalCircuitBase.computableWitnesses_unit_of_localLength_zero
    {Input : TypeMap} [CircuitType Input]
    {main : Var Input F → Circuit F (Var unit F)}
    (elaborated : ElaboratedCircuit F Input unit main)
    (empty : ∀ input, elaborated.localLength input = 0) :
    FormalCircuitBase.ComputableWitnesses main := by
  intro n input env env'
  refine ⟨?_, ?_⟩
  swap
  · intro _ _
    change (_ : Unit) = _
    exact Subsingleton.elim _ _
  have localEmpty : ((main input).operations n).localLength = 0 :=
    (elaborated.localLength_eq input n).trans (empty input)
  exact Operations.forAll_implies n
    (Operations.forAll_of_forall (fun _ op => by
      cases op <;> simp only [Condition.apply, Condition.implies] <;> tauto) n _)
    (Operations.computableWitnesses_of_localLength_zero _ localEmpty n env env')

/-- Use assertion metadata before transporting its input. -/
@[computable_witnesses_law] theorem FormalAssertion.toSubcircuit_computableWitnesses_zero
    {Input : TypeMap} [ProvableType Input] (circuit : FormalAssertion F Input)
    (n m : ℕ) (input : Var Input F) (env env' : ProverEnvironment F)
    (empty : circuit.localLength input = 0) :
    (circuit.toSubcircuit m input).ComputableWitnesses n env env' := by
  apply Subcircuit.computableWitnesses_of_localLength_zero
  exact empty

/-- Use general-circuit metadata before transporting its input. -/
@[computable_witnesses_law] theorem GeneralFormalCircuit.toSubcircuit_computableWitnesses_zero
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output)
    (n m : ℕ) (input : Var Input F) (env env' : ProverEnvironment F)
    (empty : circuit.localLength input = 0) :
    (circuit.toSubcircuit m input).ComputableWitnesses n env env' := by
  apply Subcircuit.computableWitnesses_of_localLength_zero
  exact empty
