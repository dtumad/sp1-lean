import SP1Clean.Native.Operations.HintQueueSnapshot
import ToClean.Circuit.SubcircuitProjection

/-! # Physical identities of the outgoing queue-word table

Every row gets its scheduled word and indices from the fixed prefix. Its surviving cursor,
node and word interactions retain their original multiplicities, including all padding rows.
-/

namespace SP1Clean.HostHintSnapshot
open Circuit Air.Flat Semantics HostHintQueue

variable {p : ℕ} [Fact p.Prime]

/-- The declared schedule fixes the actual padded height independently of prover hints. -/
theorem physical_height (hints : List Bytes) (t : Table (ZMod p)) (same : t.component = component hints) :
    t.table.length = (inventory (p := p) hints).height := by
  have fixed := t.fixed_rows_match
  rw [same] at fixed
  exact fixed.1.trans (UInt64.toNat_ofNatLT ..)

/-- The shape recovered from the canonical data of every physical row is its public word or padding. -/
theorem physical_shape (hints : List Bytes) (t : Table (ZMod p)) (same : t.component = component hints)
    (i : Fin t.table.length) :
    (valueFromOffset Inputs 0 (t.environment t.table[i.val])).1 =
      (fixedShapes (p := p) hints)[i.val]'((physical_height hints t same) ▸ i.isLt) := by
  have fixed := t.fixed_rows_match
  rw [same] at fixed
  rw [Table.environment, valueFromOffset_fromArray]
  exact fixed_at hints ⟨i.val, (physical_height hints t same) ▸ i.isLt⟩ _ (fixed.2 i.val i.isLt)

/-- The complete row ledger follows its public shape and private pointers. -/
theorem ledger (hints : List Bytes) (r : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main hints r).operations offset).interactions =
      [(channel.pulledIf r.2.2 (r.1.before r.2.1)).toRaw,
       (nodeChannel.pulledIf r.1.first (r.1.node r.2.1)).toRaw,
       (wordChannel.pulledIf r.1.active (r.1.word r.2.1)).toRaw,
       (channel.pushedIf r.1.active (r.1.after r.2.1)).toRaw] := by
  simp [main, Operations.interactions, circuit_norm, FormalAssertion.toSubcircuit_interactions]

/-- Recover the fixed admission check and the physical cursor multiplicity from constraints alone. -/
theorem count_of_constraints (hints : List Bytes) (env : Environment (ZMod p))
    (checked : (component hints).operations.ConstraintsHold env) :
    fits hints = true ∧ (valueFromOffset Inputs 0 env).2.2 = (valueFromOffset Inputs 0 env).1.active := by
  have raw := (Component.constraintsHold_iff env).mp checked
  let r : Var Inputs (ZMod p) := varFromOffset Inputs 0
  change ((main hints r).operations (size Inputs)).ConstraintsHold env at raw
  have cells : eval env r = valueFromOffset Inputs 0 env := eval_varFromOffset_valueFromOffset ..
  rw [← cells]
  simp only [main, circuit_norm] at raw
  have gate := raw _ (Or.inl rfl)
  have count := raw _ (Or.inr (Or.inl rfl))
  rw [eval_sub, sub_eq_zero] at count
  change (if fits hints then (0 : ZMod p) else 1) = 0 at gate
  by_cases pass : fits hints = true
  · exact ⟨pass, by simpa only [circuit_norm] using count⟩
  · simp [pass] at gate

end SP1Clean.HostHintSnapshot
