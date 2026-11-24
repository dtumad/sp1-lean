module

public import ToClean.Air.GuardedDemandTable
public import ToClean.Air.UnitBalance
public import ToClean.Air.MessageFilter

/-! # Exact signed field sums for unit-demand table padding

Clean's guarded demand rows preserve their physical padding occurrences. Within a per-message
LogUp sum their zero multiplicities leave just the chronologically populated unit rows.
-/

@[expose] public section

namespace Air.Flat.WitnessGeneration

open Circuit

variable {F : Type} [FiniteField F] {I : Type} [Zero I]

/-- Removing disabled padding preserves the signed field sum of any row emission with
zero total contribution at its disabled input. -/
theorem guardedRows_balanceOf (rows : List I) (values : I × F → List (Interaction F))
    (msg : Array F) (inactive : balanceOf (values 0) msg = 0) :
    balanceOf ((guardedRows rows).flatMap values) msg = balanceOf (rows.flatMap (fun r => values (r, 1))) msg := by
  have disabled (n : ℕ) : balanceOf ((List.replicate n 0).flatMap values) msg = 0 := by
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ, List.flatMap_cons, balanceOf_append, inactive, ih, add_zero]
  simp only [guardedRows, List.flatMap_append, balanceOf_append, List.flatMap_map, disabled, add_zero]

variable {M : TypeMap} [ProvableType M]

theorem guarded_push_sum (ch : Channel F M) (rows : List I) (record : I → M F) (msg : Array F) :
    balanceOf ((guardedRows rows).map (fun r => ch.pushedIfValue r.2 (record r.1))) msg =
      balanceOf ((rows.map record).map ch.pushedValue) msg := by
  have cut := guardedRows_balanceOf rows (fun r => [ch.pushedIfValue r.2 (record r.1)]) msg (by
    rw [balanceOf_cons]
    simp [Interaction.signedMult, Channel.pushedIfValue, balanceOf]
    exact ite_self 0)
  simpa only [← List.map_eq_flatMap, List.map_map, Function.comp_def, Channel.pushedValue, Channel.pulledValue, Channel.pushedIfValue, Channel.pulledIfValue] using cut

theorem guarded_pull_sum (ch : Channel F M) (rows : List I) (record : I → M F) (msg : Array F) :
    balanceOf ((guardedRows rows).map (fun r => ch.pulledIfValue r.2 (record r.1))) msg =
      balanceOf ((rows.map record).map ch.pulledValue) msg := by
  have cut := guardedRows_balanceOf rows (fun r => [ch.pulledIfValue r.2 (record r.1)]) msg (by
    rw [balanceOf_cons]
    simp [Interaction.signedMult, Channel.pulledIfValue, balanceOf])
  simpa only [← List.map_eq_flatMap, List.map_map, Function.comp_def, Channel.pushedValue, Channel.pulledValue, Channel.pushedIfValue, Channel.pulledIfValue] using cut

end Air.Flat.WitnessGeneration

/-- Matched typed unit messages have zero raw field sum for every payload. -/
theorem Channel.logUp_unit_of_perm {F : Type} [FiniteField F] {M : TypeMap} [ProvableType M]
    (ch : Channel F M) {puts gets : List (M F)} (paired : puts.Perm gets) :
    LogUpBalanced (puts.map ch.pushedValue ++ gets.map ch.pulledValue) := by
  apply ((ch.balanced_unit_iff puts gets).mpr paired).logUp_of_isBool
  intro i member
  rcases List.mem_append.mp member with put | get
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp put
    exact Or.inr rfl
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp get
    exact Or.inr rfl
