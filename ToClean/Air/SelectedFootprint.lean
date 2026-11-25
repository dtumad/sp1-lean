module

public import ToClean.Air.Footprint
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Perm.Subperm
public import Mathlib.Algebra.Order.BigOperators.Group.List

/-! # Additive lower bounds from distinct physical table slots

Clean's whole-ensemble occurrence count includes padding and zero-multiplicity sites.
A set of distinct physical table positions therefore gives an additive lower bound,
including when two positions contain tables with identical data.
-/

@[expose] public section

namespace Air.Flat.EnsembleWitness
open Circuit
variable {F : Type} [FiniteField F] {PublicIO : TypeMap} [ProvableType PublicIO] {ens : Ensemble F PublicIO}

/-- The selected physical slots spend their sum of row heights times channel widths. -/
theorem selected_table_cost_le (w : EnsembleWitness ens) (ids : List (Fin w.tables.length)) (unique : ids.Nodup) (ch : RawChannel F) :
    (ids.map (fun i => w.tables[i.val].length * w.tables[i.val].component.channelWidth ch)).sum ≤ w.channelOccurrences ch := by
  let cost := fun t : Table F => t.length * t.component.channelWidth ch
  have inside : ids ⊆ List.finRange w.tables.length := fun i _ => List.mem_finRange i
  obtain ⟨ordered,equal,subset⟩ := unique.subperm inside
  let f := fun i : Fin w.tables.length => cost w.tables[i.val]
  have total := (subset.map f).sum_le_sum (fun _ _ => Nat.zero_le _)
  rw [(equal.map f).sum_eq,← List.ofFn_eq_map,List.ofFn_getElem_eq_map] at total
  exact total.trans (Nat.le_add_left _ _)

end Air.Flat.EnsembleWitness
