module

public import ToClean.Air.MessageFilter
public import ToClean.Circuit.EmittedInteraction
public import Mathlib.Algebra.BigOperators.Fin

/-! # Counting assigned reads on physical provider rows

Clean's witness scheduler increments the selected provider row for each request. This
addition gives an executable count at every physical row and proves the resulting signed
balance of each encoded message. Rows with equal payloads may receive different numbers
of requests, and rows that serve no requests remain in the ledger at multiplicity zero.
-/

@[expose] public section

namespace Air.Flat.ReaderCounts

/-- Count uses of each physical index in a single pass through the assigned requests. -/
def counts {n : Nat} (requests : List (Fin n)) : Vector Nat n :=
  requests.foldl (fun totals i => totals.set i.val (totals[i] + 1)) (Vector.replicate n 0)

/-- At each physical position, the accumulated count is its exact natural multiplicity. -/
theorem counts_at {n : Nat} (requests : List (Fin n)) (i : Fin n) :
    (counts requests)[i] = requests.count i := by
  have accumulate (xs : List (Fin n)) (start : Vector Nat n) :
      (xs.foldl (fun (v : Vector Nat n) j => v.set j.val (v[j] + 1)) start)[i] =
        start[i] + xs.count i := by
    induction xs generalizing start with
    | nil => simp
    | cons r rest ih =>
      rw [List.foldl_cons, ih]
      by_cases same : r = i
      · simp [same]; omega
      · have different : r.val ≠ i.val := fun eq => same (Fin.ext eq)
        simp [same, Vector.getElem_set_ne _ _ different]
  have zero : (Vector.replicate n (0 : Nat))[i] = 0 := Vector.getElem_replicate i.isLt
  simpa only [counts, zero, Nat.zero_add] using
    accumulate requests (Vector.replicate n 0)

variable {F : Type} [FiniteField F] {Row : TypeMap} [ProvableType Row]

private theorem balance_map {α : Type} (xs : List α) (f : α → Interaction F) (msg : Array F) :
    balanceOf (xs.map f) msg = (xs.map fun x => if (f x).msg = msg then (f x).signedMult else 0).sum := by
  induction xs with
  | nil => simp [balanceOf]
  | cons a xs ih => simp [balanceOf_cons, ih]

private theorem sum_counts {n : Nat} (requests : List (Fin n)) (hit : Fin n → Bool) :
    (∑ i, if hit i then (requests.count i : F) else 0) = (requests.countP hit : F) := by
  induction requests with
  | nil => simp
  | cons r rest ih =>
    calc
      _ = (∑ i, if hit i then (rest.count i : F) else 0) +
          ∑ i, if i = r then (if hit r then (1 : F) else 0) else 0 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        by_cases same : i = r
        · subst i
          cases hit r <;> simp
        · cases hit i <;> simp [same, Ne.symm same]
      _ = _ := by rw [ih]; cases accepted : hit r <;> simp [accepted]

/-- Grouping unit requests by physical index preserves the signed total of each message,
including when different physical indices carry equal payloads. -/
theorem balance_emitted {n : Nat} (target : Channel F Row) (payload : Fin n → Row F)
    (requests : List (Fin n)) (msg : Array F) :
    balanceOf (List.ofFn fun i : Fin n => target.emittedValue ((counts requests)[i] : F) (payload i)) msg =
      (requests.countP (fun i => (toElements (payload i)).toArray = msg) : F) := by
  let emit := fun i : Fin n => target.emittedValue ((counts requests)[i] : F) (payload i)
  have physical : (List.finRange n).map emit = List.ofFn emit := by simp [List.finRange, Function.comp_def]
  change balanceOf (List.ofFn emit) msg = _
  rw [← physical, balance_map]
  simp only [List.finRange, List.map_ofFn, List.sum_ofFn, Function.comp_apply, emit,
    Channel.emittedValue, Interaction.signedMult, counts_at]
  simpa only [decide_eq_true_eq] using sum_counts (F := F) requests (fun i => (toElements (payload i)).toArray = msg)

/-- Unit pulls restore the chronological requests regardless of provider order. -/
theorem balance_pulled {α : Type} (target : Channel F Row) (payload : α → Row F)
    (requests : List α) (msg : Array F) :
    balanceOf (requests.map fun i => target.pulledValue (payload i)) msg =
      -(requests.countP (fun i => (toElements (payload i)).toArray = msg) : F) := by
  induction requests with
  | nil => simp [balanceOf]
  | cons i rest ih =>
    rw [List.map_cons, balanceOf_cons, ih, List.countP_cons]
    change (if (toElements (payload i)).toArray = msg then -(1 : F) else 0) + _ = _
    by_cases hit : (toElements (payload i)).toArray = msg <;> simp [hit, add_comm]

/-- The allocated provider and all assigned unit pulls balance on their shared channel. -/
theorem balanced {n : Nat} (target : Channel F Row) (payload : Fin n → Row F) (requests : List (Fin n)) :
    LogUpBalanced ((List.ofFn fun i : Fin n => target.emittedValue ((counts requests)[i] : F) (payload i)) ++
      requests.map fun i => target.pulledValue (payload i)) := by
  intro msg
  rw [balanceOf_append, balance_emitted, balance_pulled, add_neg_cancel]

end Air.Flat.ReaderCounts
