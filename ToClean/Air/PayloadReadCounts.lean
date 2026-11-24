module

public import Clean.Air.WitnessGeneration.Tally
public import ToClean.Air.ReaderCounts
public import Mathlib.Data.List.Count
public import Mathlib.Data.List.Nodup

/-! # Reader counts of uniquely identified physical payloads

Count typed requests with Clean's existing demand tally. When each physical payload is unique, the resulting
per-payload count funds every read at its genuine row, retaining original unread rows in the signed ledger.
-/

@[expose] public section

namespace Air.Flat.ReaderCounts
open Circuit WitnessGeneration
variable {F : Type} [FiniteField F] {Row : TypeMap} [ProvableType Row]

/-- Build the native demand tally once, then query the natural read count of each physical payload. -/
def byPayload (ch : Channel F Row) (reads : List (Row F)) : Row F → Nat :=
  let tally := reads.foldl (fun (prior : Tally F) r => prior.add ch.name (toElements r).toArray 1) .empty
  fun r => (tally.net (ch.name,(toElements r).toArray)).toNat

theorem byPayload_eq_count [DecidableEq (Row F)] (ch : Channel F Row) (reads : List (Row F)) (r : Row F) :
    byPayload ch reads r = reads.count r := by
  let key := fun x : Row F => (ch.name,(toElements x).toArray)
  let put := fun (t : Tally F) (x : Row F) => t.add ch.name (toElements x).toArray 1
  have injective : Function.Injective key := fun _ _ h =>
    ProvableType.toElements_inj_iff.mp (Vector.toArray_inj.mp (congrArg Prod.snd h))
  have accumulate (xs : List (Row F)) (t : Tally F) :
      (xs.foldl put t).net (key r) = t.net (key r) + (xs.count r : Int) := by
    induction xs generalizing t with
    | nil => simp
    | cons x xs ih =>
      rw [List.foldl_cons,ih]
      unfold put
      rw [Tally.net_add]
      change _ + (if key r = key x then 1 else 0) + _ = _
      by_cases same : x = r <;> simp [same,injective.eq_iff,Ne.symm,add_assoc,add_comm]
  have initial : (Tally.empty (F := F)).net (key r) = 0 := by simp [Tally.net,Tally.empty]
  change ((reads.foldl put .empty).net (key r)).toNat = _
  simp only [accumulate,initial,Int.zero_add,Int.toNat_natCast]

/-- Per-payload reader counts close the full raw push/pull ledger when source identities are unique and exhaustive. -/
theorem unique_balanced [DecidableEq (Row F)] (ch : Channel F Row) (sources reads : List (Row F))
    (unique : sources.Nodup) (covered : ∀ r ∈ reads, r ∈ sources) :
    LogUpBalanced (sources.map (fun r => ch.emittedValue (byPayload ch reads r : F) r) ++ reads.map ch.pulledValue) := by
  obtain ⟨slots,order,_⟩ := assign (eligible := fun _ : Fin sources.length => True) (payload := sources.get)
    (requests := reads) (fun r m => by obtain ⟨i,atRow⟩ := List.mem_iff_get.mp (covered r m); exact ⟨i,trivial,atRow⟩)
  have exactCount i : byPayload ch reads (sources.get i) = (counts slots)[i] := by
    rw [byPayload_eq_count,counts_at,← order,List.count_map_of_injective slots _ unique.injective_get]
  have funds := balanced ch sources.get slots
  have pulls := congrArg (List.map ch.pulledValue) order
  simp only [List.map_map, Function.comp_def] at pulls
  rw [pulls] at funds
  have pubs : sources.map (fun r => ch.emittedValue (byPayload ch reads r : F) r) =
      List.ofFn (fun i : Fin sources.length => ch.emittedValue ((counts slots)[i] : F) (sources.get i)) := by
    conv_lhs => arg 2; rw [← List.ofFn_get sources]
    simp only [List.map_ofFn,Function.comp_def,exactCount]
  rw [pubs]
  exact funds

end Air.Flat.ReaderCounts
