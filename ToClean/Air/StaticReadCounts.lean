module

public import ToClean.Air.StaticPayloadTable
public import ToClean.Air.ReaderCounts

/-! # Counting complete request lists on Clean's verifier-fixed payload tables

Clean's preallocated provider exposes eligible payloads, and its scheduler increments a physical row per
request. This composition fills every fixed row with its actual occurrence count, retaining padding and
zero-read rows, and proves signed balance against the original list of full requests.
-/

@[expose] public section

namespace StaticTable

open Circuit Air.Flat
variable {F : Type} [FiniteField F] {Row : TypeMap} [ProvableType Row]

/-- A full physical fixed table for an ordered list of repeated reads. Its positive counts use eligible
rows only, and its complete ledger has exactly the original verifier-fixed height. -/
theorem counted_payload (t : StaticTable F Row) (target : Channel F Row)
    (valid : ∀ r, t.Spec r → ∀ data, target.Guarantees r data) (bounded : t.height < UInt64.size)
    (requests : List (Row F)) (covered : ∀ r ∈ requests, t.Spec r) (data : ProverData F) :
    ∃ slots : List (Fin t.height),
      slots.map (fun i => (t.fixedEntry i.val).payload) = requests ∧
      (∀ i ∈ slots, (t.fixedEntry i.val).eligible = 1) ∧
      let table := t.buildPayload target valid bounded (fun i => ((ReaderCounts.counts slots)[i] : F)) data
      table.Constraints ∧ table.Guarantees ∧
      (table.interactionsWith target.toRaw).length = t.height ∧
      LogUpBalanced (table.interactionsWith target.toRaw ++ requests.map target.pulledValue) := by
  obtain ⟨slots,order,eligible⟩ := ReaderCounts.assign (eligible := fun i : Fin t.height => (t.fixedEntry i.val).eligible = 1)
    (payload := fun i => (t.fixedEntry i.val).payload) (requests := requests) (fun r mem => by
      obtain ⟨i,payload,live⟩ := (t.spec_iff_fixedEntry r).mp (covered r mem)
      exact ⟨i,live,payload⟩)
  let counts := fun i : Fin t.height => ((ReaderCounts.counts slots)[i] : F)
  have good := t.buildPayload_valid target valid bounded counts data (fun i => by
    by_cases used : i ∈ slots
    · exact Or.inr (eligible i used)
    · exact Or.inl (by simp only [counts,ReaderCounts.counts_at,List.count_eq_zero.mpr used,Nat.cast_zero]))
  have traffic := t.buildPayload_interactions target valid bounded counts data
  refine ⟨slots,order,eligible,good.1,good.2,traffic ▸ List.length_ofFn,?_⟩
  rw [traffic,← order,List.map_map]
  exact ReaderCounts.balanced target (fun i : Fin t.height => (t.fixedEntry i.val).payload) slots

end StaticTable
