module

public import ToClean.Air.StaticPayloadTable
public import ToClean.Air.StaticMembershipReaders

/-! # Counting complete request lists on Clean's verifier-fixed payload tables

Clean's preallocated provider exposes eligible payloads, and its scheduler increments a physical row per
request. This composition fills every fixed row with its actual occurrence count, retaining padding and
zero-read rows, and proves signed balance against the original list of full requests.
-/

@[expose] public section

namespace StaticTable

open Circuit Air.Flat
variable {F : Type} [FiniteField F] {Row : TypeMap} [ProvableType Row]

/-- The first matching physical row with an active eligibility tag for this valid payload. -/
def requestSlot (t : StaticTable F Row) (r : Row F) (covered : t.Spec r) : Fin t.height :=
  let entry : Entry Row F := ⟨r, 1⟩
  (t.readerIndex? (toElements entry).toArray).get (by
    obtain ⟨i,found,_⟩ := t.readerIndex?_complete entry covered rfl
    exact Option.isSome_iff_exists.mpr ⟨i,found⟩)

private theorem requestSlot_fixed (t : StaticTable F Row) (r : Row F) (covered : t.Spec r) :
    t.fixedEntry (requestSlot t r covered).val = ⟨r,1⟩ := by
  obtain ⟨i,found,equal⟩ := t.readerIndex?_complete ⟨r,1⟩ covered rfl
  simpa only [requestSlot,found,Option.get_some] using equal

/-- The original eligible preallocated index for each complete request, in order. -/
def requestSlots (t : StaticTable F Row) (requests : List (Row F)) (covered : ∀ r ∈ requests, t.Spec r) :
    List (Fin t.height) :=
  requests.attach.map fun r => requestSlot t r.val (covered r.val r.property)

private theorem requestSlots_valid (t : StaticTable F Row) (requests : List (Row F)) (covered : ∀ r ∈ requests, t.Spec r) :
    (t.requestSlots requests covered).map (fun i => (t.fixedEntry i.val).payload) = requests ∧
      ∀ i ∈ t.requestSlots requests covered, (t.fixedEntry i.val).eligible = 1 := by
  constructor
  · simp only [requestSlots,List.map_map,Function.comp_def,requestSlot_fixed,List.attach_map_subtype_val]
  · intro i used
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp used
    exact congrArg Entry.eligible (requestSlot_fixed t r.val (covered r.val r.property))

/-- Construct a complete fixed table by counting actual requests at their original eligible rows. -/
def countedPayload (t : StaticTable F Row) (target : Channel F Row)
    (valid : ∀ r, t.Spec r → ∀ data, target.Guarantees r data) (bounded : t.height < UInt64.size)
    (requests : List (Row F)) (covered : ∀ r ∈ requests, t.Spec r) (data : ProverData F) : Table F :=
  t.buildPayload target valid bounded (fun i => ((ReaderCounts.counts (t.requestSlots requests covered))[i] : F)) data

/-- The concrete counted table funds the exact ordered requests and retains every provider occurrence. -/
theorem countedPayload_checked (t : StaticTable F Row) (target : Channel F Row)
    (valid : ∀ r, t.Spec r → ∀ data, target.Guarantees r data) (bounded : t.height < UInt64.size)
    (requests : List (Row F)) (covered : ∀ r ∈ requests, t.Spec r) (data : ProverData F) :
    let table := t.countedPayload target valid bounded requests covered data
    table.Constraints ∧ table.Guarantees ∧ (table.interactionsWith target.toRaw).length = t.height ∧
      LogUpBalanced (table.interactionsWith target.toRaw ++ requests.map target.pulledValue) := by
  let slots := t.requestSlots requests covered
  obtain ⟨order,eligible⟩ := requestSlots_valid t requests covered
  let counts := fun i : Fin t.height => ((ReaderCounts.counts slots)[i] : F)
  have good := t.buildPayload_valid target valid bounded counts data (fun i => by
    by_cases used : i ∈ slots
    · exact Or.inr (eligible i used)
    · exact Or.inl (by simp only [counts,ReaderCounts.counts_at,List.count_eq_zero.mpr used,Nat.cast_zero]))
  have traffic := t.buildPayload_interactions target valid bounded counts data
  change (t.buildPayload target valid bounded counts data).Constraints ∧ _
  refine ⟨good.1,good.2,traffic ▸ List.length_ofFn,?_⟩
  change LogUpBalanced ((t.buildPayload target valid bounded counts data).interactionsWith target.toRaw ++ requests.map target.pulledValue)
  rw [traffic,← order,List.map_map]
  exact ReaderCounts.balanced target (fun i : Fin t.height => (t.fixedEntry i.val).payload) slots

/-- View the deterministic physical constructor together with its eligible reader assignments. -/
theorem counted_payload (t : StaticTable F Row) (target : Channel F Row)
    (valid : ∀ r, t.Spec r → ∀ data, target.Guarantees r data) (bounded : t.height < UInt64.size)
    (requests : List (Row F)) (covered : ∀ r ∈ requests, t.Spec r) (data : ProverData F) :
    ∃ slots : List (Fin t.height),
      slots.map (fun i => (t.fixedEntry i.val).payload) = requests ∧
      (∀ i ∈ slots, (t.fixedEntry i.val).eligible = 1) ∧
      let table := t.buildPayload target valid bounded (fun i => ((ReaderCounts.counts slots)[i] : F)) data
      table.Constraints ∧ table.Guarantees ∧
      (table.interactionsWith target.toRaw).length = t.height ∧
      LogUpBalanced (table.interactionsWith target.toRaw ++ requests.map target.pulledValue) :=
  ⟨t.requestSlots requests covered,(t.requestSlots_valid requests covered).1,(t.requestSlots_valid requests covered).2,
    t.countedPayload_checked target valid bounded requests covered data⟩

end StaticTable
