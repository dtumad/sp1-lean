module

public import ToClean.Air.StaticMembershipTable

/-! # Routing real signed consumers to their verifier-fixed membership rows

Read the positive unit pulls in a physical client ledger, retaining occurrence order and repeated
payloads. Each request goes to the first complete matching fixed entry. Inactive occurrences stay
in the physical ledger and contribute zero to the proved balance.
-/

@[expose] public section

namespace StaticTable
open Circuit Air.Flat

variable {F : Type} [FiniteField F] {Row : TypeMap} [ProvableType Row]

/-- The scheduler selects the first complete matching fixed entry, including its eligibility tag. -/
def readerIndex? (t : StaticTable F Row) (msg : Array F) : Option (Fin t.height) :=
  (List.finRange t.height).find? fun i => (toElements (t.fixedEntry i.val)).toArray == msg

/-- Attribute the actual active reads to physical provider positions, rejecting a missing entry. -/
def readers? (t : StaticTable F Row) : List (Interaction F) → Option (List (Fin t.height))
  | [] => some []
  | r :: rs => if r.mult = 0 then t.readers? rs
    else do let i ← t.readerIndex? r.msg; return i :: (← t.readers? rs)

private theorem reader_eq (t : StaticTable F Row) (x : Entry Row F) (spec : t.Spec x.payload) (on : x.eligible = 1) :
    ∃ i, t.readerIndex? (toElements x).toArray = some i ∧ t.fixedEntry i.val = x := by
  obtain ⟨j, payload, tag⟩ := (t.spec_iff_fixedEntry x.payload).mp spec
  have same : t.fixedEntry j.val = x := by
    cases x
    cases fixed : t.fixedEntry j.val
    rw [fixed] at payload tag
    exact congrArg₂ Entry.mk payload (tag.trans on.symm)
  have someIndex : (t.readerIndex? (toElements x).toArray).isSome := by
    apply List.find?_isSome.mpr
    exact ⟨j, List.mem_finRange _, by simp [same]⟩
  obtain ⟨i, picked⟩ := Option.isSome_iff_exists.mp someIndex
  have equal := List.find?_some (p := fun i : Fin t.height => (toElements (t.fixedEntry i.val)).toArray == (toElements x).toArray) picked
  have decode := congrArg (fromElements (M := Entry Row)) (Vector.toArray_inj.mp (eq_of_beq equal))
  exact ⟨i,picked,by simpa only [ProvableType.fromElements_toElements] using decode⟩

/-- A checked physical client's unit pull is either inactive or names one exact eligible
verifier-fixed entry. The raw guarantee is used only on its active pull. -/
theorem checked_pull (t : StaticTable F Row) (r : Interaction F) (data : ProverData F)
    (same : r.channel = t.channel.toRaw) (pull : r.direction = .pull)
    (required : r.Requirements data) (guaranteed : r.Guarantees data) :
    r.mult = 0 ∨ ∃ x : Entry Row F, r = t.channel.pulledValue x ∧ t.Spec x.payload ∧ x.eligible = 1 := by
  rcases r with ⟨ch,d,m,msg,width⟩
  dsimp only at same pull
  subst ch d
  change IsBool m at required
  rcases required with zero | unit
  · exact Or.inl zero
  · subst m
    let x : Entry Row F := fromElements ⟨msg,width⟩
    have valid : x.eligible = 1 ∧ t.Spec x.payload := guaranteed rfl rfl
    refine Or.inr ⟨x, ?_,valid.2,valid.1⟩
    simp only [x, Channel.pulledValue, ProvableType.toElements_fromElements]

private theorem readers_funded (t : StaticTable F Row) (rs : List (Interaction F))
    (honest : ∀ r ∈ rs, r.mult = 0 ∨ ∃ x : Entry Row F, r = t.channel.pulledValue x ∧ t.Spec x.payload ∧ x.eligible = 1) :
    ∃ ids, t.readers? rs = some ids ∧ (∀ i ∈ ids, (t.fixedEntry i.val).eligible = 1) ∧
      ∀ m, balanceOf rs m = balanceOf (ids.map fun i => t.channel.pulledValue (t.fixedEntry i.val)) m := by
  induction rs with
  | nil => exact ⟨[],rfl,by simp,fun _ => rfl⟩
  | cons r rest ih =>
    obtain ⟨is, built, valid, balances⟩ := ih fun x h => honest x (List.mem_cons_of_mem _ h)
    rcases honest r List.mem_cons_self with zero | ⟨x,rfl,spec,on⟩
    · refine ⟨is,by simp only [readers?,zero,ite_true,built],valid,?_⟩
      intro m
      rw [balanceOf_cons,balances]
      have idle : r.signedMult = 0 := by cases dir : r.direction <;> simp [Interaction.signedMult, dir, zero]
      simp [idle]
    · obtain ⟨i, picked, eqn⟩ := t.reader_eq x spec on
      refine ⟨i :: is, ?_, List.forall_mem_cons.mpr ⟨eqn ▸ on,valid⟩, ?_⟩
      · change (if (1 : F) = 0 then t.readers? rest else _) = _
        simp only [one_ne_zero, ↓reduceIte]
        change (t.readerIndex? (toElements x).toArray).bind _ = _
        rw [picked]
        simp [built]
      · intro m
        simp only [List.map_cons, balanceOf_cons,eqn,balances]

/-- Construct a counted physical membership provider directly from its signed client ledger.
No counts, witness validity, routing, or selected provider rows are supplied by the caller. -/
theorem fromReaders (t : StaticTable F Row) (bounded : t.height < UInt64.size) (rs : List (Interaction F))
    (honest : ∀ r ∈ rs, r.mult = 0 ∨ ∃ x : Entry Row F, r = t.channel.pulledValue x ∧ t.Spec x.payload ∧ x.eligible = 1)
    (data : ProverData F) :
    ∃ ids, t.readers? rs = some ids ∧
      let physical := t.buildMembership bounded (fun i => ((ReaderCounts.counts ids)[i] : F)) data
      physical.Constraints ∧ physical.Guarantees ∧ physical.length = t.height ∧
        LogUpBalanced (physical.interactionsWith t.channel.toRaw ++ rs) := by
  obtain ⟨ids,built,eligible,sums⟩ := readers_funded t rs honest
  obtain ⟨valid,guarantees,height,balance⟩ := t.assignedMembership bounded ids eligible data
  refine ⟨ids,built,valid,guarantees,height,fun msg => ?_⟩
  rw [balanceOf_append,sums,← balanceOf_append]
  exact balance msg

/-- Discharge the reader contract from the real component's local checks and its physical pull
directions. The resulting provider counts are taken from that exact signed table ledger. -/
theorem fromClient (t : StaticTable F Row) (bounded : t.height < UInt64.size) (client : Table F)
    (assumptions : client.Assumptions) (checked : client.Constraints ∧ client.Guarantees)
    (directions : ∀ a ∈ client.component.operations.interactionsWith t.channel.toRaw, a.direction = .pull)
    (data : ProverData F) :
    ∃ ids, t.readers? (client.interactionsWith t.channel.toRaw) = some ids ∧
      let physical := t.buildMembership bounded (fun i => ((ReaderCounts.counts ids)[i] : F)) data
      physical.Constraints ∧ physical.Guarantees ∧ physical.length = t.height ∧
        LogUpBalanced (physical.interactionsWith t.channel.toRaw ++ client.interactionsWith t.channel.toRaw) := by
  apply t.fromReaders bounded _ _ data
  intro r member
  have full : r ∈ client.interactions := (List.mem_filter.mp (client.interactionsWith_eq_filter ▸ member)).1
  apply t.checked_pull r client.data (client.channel_eq_of_mem_interactionsWith member) _
    ((client.requirements_iff_forall.mp (client.weakSoundness assumptions checked.1 checked.2).2) _ full)
    ((client.guarantees_iff_forall.mp checked.2) _ full)
  obtain ⟨row, _, emitted⟩ := List.mem_flatMap.mp member
  obtain ⟨a, used, rfl⟩ := List.mem_map.mp emitted
  exact directions a used

end StaticTable
