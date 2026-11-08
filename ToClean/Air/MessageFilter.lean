module

public import ToClean.Air.TransitionView

/-! # Selecting complete message classes and physical rows

Clean exposes channel balance and physical tables, but has no transport from global balance to
a subset selected solely by message contents. This addition provides a typed payload selector
and selects semantic row environments at their original stored data. Count bounds remain checked
on the complete physical witness before selection. A selection does not construct a new table or
claim agreement with data derived from its selected rows. The intended upstream homes are
`Clean/Air/Balance.lean` and `Clean/Air/FlatComponent.lean`.
-/

@[expose] public section

variable {F : Type}

section Balance
variable [FiniteField F]

/-- Reordering occurrences preserves every signed field sum. -/
theorem balanceOf_perm {left right : List (Interaction F)} (perm : left.Perm right)
    {message : Array F} : balanceOf left message = balanceOf right message := by
  unfold balanceOf
  exact ((perm.filter fun interaction => decide (interaction.msg = message)).map Interaction.signedMult).sum_eq

/-- Concatenated ledgers add their signed field sums, retaining repeated occurrences. -/
theorem balanceOf_append (left right : List (Interaction F)) (message : Array F) :
    balanceOf (left ++ right) message = balanceOf left message + balanceOf right message := by
  simp only [balanceOf, List.filter_append, List.map_append, List.sum_append]

/-- Selecting by payload retains either every occurrence of a message or none of them. -/
theorem balanceOf_filter_messages (interactions : List (Interaction F)) (keep : Array F → Bool)
    (message : Array F) :
    balanceOf (interactions.filter fun interaction => keep interaction.msg) message =
      if keep message then balanceOf interactions message else 0 := by
  induction interactions with
  | nil => simp [balanceOf]
  | cons head rest ih =>
    by_cases same : head.msg = message
    · simp only [List.filter_cons, balanceOf_cons, same]
      cases selected : keep message <;> simp [selected, balanceOf_cons, same, ih]
    · cases selected : keep head.msg <;> cases wanted : keep message <;>
        simp [selected, wanted, balanceOf_cons, same, ih]

/-- Global abstract balance restricts to complete payload classes. Physical count bounds
remain obligations of the original witness and its chosen balance check. -/
theorem BalancedInteractions.filter_messages {interactions : List (Interaction F)}
    (balanced : BalancedInteractions interactions) (keep : Array F → Bool) :
    BalancedInteractions (interactions.filter fun interaction => keep interaction.msg) := by
  have counts (direction : Channel.Direction) (message : Array F) :
      activeCount (interactions.filter fun interaction => keep interaction.msg) direction message =
        if keep message then activeCount interactions direction message else 0 := by
    simp only [activeCount, List.countP_filter]
    have predicate : (fun i : Interaction F =>
        decide (i.direction = direction ∧ i.msg = message ∧ i.mult ≠ 0) && keep i.msg) =
        (fun i => if keep message then decide (i.direction = direction ∧ i.msg = message ∧ i.mult ≠ 0)
          else false) := by
      funext i
      by_cases same : i.msg = message <;> simp [same, Bool.and_comm]
    rw [predicate]
    cases keep message <;> simp
  constructor
  · intro a member pull
    obtain ⟨b, present, same, push⟩ :=
      balanced.exists_push_of_pull a (List.mem_filter.mp member).1 pull
    refine ⟨b, List.mem_filter.mpr ⟨present, ?_⟩, same, push⟩
    simpa only [same] using (List.mem_filter.mp member).2
  · intro message binary
    rw [counts, counts]
    split
    · next selected =>
      apply balanced.activeCount_push_eq_activeCount_pull_of_isBool
      intro i member same
      exact binary i (List.mem_filter.mpr ⟨member, by simpa only [same] using selected⟩) same
    · rfl

/-- Message selection also preserves the concrete signed field-sum relation. -/
theorem LogUpBalanced.filter_messages {interactions : List (Interaction F)}
    (balanced : LogUpBalanced interactions) (keep : Array F → Bool) :
    LogUpBalanced (interactions.filter fun interaction => keep interaction.msg) := by
  intro message
  rw [balanceOf_filter_messages, balanced]
  simp

end Balance

namespace ProvableType

variable {Message : TypeMap} [ProvableType Message]

/-- Decode only correctly sized payloads when selecting a typed message class. -/
def selectMessage (keep : Message F → Bool) (message : Array F) : Bool :=
  if bound : message.size = size Message then keep (fromElements ⟨message, bound⟩) else false

theorem selectMessage_toElements (keep : Message F → Bool) (message : Message F) :
    selectMessage keep (toElements message).toArray = keep message := by
  simp only [selectMessage, Vector.size_toArray, ↓reduceDIte]
  exact congrArg keep (fromElements_toElements message)

end ProvableType

namespace Air.Flat

variable [FiniteField F]

/-- Select semantic environments while retaining each source table's actual prover data.
This is a view of the original physical rows, not a newly committed table. -/
def Table.selectedRows (table : Table F) (keep : Environment F → Bool) : List (Environment F) :=
  (table.table.map table.environment).filter keep

theorem Table.selectedRows_spec (table : Table F) (keep : Environment F → Bool)
    (valid : table.Spec) : ∀ env ∈ table.selectedRows keep, table.component.Spec env := by
  intro env member
  obtain ⟨row, present, rfl⟩ := List.mem_map.mp (List.mem_filter.mp member).1
  exact valid row present

omit [FiniteField F] in
/-- Selecting whole rows commutes with selecting complete message classes when each
row's interactions agree on the selection. Repeated and zero-multiplicity occurrences remain. -/
theorem selectedRows_interactions {Row : Type*} (rows : List Row)
    (interactions : Row → List (Interaction F)) (keep : Row → Bool) (select : Array F → Bool)
    (homogeneous : ∀ row ∈ rows, ∀ interaction ∈ interactions row,
      select interaction.msg = keep row) :
    ((rows.filter keep).flatMap interactions) =
      (rows.flatMap interactions).filter (fun interaction => select interaction.msg) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have same := homogeneous row (List.mem_cons_self ..)
    have rest := ih (fun other member => homogeneous other (List.mem_cons_of_mem _ member))
    have selected : (interactions row).filter (fun interaction => select interaction.msg) =
        if keep row then interactions row else [] := by
      rw [List.filter_congr (fun interaction present => same interaction present)]
      cases keep row <;> simp
    simp only [List.filter_cons, List.flatMap_cons, List.filter_append]
    rw [selected]
    cases keep row <;> simp [rest]

namespace TransitionView

variable {Index : Type*}

/-- A selected semantic view retains the original component index and data environment. -/
def selectRows (indices : List Index) (tables : List (Table F))
    (keep : Index → Environment F → Bool) : List (Index × Environment F) :=
  (readIndexedRows indices tables).filter fun (index, env) => keep index env

/-- Selection retains physical occurrences in their original order. -/
theorem selectRows_sublist (indices : List Index) (tables : List (Table F))
    (keep : Index → Environment F → Bool) :
    (selectRows indices tables keep).Sublist (readIndexedRows indices tables) :=
  List.filter_sublist

/-- Selecting physical rows retains the source of every interaction, on any channel. -/
theorem selectRows_interactions_sublist (indices : List Index) (tables : List (Table F))
    (component : Index → Component F) (keep : Index → Environment F → Bool)
    (channel : RawChannel F)
    (aligned : List.Forall₂ (fun index table => component index = table.component) indices tables) :
    ((selectRows indices tables keep).flatMap (fun (index, env) =>
      (component index).operations.interactionValuesWith channel env)).Sublist
      (tables.flatMap (·.interactionsWith channel)) := by
  rw [readIndexedRows_interactions indices component tables channel aligned]
  exact (selectRows_sublist indices tables keep).flatMap _

end TransitionView
end Air.Flat
