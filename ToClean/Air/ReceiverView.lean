module

public import ToClean.Air.TransitionView

/-! # Reading active receivers from physical AIR tables

Clean exposes raw interaction lists but has no adapter from heterogeneous unit receiver
components to their complete active typed message inventory. `ReceiverView` records the row-local
ledger equation; `messages_interactions` lifts it over physically aligned tables. The shared
indexed-row reader retains every occurrence, and the sublist theorem transports global message
uniqueness to any registered table. These are pure additions for `Clean/Air/FlatComponent.lean`.
-/

@[expose] public section

namespace Air.Flat

variable {F : Type} [FiniteField F]
variable {Message : TypeMap} [ProvableType Message]

/-- Each active physical row consumes exactly one complete typed message. -/
structure ReceiverView (channel : Channel F Message) where
  component : Component F
  message : Environment F → Message F
  /-- Unguarded receivers consume one message per physical row. -/
  activity : Expression F := .const 1
  /-- Constraints establish Boolean activity before channel authentication. -/
  activity_of_constraints : ∀ env, component.operations.ConstraintsHold env →
      env activity = 0 ∨ env activity = 1 := by
    intros
    exact Or.inr rfl
  interactions : ∀ env, component.operations.interactionValuesWith channel.toRaw env =
    [channel.pulledIfValue (env activity) (message env)]

namespace ReceiverView

variable {channel : Channel F Message}

def tableMessages (view : ReceiverView channel) (table : Table F) : List (Message F) :=
  (table.table.filter fun physical => decide (table.environment physical view.activity = 1)).map
    fun physical => view.message (table.environment physical)

/-- Select active messages without changing the physical interaction inventory. -/
def messages (views : List (ReceiverView channel)) (tables : List (Table F)) : List (Message F) :=
  ((TransitionView.readIndexedRows views tables).filter fun (view, env) =>
    decide (env view.activity = 1)).map fun (view, env) => view.message env

theorem messages_cons (view : ReceiverView channel) (views : List (ReceiverView channel))
    (table : Table F) (tables : List (Table F)) :
    messages (view :: views) (table :: tables) = tableMessages view table ++ messages views tables := by
  simp only [messages, TransitionView.readIndexedRows, List.zip_cons_cons, List.flatMap_cons,
    List.filter_append, List.filter_map, List.map_append, List.map_map, Function.comp_def, tableMessages]

/-- Split the physical receiver inventory at a registration boundary. -/
theorem messages_take_drop (views : List (ReceiverView channel)) (tables : List (Table F)) (n : ℕ) :
    messages views tables = messages (views.take n) (tables.take n) ++
      messages (views.drop n) (tables.drop n) := by
  unfold messages TransitionView.readIndexedRows
  conv_lhs => rw [← List.take_append_drop n (views.zip tables)]
  simp only [List.zip_eq_zipWith, List.take_zipWith, List.drop_zipWith,
    List.flatMap_append, List.filter_append, List.map_append]

theorem aligned_of_map_eq (views : List (ReceiverView channel)) (tables : List (Table F))
    (aligned : views.map (·.component) = tables.map (·.component)) :
    List.Forall₂ (fun view table => view.component = table.component) views tables := by
  have equal : List.Forall₂ (· = ·) (views.map (·.component)) (tables.map (·.component)) := by
    simpa only [List.forall₂_eq_eq_eq] using aligned
  simpa only [List.forall₂_map_left_iff, List.forall₂_map_right_iff] using equal

/-- Retain every physical occurrence, including disabled rows at zero multiplicity. -/
theorem physical_interactions (views : List (ReceiverView channel)) (tables : List (Table F))
    (aligned : List.Forall₂ (fun view table => view.component = table.component) views tables) :
    tables.flatMap (·.interactionsWith channel.toRaw) =
      (TransitionView.readIndexedRows views tables).map fun (view, env) =>
        channel.pulledIfValue (env view.activity) (view.message env) := by
  rw [TransitionView.readIndexedRows_interactions views (·.component) tables channel.toRaw aligned]
  simp only [interactions]
  exact List.flatMap_pure_eq_map _ _

/-- Boolean guards identify the active unit pulls in the complete physical ledger. -/
theorem messages_interactions (views : List (ReceiverView channel)) (tables : List (Table F))
    (aligned : List.Forall₂ (fun view table => view.component = table.component) views tables)
    (constraints : ∀ table ∈ tables, table.Constraints) :
    ((tables.flatMap (·.interactionsWith channel.toRaw)).filter
      fun interaction => decide (interaction.mult ≠ 0)) =
        (messages views tables).map channel.pulledValue := by
  rw [physical_interactions views tables aligned]
  rw [channel.pulledIfValues_filter_nonzero]
  · simp only [messages, List.map_map, Function.comp_def]
  · intro row member
    exact row.1.activity_of_constraints row.2
      (TransitionView.readIndexedRows_constraints views (·.component) tables aligned constraints row member)

/-- An actual unit pull identifies its complete typed message in the receiver inventory. -/
theorem message_mem_of_pull_mem (views : List (ReceiverView channel)) (tables : List (Table F))
    (aligned : List.Forall₂ (fun view table => view.component = table.component) views tables)
    (message : Message F)
    (member : channel.pulledValue message ∈ tables.flatMap (·.interactionsWith channel.toRaw)) :
    message ∈ messages views tables := by
  rw [physical_interactions views tables aligned] at member
  obtain ⟨⟨view, env⟩, present, equal⟩ := List.mem_map.mp member
  have active : env view.activity = 1 := by
    have multiplicity := congrArg Interaction.mult equal
    simpa only [Channel.pulledIfValue, Channel.pulledValue, neg_inj] using multiplicity
  have encoded := Vector.toArray_inj.mp (congrArg Interaction.msg equal)
  have same : view.message env = message := by
    simpa only [ProvableType.fromElements_toElements] using congrArg fromElements encoded
  exact List.mem_map.mpr ⟨(view, env), List.mem_filter.mpr ⟨present, by simpa using active⟩, same⟩

/-- A registered receiver's physical occurrences form a sublist of the complete inventory. -/
theorem tableMessages_sublist (views : List (ReceiverView channel)) (tables : List (Table F))
    (aligned : List.Forall₂ (fun view table => view.component = table.component) views tables)
    (index : ℕ) (bound : index < views.length) :
    (tableMessages views[index] (tables[index]'(by rw [← aligned.length_eq]; exact bound))).Sublist
      (messages views tables) := by
  induction aligned generalizing index with
  | nil => simp at bound
  | @cons view table views tables same aligned ih =>
    cases index with
    | zero =>
      simp only [List.getElem_cons_zero, messages_cons]
      exact List.sublist_append_left _ _
    | succ index =>
      simp only [List.getElem_cons_succ, messages_cons]
      exact (ih index (by simpa using bound)).trans (List.sublist_append_right _ _)

/-- Global message-key uniqueness applies to every physical row of any registered receiver. -/
theorem tableMessages_keys_nodup {Key : Type*} (views : List (ReceiverView channel))
    (tables : List (Table F))
    (aligned : List.Forall₂ (fun view table => view.component = table.component) views tables)
    (key : Message F → Key) (unique : ((messages views tables).map key).Nodup)
    (index : ℕ) (bound : index < views.length) :
    ((tableMessages views[index] (tables[index]'(by rw [← aligned.length_eq]; exact bound))).map key).Nodup :=
  unique.sublist ((tableMessages_sublist views tables aligned index bound).map key)

end ReceiverView
end Air.Flat
