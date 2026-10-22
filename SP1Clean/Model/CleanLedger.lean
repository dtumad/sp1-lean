import SP1Clean.Model.InteractionProjection
import ToClean.Air.TableBuild

/-! # Literal Clean access ledgers

Project evaluated Clean interactions into the access vocabulary, preserving every physical
occurrence. Each table stores its evaluation data; assembly supplies data derived from final
committed rows. Changing that data preserves the literal ledger without asserting agreement
of data-dependent semantic predicates.

Rust adapters additionally dualize Memory and Program signs. This module describes the native
ledger and does not prove equivalence to released Rust.
-/

set_option autoImplicit false

namespace SP1Clean

open Circuit
open Air.Flat (Component Table)

variable {p : ℕ} [Fact p.Prime]

/-- Literal Clean interactions followed by the common integer projection. This retains Clean's
Memory and Program signs; `tableNativeAccesses` supplies the Rust-facing orientation instead.
Native provider recounting and channel balance use this literal ledger. -/
def tableCleanAccesses (table : Table (ZMod p)) : LookupAccessList :=
  (table.interactions).map Interaction.toAccess

/-- Literal evaluated interactions in Rust-facing orientation: Memory and Program are
dualized; State, Byte and unexpected channels retain their Clean signs and occurrence order. -/
noncomputable def tableRustOrientedAccesses (table : Table (ZMod p)) : LookupAccessList :=
  (table.interactions).map Interaction.toRustOrientedAccess

/-- Concatenate the literal Clean ledgers of a list of tables, preserving table and row order. -/
def tablesCleanAccesses (tables : List (Table (ZMod p))) : LookupAccessList :=
  tables.flatMap tableCleanAccesses

/-- Literal interaction values read row cells alone; semantic channel predicates are separate. -/
@[simp] theorem tableCleanAccesses_setData (table : Table (ZMod p))
    (data : ProverData (ZMod p)) :
    tableCleanAccesses { table with data } = tableCleanAccesses table := by
  apply congrArg (List.map Interaction.toAccess)
  unfold Table.interactions
  apply List.flatMap_congr
  intro row _
  exact Operations.interactionValues_congr (env := Environment.fromArray row data)
    (env' := Environment.fromArray row table.data) rfl

/-- Changing stored data preserves every occurrence in the physical table ledgers. -/
@[simp] theorem tablesCleanAccesses_setData (tables : List (Table (ZMod p)))
    (data : ProverData (ZMod p)) :
    tablesCleanAccesses (tables.map fun table => { table with data }) =
      tablesCleanAccesses tables := by
  simp only [tablesCleanAccesses, List.flatMap_map, tableCleanAccesses_setData]

@[simp] theorem tablesCleanAccesses_append (left right : List (Table (ZMod p))) :
    tablesCleanAccesses (left ++ right) =
      tablesCleanAccesses left ++ tablesCleanAccesses right := by
  simp only [tablesCleanAccesses, List.flatMap_append]

/-- Evaluating an interaction commutes with the literal Clean projection, without the
Memory/Program dualization used by Rust adapters. -/
theorem interactionToAccess_eval (env : Environment (ZMod p))
    (interaction : AbstractInteraction (ZMod p)) :
    Interaction.toAccess (interaction.eval env) =
      AbstractInteraction.toAccess env interaction := by
  simp only [Interaction.toAccess, AbstractInteraction.toAccess, AbstractInteraction.eval,
    Vector.toList]

@[simp] theorem tablesCleanAccesses_nil : tablesCleanAccesses ([] : List (Table (ZMod p))) = [] :=
  rfl

theorem tablesCleanAccesses_cons (table : Table (ZMod p)) (tables : List (Table (ZMod p)))
    : tablesCleanAccesses (table :: tables) =
      tableCleanAccesses table ++ tablesCleanAccesses tables := by
  simp only [tablesCleanAccesses, List.flatMap_cons]

/-! ## One channel's ledger versus the whole table's

Clean's balance obligations are stated per channel (`EnsembleWitness.interactionsWith channel`),
while a provider recount reads the whole table at once. The two are the same accesses, and at any
given key they are the same *sum* — because `Interaction.toAccess` puts the channel's own `name` in
the key's table slot, so a key already determines which channel could have produced it.

What that argument needs, and all it needs, is that the channel name determines the channel among
the ones the table can actually emit on. That is supplied by the caller: it is an ensemble-level
fact (SP1's four buses have four distinct names), not something a single table knows.
-/

private theorem filter_map_eq {α β : Type*} (l : List α) (f : α → β) (q : β → Bool) :
    (l.map f).filter q = (l.filter fun a => q (f a)).map f := by
  induction l with
  | nil => rfl
  | cons head tail ih => by_cases hq : q (f head) <;> simp [hq, ih]

/-- **A table's ledger restricted to one bus IS that bus's own interaction list.**

The multi-bus counterpart of the providers' route. A provider component names exactly one channel,
so `Ledger.OnlyChannel` lets its whole `interactions` list be read as that channel's — an
instruction chip names up to four, so that lemma is unavailable to it. Filtering by
`InteractionKind` is the replacement, and it works because `Interaction.toAccess` reads the kind off
the emitting channel's own `name`: the kind *is* the channel, as long as no two channels the table
can emit on share one.

That last condition is `honly`, and it is the caller's: for `sp1Ensemble` it comes from
`Soundness/EnsembleChannels.lean` (tables emit only on the ensemble's four channels, whose names —
hence kinds — are distinct). Stating it here rather than assuming it keeps this file free of the
ensemble.

Unlike `multiplicitySum_interactionsWith_eq`, which compares the two at a single key, this is a
**list** equality — which is what a permutation obligation needs. -/
theorem tableCleanAccesses_filterKind (table : Table (ZMod p)) (channel : RawChannel (ZMod p))
    (K : InteractionKind) (hkind : kindOf channel.name = K)
    (honly : ∀ i ∈ table.interactions, kindOf i.channel.name = K → i.channel = channel) :
    (tableCleanAccesses table).filter (fun a => a.1 = K) =
      (table.interactionsWith channel).map Interaction.toAccess := by
  rw [tableCleanAccesses, filter_map_eq, Air.Flat.Table.interactionsWith_eq_filter]
  refine congrArg (List.map Interaction.toAccess) (List.filter_congr fun i hi => ?_)
  by_cases hc : i.channel = channel
  · simp only [hc, hkind, decide_true, Interaction.toAccess]
  · have hne : kindOf i.channel.name ≠ K := fun h => hc (honly i hi h)
    simp only [Interaction.toAccess, hne, hc, decide_false]

/-- **A table's ledger at a key is that key's own channel's ledger.** -/
theorem multiplicitySum_interactionsWith_eq (table : Table (ZMod p))
    (channel : RawChannel (ZMod p)) {k : LookupAccessList.LookupKey}
    (honly : ∀ i ∈ table.interactions,
      LookupAccessList.keyOf (Interaction.toAccess i) = k → i.channel = channel) :
    LookupAccessList.multiplicitySum
        ((table.interactionsWith channel).map Interaction.toAccess) k =
      LookupAccessList.multiplicitySum (tableCleanAccesses table) k := by
  rw [Air.Flat.Table.interactionsWith_eq_filter, tableCleanAccesses]
  exact LookupAccessList.multiplicitySum_filter_map_eq _ _ _ _
    fun i hi hkey => by simpa using honly i hi hkey

omit [Fact p.Prime] in
/-- The key an interaction lands on names its own channel, so a key with a different table name
cannot have come from this interaction. -/
theorem channel_name_of_keyOf_toAccess {i : Interaction (ZMod p)}
    {k : LookupAccessList.LookupKey}
    (h : LookupAccessList.keyOf (Interaction.toAccess i) = k) : i.channel.name = k.2.1 := by
  rw [← h]
  rfl

/-- Closed form for the literal Clean access ledger of an honestly built table. -/
theorem tableCleanAccesses_build (component : Component (ZMod p))
    (inputs : List (component.Input (ZMod p))) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (bounded : inputs.length ≤ UInt64.size)
    (fixed : component.FixedRowsMatch (inputs.map (component.buildRow · data hint)))
    : tableCleanAccesses (Table.build component inputs data hint bounded fixed) =
      inputs.flatMap fun input =>
        component.operations.interactions.map
          (AbstractInteraction.toAccess
            (Environment.fromArray (component.buildRow input data hint) data)) := by
  simp only [tableCleanAccesses, Table.interactions, Table.build, Table.environment, List.flatMap_map,
    Operations.interactionValues, List.map_flatMap, List.map_map, Function.comp_def,
    interactionToAccess_eval]

/-- Row-wise singleton specialization of `tableCleanAccesses_build`.  Provider components emit one
literal Clean access per row. -/
theorem tableCleanAccesses_build_map_singleton
    {Row : Type} (component : Component (ZMod p)) (rows : List Row)
    (decode : Row → component.Input (ZMod p)) (access : Row → LookupAccess)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (bounded : (rows.map decode).length ≤ UInt64.size)
    (fixed : component.FixedRowsMatch ((rows.map decode).map (component.buildRow · data hint)))
    (rowAccess : ∀ row ∈ rows,
      component.operations.interactions.map
          (AbstractInteraction.toAccess
            (Environment.fromArray (component.buildRow (decode row) data hint) data)) =
        [access row]) :
    tableCleanAccesses (Table.build component (rows.map decode) data hint bounded fixed) =
      rows.map access := by
  rw [tableCleanAccesses_build]
  clear fixed bounded
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [List.map_cons, List.flatMap_cons]
    rw [rowAccess row (by simp), ih (fun r hr => rowAccess r (by simp [hr]))]
    rfl

/-! ## Reading a built row's input cells back

After a component's `rowOperations` is unfolded its input variables are plain offsets rather than an
occurrence of `rowInput`, so `Component.rowInput_buildRow` cannot rewrite them directly. These two
recover the typed input at a cell. Stated over Clean's `Component`/`ProvableType` and nothing else. -/

/-- A built row keeps its typed input as a literal prefix.  This cell-level form is useful when
normalizing interactions: after a component's `rowOperations` is unfolded, its input variables are
plain offsets rather than an occurrence of `rowInput`, so `Component.rowInput_buildRow` cannot
rewrite them directly. -/
theorem buildRow_input_get (component : Component (ZMod p))
    (input : component.Input (ZMod p)) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (i : ℕ) (hi : i < size component.Input) :
    (Environment.fromArray (component.buildRow input data hint) data).get i =
      (toElements input)[i] := by
  have decoded := component.rowInput_buildRow input data data hint
  have atCell := congrArg
    (fun value : component.Input (ZMod p) => (toElements value)[i]) decoded
  simpa only [Component.rowInput, valueFromOffset, ProvableType.toElements_fromElements,
    Vector.getElem_mapRange, Nat.zero_add] using atCell

/-- Expression-level form of `buildRow_input_get`, matching the variables that remain after a
component's interaction list has been normalized without unfolding `Expression.eval`. -/
theorem eval_var_buildRow_input_get (component : Component (ZMod p))
    (input : component.Input (ZMod p)) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (i : ℕ) (hi : i < size component.Input) :
    Expression.eval
        (Environment.fromArray (component.buildRow input data hint) data)
        (var ⟨i⟩) = (toElements input)[i] := by
  simpa only [Expression.eval] using buildRow_input_get component input data hint i hi

end SP1Clean
