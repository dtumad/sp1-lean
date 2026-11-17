module

public import ToClean.Air.TableBuild

/-! # Lookup-free table inventories

A flat component without lookup operations has constraints that read its physical row cells
only, so they survive any change of canonical prover data (`Component.constraintsHold_setData`).
Clean has no name for an inventory of such components, nor for its closure under the list
operations that assemble an ensemble. This module adds the predicate and those combinators, so
an assembly proves lookup freedom once per building block rather than per physical position.

The intended upstream home is `Clean/Air/FlatComponent.lean`.
-/

@[expose] public section

namespace Air.Flat

variable {F : Type} [FiniteField F]

/-- A component whose row circuit has no lookups at any input and offset has none at its row. -/
theorem Component.lookups_eq_nil_of_main (component : Component F)
    (empty : ∀ input offset, ((component.circuit.main input).operations offset).lookups = []) :
    component.operations.lookups = [] := by
  rw [Component.lookups_eq]
  exact empty _ _

/-- No component of the inventory uses a lookup. -/
def LookupFree (tables : List (Component F)) : Prop :=
  ∀ component ∈ tables, component.operations.lookups = []

namespace LookupFree

variable {tables tables' : List (Component F)} {component : Component F}

@[simp] theorem nil : LookupFree ([] : List (Component F)) := nofun

@[simp] theorem cons_iff :
    LookupFree (component :: tables) ↔ component.operations.lookups = [] ∧ LookupFree tables :=
  List.forall_mem_cons

@[simp] theorem append_iff : LookupFree (tables ++ tables') ↔ LookupFree tables ∧ LookupFree tables' :=
  List.forall_mem_append

theorem cons (head : component.operations.lookups = []) (tail : LookupFree tables) :
    LookupFree (component :: tables) :=
  cons_iff.mpr ⟨head, tail⟩

theorem append (left : LookupFree tables) (right : LookupFree tables') :
    LookupFree (tables ++ tables') :=
  append_iff.mpr ⟨left, right⟩

/-- Replacing one physical component by a lookup-free one preserves lookup freedom. -/
theorem set (free : LookupFree tables) (replacement : component.operations.lookups = []) (index : ℕ) :
    LookupFree (tables.set index component) := fun _ member =>
  (List.mem_or_eq_of_mem_set member).elim (free _) fun same => same ▸ replacement

theorem map {α : Type*} {f : α → Component F} {items : List α}
    (each : ∀ item ∈ items, (f item).operations.lookups = []) : LookupFree (items.map f) := by
  simpa only [LookupFree, List.forall_mem_map] using each

/-- Constraints of an inventory member transport across canonical prover data. -/
theorem constraintsHold_setData (free : LookupFree tables) (member : component ∈ tables)
    {row : Array F} {data data' : ProverData F}
    (checked : component.operations.ConstraintsHold (Environment.fromArray row data)) :
    component.operations.ConstraintsHold (Environment.fromArray row data') :=
  component.constraintsHold_setData (free component member) checked

end LookupFree

end Air.Flat
