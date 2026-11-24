import SP1Clean.Export.WriteMixedSourceAssembly
import SP1Clean.Soundness.HostTableRegistry
import SP1Clean.Soundness.HostObservedLedger

/-! # Original commitment and observation slots of the WRITE supervisor

The host block references the actual commitment components and the ordinary observation registry.
These references are disjoint from all read-back publishers and keep their native positions.
-/

namespace SP1Clean.Export.WriteMixedHostTables

open Circuit Air.Flat Semantics Soundness FormalModel.Shard
open WriteSourceRegistry

private abbrev F := ZMod SP1Prime

/-- Host protocol tables built from the semantic execution before deriving global data. -/
inductive Index
  | bank (deferred : Bool) (lane : HostCommitBank.Index)
  | observation (slot : Fin 4)
  deriving DecidableEq

/-- Enumerate the participants in both bank histories and the ordinary observation protocol. -/
def indices : List Index :=
  [false,true].flatMap (fun d => HostCommitBank.indices.map (.bank d)) ++ (List.finRange 4).map .observation

/-- Physical table index in the original supervisor component list. -/
def position : Index → ℕ
  | .bank d i => 63 + HostTableRegistry.bankPosition d i
  | .observation i => 90 + i.val

/-- The original Clean component at a commitment or observation slot. -/
def component : Index → Component F
  | .bank d i => (HostCommitBank.view d i).component
  | .observation i => (Soundness.OrdinaryObservation.tables (p := SP1Prime))[i.val]'i.isLt

/-- Find the generated bank or observation participant at a supervisor position. -/
def indexAt (i : ℕ) : Option Index := indices.find? (fun id => position id == i)

theorem position_of_indexAt {i : ℕ} {id : Index} (found : indexAt i = some id) : position id = i :=
  eq_of_beq (List.find?_some (p := fun candidate => position candidate == i) found)

theorem indexAt_position (id : Index) : indexAt (position id) = some id := by
  cases id with
  | observation i => fin_cases i <;> decide
  | bank d i => cases i with
    | none => cases d <;> decide
    | some i => cases d <;> fin_cases i <;> decide

theorem outside_memory (id : Index) : sourceAt (position id) = none := by
  cases id with
  | observation i => fin_cases i <;> decide
  | bank d i => cases i with
    | none => cases d <;> decide
    | some i => cases d <;> fin_cases i <;> decide

variable (image : ProgramImage) (source target : ExecutionSnapshot) (finish : HostHintQueue.State F)

attribute [local irreducible] HostObserved.observationSlot HostObserved.ensemble in
/-- Typed component identity in the literal 98-table supervisor. -/
theorem registered_at (id : Index) :
    (base image source target finish).tables[position id]? = some (component id) := by
  cases id with
  | observation i =>
    let slot := HostObserved.observationSlot (p := SP1Prime) (image := image) (source := source) (target := target) (final := finish) i
    have located : (base image source target finish).tables[slot.index.val]? = some (component (.observation i)) :=
      List.getElem?_eq_some_iff.mpr ⟨slot.index.isLt, slot.component_eq⟩
    have whereAt : slot.index.val = 90 + i.val := HostObserved.observationSlot_position (image := image) (source := source) (target := target) (final := finish) i
    exact (congrArg (fun n : ℕ => (base image source target finish).tables[n]?) whereAt.symm).trans located
  | bank d idx =>
    have lim := HostTableRegistry.bankPosition_lt d idx
    simp only [position]
    rw [retained_at _ _ _ _ _ (by omega) (by omega) (by omega), HostFinalMemory.beforeChecks, HostLocalCore.tables,
      List.getElem?_append_right (by rw [List.length_set, ProtectedLocalCore.tables_length]; omega),
      List.length_set, ProtectedLocalCore.tables_length, Nat.add_sub_cancel_left]
    let slot := HostTableRegistry.bankSlot (p := SP1Prime) source.host.io.hints [] d idx
    have found : (HostTableRegistry.auxiliary (p := SP1Prime) source.host.io.hints [])[slot.index.val]? = some (component (.bank d idx)) :=
      List.getElem?_eq_some_iff.mpr ⟨slot.index.isLt, slot.component_eq⟩
    change (HostTableRegistry.auxiliary (p := SP1Prime) source.host.io.hints [])[HostTableRegistry.bankPosition d idx]? = _ at found
    simpa only [HostTableRegistry.auxiliary, List.append_nil] using found

/-- The other original providers occupy exactly 41 of the 98 physical slots after the ordered
boundaries, Memory publishers, commitment banks and ordinary observations have been built. -/
theorem remaining_count :
    ((List.range' 6 ((base image source target finish).tables.drop 6).length).filter
      (fun i => (sourceAt i).isNone && (indexAt i).isNone)).length = 41 := by
  rw [List.length_drop, base_length]
  decide

end SP1Clean.Export.WriteMixedHostTables
