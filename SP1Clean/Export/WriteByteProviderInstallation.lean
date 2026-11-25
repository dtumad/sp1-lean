import SP1Clean.Export.WriteMixedControlTables
import SP1Clean.Proofs.Completeness.ByteProviderBalance

/-! # Installing the complete Byte demand window in the mixed supervisor

The supervisor retains the six original Byte components and seventeen Range components at
positions 32 through 54. The row construction here uses that exact residual window.
-/

namespace SP1Clean.Export.WriteByteProviderInstallation
open Circuit Air.Flat Semantics Soundness Machine WriteSourceRegistry LookupAccessList
open Soundness.ByteProviderDemand hiding component table tables

private abbrev F := ZMod SP1Prime
variable (image : ProgramImage) (source target : ExecutionSnapshot) (finish : HostHintQueue.State F)

/-- Component identity in the original verifier order, relative to position 32. -/
def provider (pos : Fin 23) : Id := all[pos.val]'(by exact pos.isLt)

/-- Every slot in the residual window retains the original core verifier component. -/
theorem registered (pos : Fin 23) :
    (base image source target finish).tables[32 + pos.val]? = some (ByteProviderDemand.component (p := SP1Prime) (provider pos)) := by
  have h := pos.isLt
  rw [retained_core_at _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  have list : (((LocalCore.tables (p := SP1Prime) image source).drop 32).take 23) =
      all.map (ByteProviderDemand.component (p := SP1Prime)) := by rfl
  rw [← List.getElem?_drop,← List.getElem?_take_of_lt pos.isLt,list,List.getElem?_map,
    List.getElem?_eq_getElem (show pos.val < all.length from pos.isLt)]
  rfl

private abbrev suffix := (base image source target finish).tables.drop 6

private theorem residual {i : Fin (suffix image source target finish).length}
    (a : sourceAt (6 + i.val) = none) (b : WriteMixedHostTables.indexAt (6 + i.val) = none)
    (c : WriteMixedFixedResources.indexAt (6 + i.val) = none) (d : WriteMixedControlTables.indexAt (6 + i.val) = none) :
    32 ≤ 6 + i.val ∧ 6 + i.val < 55 := by
  have found : 6 + i.val ∈ (List.range' 6 (suffix image source target finish).length).filter
      (fun j => (sourceAt j).isNone && (WriteMixedHostTables.indexAt j).isNone &&
        (WriteMixedFixedResources.indexAt j).isNone && (WriteMixedControlTables.indexAt j).isNone) := by
    apply List.mem_filter.mpr
    exact ⟨List.mem_range'_1.mpr (by have := i.isLt; omega),by simp [a,b,c,d]⟩
  rw [WriteMixedControlTables.remaining_positions image source target finish,List.mem_range'_1] at found
  exact found

include image source target finish in
/-- The 23 actual providers are outside all original reader generators. -/
theorem window (i : Fin 23) : let k := 32 + i.val
    sourceAt k = none ∧ WriteMixedHostTables.indexAt k = none ∧ WriteMixedFixedResources.indexAt k = none ∧ WriteMixedControlTables.indexAt k = none := by
  intro k
  have member : k ∈ List.range' 32 23 := List.mem_range'_1.mpr (by dsimp only [k]; omega)
  rw [← WriteMixedControlTables.remaining_positions image source target finish] at member
  simpa only [Bool.and_eq_true,Option.isNone_iff_eq_none,and_assoc] using (List.mem_filter.mp member).2

variable (support : List LookupKey) (count : LookupKey → ℕ) (valid : ∀ k ∈ support, ByteServable k) (data : ProverData F)

/-- The 23 generated native providers fill all remaining original physical positions. -/
def remaining : WriteMixedControlTables.Remaining image source target finish :=
  fun i a b c d => by
    have bounds := residual image source target finish a b c d
    let pos : Fin 23 := ⟨6 + i.val - 32,by omega⟩
    have index : 32 + pos.val = 6 + i.val := by dsimp only [pos]; omega
    have found := registered image source target finish pos
    rw [index,← List.getElem?_drop,List.getElem?_eq_getElem i.isLt] at found
    exact ⟨ByteProviderDemand.table support count valid data (provider pos),(Option.some.inj found).symm⟩

/-- At each provider index, the installed physical table is its corresponding generated
opcode or range bucket. -/
theorem remaining_at (pos : Fin 23) (i : Fin (suffix image source target finish).length)
    (same : 6 + i.val = 32 + pos.val) (a b c d) :
    (remaining image source target finish support count valid data i a b c d).1 =
      ByteProviderDemand.table support count valid data (provider pos) := by
  let own : Fin 23 := ⟨6 + i.val - 32,by omega⟩
  change ByteProviderDemand.table support count valid data (provider own) = _
  exact congrArg (fun j => ByteProviderDemand.table support count valid data (provider j)) (Fin.ext (by dsimp [own]; omega))

/-- All residual table constraints and guarantees are discharged by their original generated rows. -/
theorem remaining_valid : ∀ i a b c d, let t := (remaining image source target finish support count valid data i a b c d).1
    t.Constraints ∧ t.Guarantees := by
  intro i a b c d
  exact ByteProviderDemand.table_valid support count valid data _

/-- Every original remaining slot is generated from the support and counts of the native
tally on the physical reads. -/
def ofReaders (reads : List (Interaction F))
    (serve : ∀ item ∈ reads, item.mult ≠ 0 → ByteServable (messageKey item.msg)) :
    WriteMixedControlTables.Remaining image source target finish :=
  remaining image source target finish (requested reads) (readerCount reads) (requested_servable reads serve) data

end SP1Clean.Export.WriteByteProviderInstallation
