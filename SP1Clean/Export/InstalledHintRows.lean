import SP1Clean.Export.WriteHintRecordOrigins
import SP1Clean.Export.WriteMixedControlTables
import SP1Clean.Export.WriteObserverSlotLedger

/-! # Original immutable queue rows in the constructed observation witness

The supervisor projection erases the observer suffix and the readback interactions. Its host
tables still have exactly the physical cells generated before the shared data was computed.
-/

namespace SP1Clean.Export.WriteObservationAssembly

open Circuit Air.Flat Semantics Soundness Machine TraceGen FormalModel.Shard WriteSourceRegistry

private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot} {finish : HostHintQueue.State F}
attribute [local irreducible] base withSources preprocessing

/-- Erasing the observation tables and receipts recovers every original supervisor array. -/
theorem supervisor_build_rows (w : EnsembleWitness (base image source target finish)) (suffix : List (Table F))
    (reg : suffix.map Table.component = tables source target) (i : Fin (base image source target finish).tables.length) :
    ((supervisor (build w suffix reg)).tables.map Table.table)[i.val]? = (w.tables.map Table.table)[i.val]? := by
  let pre := build w suffix reg
  let layout := appended image source target finish
  let same := sameRows image source target finish
  let j : Fin (withSources image source target finish).tables.length := ⟨i.val,same.length ▸ i.isLt⟩
  have a := same.rows (layout.project pre) i
  have b := pre.projectPrefix_getElem_rows_of_width_eq layout.prefix_length
    (fun k => (congrArg Component.width (layout.prefix_component k)).symm.le)
    (fun k => (congrArg Component.FixedRowsMatch (layout.prefix_component k)).symm) j (congrArg Component.width (layout.prefix_component j)).symm
  have c : pre.tables.map Table.table = ((installSources w).tables ++ suffix).map Table.table := by
    dsimp only [pre,build,Ensemble.AppendedTables.extend]
    rw [EnsembleWitness.ofTables_tables,withDerivedData_map_table]
  have inside : j.val < (installSources w).tables.length := (installSources w).same_length ▸ j.isLt
  have inPre : j.val < pre.tables.length := pre.same_length ▸ (j.isLt.trans_le layout.prefix_length)
  have old := congrArg (fun xs : List (List (Array F)) => xs[j.val]?) c
  simp only [List.getElem?_map,List.getElem?_append_left inside,List.getElem?_eq_getElem inside,List.getElem?_eq_getElem inPre,Option.map_some] at old
  rw [List.getElem?_map,List.getElem?_map,List.getElem?_eq_getElem (by rw [← EnsembleWitness.same_length]; exact i.isLt),
    List.getElem?_eq_getElem (by rw [← w.same_length]; exact i.isLt),Option.map_some,Option.map_some]
  exact congrArg some (a.trans (b.trans ((Option.some.inj old).trans (same.symm.rows w j))))

/-- The projected host table at the given index retains its generated original row array. -/
theorem built_hint_host_rows (w : EnsembleWitness (base image source target finish)) (suffix : List (Table F))
    (reg : suffix.map Table.component = tables source target) (i : Fin 35) :
    (w.tables.map Table.table)[63 + i.val]? = some (hintHostTable (build w suffix reg) i).table := by
  let index : Fin (base image source target finish).tables.length := ⟨(63 : Nat) + i.val,by rw [base_length]; omega⟩
  exact (supervisor_build_rows w suffix reg index).symm.trans (hintHostTable_cells (build w suffix reg) i)

end SP1Clean.Export.WriteObservationAssembly
