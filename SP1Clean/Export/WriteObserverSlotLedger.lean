import SP1Clean.Export.WriteObservationBuild
import SP1Clean.Export.WriteObservationHandoff
import ToClean.Air.TableEvaluation

/-! # Physical channel occurrences at each canonically installed observer slot -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics WriteSourceRegistry
private abbrev F := ZMod SP1Prime

variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}
attribute [local irreducible] base withSources preprocessing

/-- An observer table retains its entire ordered channel ledger after Clean installs the
extended table set and public input. Its physical slot supplies the identity proof. -/
theorem build_slot_ledger (w : EnsembleWitness (base image source target final)) (suffix : List (Table F))
    (registry : suffix.map Table.component = tables source target) (i : Fin 19) (t : Table F)
    (atSuffix : suffix[i.val]? = some t) (ch : RawChannel F) :
    ((slot image source target final i).table (build w suffix registry)).interactionsWith ch = t.interactionsWith ch := by
  let full := build w suffix registry
  let atSlot := slot image source target final i
  have own := congrArg (fun cs : List (Component F) => cs[i.val]?) registry
  simp only [List.getElem?_map,atSuffix,Option.map_some,List.getElem?_eq_getElem (show i.val < (tables source target).length from i.isLt),
    Option.some.injEq] at own
  have same := (atSlot.table_component full).trans own.symm
  apply Table.interactionsWith_eq_of_rows _ t ch _ (congrArg (fun c : Component F => c.operations.interactionsWith ch) same)
  have arrays : full.tables.map Table.table = ((installSources w).tables ++ suffix).map Table.table := by
    dsimp only [full,build,Ensemble.AppendedTables.extend]
    rw [EnsembleWitness.ofTables_tables,withDerivedData_map_table]
  have whereAt : atSlot.index.val = (installSources w).tables.length + i.val := by
    rw [← (installSources w).same_length]; rfl
  have physical := congrArg (fun rs : List (List (Array F)) => rs[atSlot.index.val]?) arrays
  simp only [List.getElem?_map,List.getElem?_eq_getElem (show atSlot.index.val < full.tables.length from
    full.same_length ▸ atSlot.index.isLt),Option.map_some] at physical
  have old : ((installSources w).tables ++ suffix)[atSlot.index.val]? = some t := by
    rw [whereAt,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left,atSuffix]
  rw [old,Option.map_some] at physical
  exact Option.some.inj physical

/-- A channel registered on exactly two observer components has the complete original
ledgers of those two tables in order, including the effects of both public verifiers. -/
theorem build_pair_ledger (w : EnsembleWitness (base image source target final)) (suffix : List (Table F))
    (registry : suffix.map Table.component = tables source target) (ch : RawChannel F) (fresh : ch ∈ channels)
    (privateChannel : ch ≠ WriteProbe.readbackChannel.toRaw)
    (publicSilent : ch.name ∉ [(WriteEffects.cursorChannel (p := SP1Prime)).name,(WriteEffects.closeChannel (p := SP1Prime)).name])
    (i j : Fin 19) (selected : selectedSlots source target ch = [i,j]) (left right : Table F)
    (first : suffix[i.val]? = some left) (second : suffix[j.val]? = some right) :
    (withPublicChecks (build w suffix registry)).interactionsWith ch = left.interactionsWith ch ++ right.interactionsWith ch := by
  rw [withPublicChecks_ledger _ _ (protocol_installed _ _ _ _ ch fresh) publicSilent,
    fresh_slots_ledger _ ch fresh privateChannel,selected]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [build_slot_ledger w suffix registry i left first ch,build_slot_ledger w suffix registry j right second ch]

end SP1Clean.Export.WriteObservationAssembly
