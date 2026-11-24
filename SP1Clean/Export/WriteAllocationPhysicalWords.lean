import SP1Clean.Export.WriteAllocationWordSeeds
import SP1Clean.Export.WriteAllocationStoreBinding
import SP1Clean.Soundness.AllocationWordWalk

/-! # The exhaustive physical word cursor ledger of freshly allocated immutable buffers -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Soundness WriteAllocation WriteSourceRegistry
private abbrev F := ZMod SP1Prime
attribute [local instance 2000] FiniteField.instDecidableEq
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}
attribute [local irreducible] base withSources preprocessing

private theorem word_registered : (Words.cursorChannel (p := SP1Prime)).toRaw ∈ channels := List.mem_of_getElem? (i := 18) rfl

/-- The actual word headers and padded word rows supply the complete private word ledger. -/
theorem allocation_word_cursor_ledger (w : EnsembleWitness (preprocessing image source target final)) :
    let ch := (Words.cursorChannel (p := SP1Prime)).toRaw
    w.interactionsWith ch = ((slot image source target final 17).table w).interactionsWith ch ++
      ((slot image source target final 18).table w).interactionsWith ch := by
  let ch := (Words.cursorChannel (p := SP1Prime)).toRaw
  have support : selectedSlots source target ch = [17,18] := rfl
  simpa only [support,List.flatMap_cons,List.flatMap_nil,List.append_nil] using fresh_slots_ledger w ch word_registered
    (fun eq => Bool.noConfusion (congrArg (fun c => c.name == "sp1.native.write_readback") eq))

private def continuation (r : Words.Row F) : List (Words.Cursor F) :=
  if r.payload.more = 1 then [r.next] else []

private theorem word_nonzero (ws : List (Words.Row F × F))
    (sound : ∀ x ∈ ws, IsBool x.2 ∧ (x.2 = 1 → x.1.Valid)) :
    ((ws.flatMap Words.wordCursors).filter (fun i => decide (i.mult ≠ 0))) =
      (enabledInputs ws).flatMap (fun r =>
        [Words.cursorChannel.pulledValue r.prior] ++ (continuation r).map Words.cursorChannel.pushedValue) := by
  induction ws with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨bool,valid⟩ := sound x List.mem_cons_self
    have tail := ih (fun y m => sound y (List.mem_cons_of_mem x m))
    simp only [List.flatMap_cons,List.filter_append,tail]
    rcases bool with inactive | active
    · simp [enabledInputs,Words.wordCursors,Channel.pulledIfValue,Channel.pushedIfValue,inactive]
    · have flag : IsBool x.1.payload.more := ((valid active).2.1 7).2.1
      rcases flag with stop | more <;> simp [enabledInputs,Words.wordCursors,continuation,
        Channel.pulledIfValue,Channel.pushedIfValue,Channel.pulledValue,Channel.pushedValue, *]

private theorem word_matches (seeds : List (Contents F × F)) (words : List (Words.Row F × F))
    (seedBool : ∀ x ∈ seeds, IsBool x.2) (checked : ∀ x ∈ words, IsBool x.2 ∧ (x.2 = 1 → x.1.Valid))
    (funded : BalancedInteractions (seeds.flatMap Words.seedCursors ++ words.flatMap Words.wordCursors)) :
    ((enabledInputs seeds).map Words.start ++ (enabledInputs words).flatMap continuation).Perm
      ((enabledInputs words).map Words.Row.prior) := by
  let ch := Words.cursorChannel (p := SP1Prime)
  let rows := enabledInputs words
  have startEq : seeds.flatMap Words.seedCursors = seeds.map (fun x => ch.pushedIfValue x.2 (Words.start x.1)) := by
    rw [List.map_eq_flatMap]; rfl
  have active := funded.filter_nonzero
  rw [List.filter_append,startEq,ch.pushedIfValues_filter_nonzero seeds Prod.snd (fun x => Words.start x.1) seedBool,
    word_nonzero words checked] at active
  let first := (enabledInputs seeds).map Words.start
  let pushes := rows.flatMap continuation
  let pulls := rows.map Words.Row.prior
  have arranged := (List.flatMap_append_perm rows (fun r => [ch.pulledValue r.prior])
    (fun r => (continuation r).map ch.pushedValue)).symm
  have rest : (rows.flatMap (fun r => [ch.pulledValue r.prior] ++ (continuation r).map ch.pushedValue)).Perm
      (pushes.map ch.pushedValue ++ pulls.map ch.pulledValue) := by
    apply arranged.trans
    rw [List.map_flatMap]
    rw [← List.map_eq_flatMap]
    simpa only [pulls,List.map_map,Function.comp_def] using
      List.perm_append_comm (l₁ := rows.map (fun r => ch.pulledValue r.prior))
        (l₂ := rows.flatMap (fun r => (continuation r).map ch.pushedValue))
  have typed := BalancedInteractions.of_perm active (rest.append_left _)
  apply (ch.balanced_unit_iff _ _).mp
  simpa only [List.map_append,List.append_assoc,first,pushes,pulls,enabledInputs,List.map_map,
    Function.comp_def,rows] using typed

/-- A seed or an active continuation is consumed at its exact full cursor; every enabled
word has its checked row contract, even if its publication has zero external readers. -/
theorem native_word_endpoints (w : EnsembleWitness (assembly image source target final)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    let seeds := allocationSeeds (observed w)
    let rows := allocationWords (observed w)
    (seeds.map Words.start ++ rows.flatMap (fun r => if r.payload.more = 1 then [r.next] else [])).Perm (rows.map Words.Row.prior) ∧
      ∀ r ∈ rows,r.Valid := by
  let seen := observed w
  let ch := (Words.cursorChannel (p := SP1Prime)).toRaw
  let s := slot image source target final 17
  let h := slot image source target final 18
  let seeds := guardedInputs Contents (s.table seen)
  let rows := guardedInputs Words.Row (h.table seen)
  have valid := (observed_constraints w).mp checked
  have paid := observed_balance w fit raw ch (protocol_installed image source target final _ word_registered) (of_decide_eq_true rfl)
  change BalancedInteractions (seen.interactionsWith ch) at paid
  rw [allocation_word_cursor_ledger] at paid
  have sl : (s.table seen).interactionsWith ch = seeds.flatMap Words.seedCursors := by
    simp only [Table.interactionsWith,seeds,guardedInputs,List.flatMap_map,s.table_component seen]
    exact List.flatMap_congr fun row _ => Words.seedInput_cursors _
  have wl : (h.table seen).interactionsWith ch = rows.flatMap Words.wordCursors := by
    simp only [Table.interactionsWith,rows,guardedInputs,List.flatMap_map,h.table_component seen]
    exact List.flatMap_congr fun row _ => Words.wordInput_cursors _
  change BalancedInteractions ((s.table seen).interactionsWith ch ++ (h.table seen).interactionsWith ch) at paid
  rw [sl,wl] at paid
  have seedBool : ∀ x ∈ seeds, IsBool x.2 := by
    intro x m
    obtain ⟨row,mem,rfl⟩ := List.mem_map.mp m
    have v := s.table_constraints seen valid row mem
    rw [s.table_component seen] at v
    have bit := Guarded.activity_of_constraints Words.seedCircuit Words.seedSupported
      (varFromOffset (ProvablePair Contents field) 0) _ _ ((Component.constraintsHold_iff _).mp v)
    rwa [Guarded.eval_activity,eval_varFromOffset_valueFromOffset] at bit
  have rowFacts : ∀ x ∈ rows, IsBool x.2 ∧ (x.2 = 1 → x.1.Valid) := by
    intro x m
    obtain ⟨row,mem,rfl⟩ := List.mem_map.mp m
    have v := h.table_constraints seen valid row mem
    rw [h.table_component seen] at v
    have fact := Words.guarded_word_valid (varFromOffset (ProvablePair Words.Row field) 0) _ _ ((Component.constraintsHold_iff _).mp v)
    rwa [eval_varFromOffset_valueFromOffset] at fact
  refine ⟨word_matches seeds rows seedBool rowFacts paid,?_⟩
  intro r mem
  obtain ⟨x,inRows,rfl⟩ := List.mem_map.mp mem
  obtain ⟨physical,active⟩ := List.mem_filter.mp inRows
  exact (rowFacts _ physical).2 (of_decide_eq_true active)

end SP1Clean.Export.WriteObservationAssembly
